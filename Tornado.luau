local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local ServerStorage = game:GetService("ServerStorage")

local CombatModule = require(ServerStorage.Modules.Combat)
local CarModule = require(ServerStorage.Modules.Car)
local DamageModule = require(ServerStorage.Modules.Damage)

local ScreenShakeEvent = ReplicatedStorage.Events.Screenshake

-- Core
local BASE_RADIUS = 256
local INNER_CORE_RADIUS = 28
local INTENSITY = 1
local UPDATE_RATE = 1 / 30
local DETECTION_REFRESH_RATE = 0.2

-- Forces
local PULL_STRENGTH = 5600
local PULL_MIN_DISTANCE = 0
local SWIRL_STRENGTH = 10000
local SWIRL_SPEED = 2.8
local LIFT_STRENGTH = 10000
local LIFT_THRESHOLD_MULTIPLIER = 0.75
local TURBULENCE_STRENGTH = 5000
local FORCE_FALLOFF_EXPONENT = 1

local MIN_SWIRL_FORCE = 25
local MIN_SWIRL_TANGENTIAL_SPEED = 14
local MIN_SWIRL_TANGENTIAL_TO_RADIAL_RATIO = 1.35

local ACCEL_SMOOTHING = 14
local TURBULENCE_FREQUENCY = 0.7
local TURBULENCE_WHEN_NOT_SWIRLING_MULTIPLIER = 0.04

-- Damage
local PLAYER_DAMAGE_PER_TICK = 3
local VEHICLE_DAMAGE_PER_TICK = 2
local DAMAGE_START_DISTANCE = 156
local DAMAGE_TICK_INTERVAL = 0.35

-- Throw System
local CAPTURE_DURATION_BEFORE_THROW = 12
local THROW_FORCE = 700
local THROW_UPWARD_BOOST = 80
local POST_THROW_IMMUNITY_DURATION = 2

-- Screenshake
local MAX_SCREENSHAKE_INTENSITY = 18
local SCREENSHAKE_DURATION = 0.6
local SCREENSHAKE_RATE_LIMIT = 0.15

-- Filtering
local IGNORE_ANCHORED = true
local MAX_AFFECTED_ASSEMBLIES = 30
local OCCLUSION_PULL_MULTIPLIER = 0.2

local FILTER_MODE = Enum.RaycastFilterType.Exclude
local FILTER_LIST = {}

local TornadoPart = script.Parent
local CenterAttachment = TornadoPart.Center
local ParticleAttachment = TornadoPart.Particle

local function GetModelFromPart(part: BasePart): Model?
	local ancestor = part.Parent
	for _ = 1, 5 do
		if not ancestor then
			return nil
		end
		if ancestor:IsA("Model") then
			return ancestor
		end
		ancestor = ancestor.Parent
	end
	return nil
end

local function GetCharacterHumanoid(rootPart: BasePart): (Model?, Humanoid?)
	local model = GetModelFromPart(rootPart)
	if not model then
		return nil, nil
	end
	local humanoid = model:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		return nil, nil
	end
	return model, humanoid
end

local function IsAssemblyValid(rootPart: BasePart?): boolean
	if not rootPart then
		return false
	end
	if not rootPart.Parent then
		return false
	end
	if IGNORE_ANCHORED and rootPart.Anchored then
		return false
	end
	return true
end

local function BuildOverlapParams(): OverlapParams
	local overlapParams = OverlapParams.new()
	local filterList = table.clone(FILTER_LIST)
	table.insert(filterList, TornadoPart)
	overlapParams.FilterType = FILTER_MODE
	overlapParams.FilterDescendantsInstances = filterList
	return overlapParams
end

local function BuildOcclusionParams(targetRoot: BasePart): RaycastParams
	local rayParams = RaycastParams.new()
	rayParams.FilterType = Enum.RaycastFilterType.Exclude
	local filterList = { TornadoPart }
	local targetModel = GetModelFromPart(targetRoot)
	if targetModel then
		table.insert(filterList, targetModel)
	else
		table.insert(filterList, targetRoot)
	end
	rayParams.FilterDescendantsInstances = filterList
	return rayParams
end

local function IsGrounded(rootPart: BasePart): boolean
	local rayParams = RaycastParams.new()
	rayParams.FilterType = Enum.RaycastFilterType.Exclude
	rayParams.FilterDescendantsInstances = { TornadoPart, rootPart }
	local castDistance = (rootPart.Size.Y * 0.5) + 2
	local hit = workspace:Raycast(rootPart.Position, vector.create(0, -castDistance, 0), rayParams)
	return hit ~= nil
end

local function GetFalloff(distance: number, radius: number): number
	local normalized = math.clamp(distance / math.max(radius, 0.001), 0, 1)
	return (1 - normalized) ^ FORCE_FALLOFF_EXPONENT
end

local CapturedAssemblies = {} :: { [BasePart]: {
	CaptureStartTime: number,
	SwirlStartTime: number?,
	LastDamageTime: number,
	LastVehicleDamageTime: number,
	CharacterModel: Model?,
	Humanoid: Humanoid?,
	Vehicle: any,
} }

local PostThrowImmunity = {} :: { [BasePart]: number }
local LastScreenShakeTime = {} :: { [Player]: number }

local LastAcceleration = {} :: { [BasePart]: Vector3 }
local TurbulenceSeeds = {} :: { [BasePart]: Vector3 }

local function ResolveAssemblyRoot(part: BasePart): BasePart?
	local rootPart = part.AssemblyRootPart
	if not rootPart then
		rootPart = part
	end
	if not IsAssemblyValid(rootPart) then
		return nil
	end
	return rootPart
end

local function CanBeCaptured(rootPart: BasePart, now: number): boolean
	local immunityExpires = PostThrowImmunity[rootPart]
	if immunityExpires and immunityExpires > now then
		return false
	end
	if immunityExpires and immunityExpires <= now then
		PostThrowImmunity[rootPart] = nil
	end
	return true
end

local function EnsureCaptured(rootPart: BasePart, now: number)
	if CapturedAssemblies[rootPart] then
		return
	end
	local characterModel, humanoid = GetCharacterHumanoid(rootPart)
	local vehicle = CarModule.indexVehicleFromPart(rootPart)
	CapturedAssemblies[rootPart] = {
		CaptureStartTime = now,
		SwirlStartTime = nil,
		LastDamageTime = 0,
		LastVehicleDamageTime = 0,
		CharacterModel = characterModel,
		Humanoid = humanoid,
		Vehicle = vehicle,
	}
end

local function ComputeOcclusionMultiplier(rootPart: BasePart): number
	local rayParams = BuildOcclusionParams(rootPart)
	local origin = ParticleAttachment.WorldPosition

	-- Aim at roughly the middle of the target, not their feet
	local targetLow = rootPart.Position + vector.create(0, math.min(3, rootPart.Size.Y * 0.25), 0)
	local directionLow = targetLow - origin
	if directionLow.Magnitude < 1 then
		return 1
	end

	local hitLow = workspace:Raycast(origin, directionLow, rayParams)

	-- Second ray slightly higher to catch cover cases where low ray slips through gaps
	local targetHigh = rootPart.Position + vector.create(0, math.min(7, rootPart.Size.Y * 0.5), 0)
	local directionHigh = targetHigh - origin
	local hitHigh = workspace:Raycast(origin, directionHigh, rayParams)

	if hitLow or hitHigh then
		return OCCLUSION_PULL_MULTIPLIER
	end

	return 1
end

local function GetTurbulenceVector(rootPart: BasePart, now: number): Vector3
	local seed = TurbulenceSeeds[rootPart]
	if not seed then
		seed = vector.create(math.random() * 1000, math.random() * 1000, math.random() * 1000)
		TurbulenceSeeds[rootPart] = seed
	end

	local t = now * TURBULENCE_FREQUENCY
	local x = math.noise(seed.X, t, 0)
	local y = math.noise(seed.Y, t, 1)
	local z = math.noise(seed.Z, t, 2)

	return vector.create(x, y, z)
end

local function ApplyTornadoForces(rootPart: BasePart, captureData, centerPosition: Vector3, effectiveRadius: number, deltaTime: number): boolean
	local offset = rootPart.Position - centerPosition
	local distance = offset.Magnitude
	if distance > effectiveRadius then
		return false
	end

	local mass = rootPart.AssemblyMass
	if mass <= 0 then
		return false
	end

	local falloff = GetFalloff(distance, effectiveRadius)
	local occlusionMultiplier = ComputeOcclusionMultiplier(rootPart)

	local pullForce = vector.zero
	if distance > PULL_MIN_DISTANCE then
		pullForce = (-offset.Unit) * (PULL_STRENGTH * INTENSITY * falloff * occlusionMultiplier)
	end
	
	local swirlForce = vector.zero
	local tangentUnit: Vector3? = nil
	local radialUnit: Vector3? = nil

	local planarOffset = vector.create(offset.X, 0, offset.Z)
	local planarDistance = planarOffset.Magnitude

	local SwirlAllowed = planarDistance <= math.min(8, effectiveRadius)

	if SwirlAllowed and planarDistance > 0.5 then
		radialUnit = planarOffset.Unit
		local tangent = Vector3.yAxis:Cross(radialUnit)
		if tangent.Magnitude > 0 then
			tangentUnit = tangent.Unit
			swirlForce = tangentUnit * (SWIRL_STRENGTH * SWIRL_SPEED * INTENSITY * falloff * occlusionMultiplier)
		end
	end

	local liftForce = vector.zero
	local desiredLift = LIFT_STRENGTH * INTENSITY * falloff * occlusionMultiplier
	local liftThreshold = mass * workspace.Gravity * LIFT_THRESHOLD_MULTIPLIER
	local grounded = IsGrounded(rootPart)
	if (not grounded) or desiredLift > liftThreshold then
		liftForce = vector.create(0, desiredLift, 0)
	end

	local wasSwirling = captureData and captureData.SwirlStartTime ~= nil
	local turbulenceMultiplier = wasSwirling and 1 or TURBULENCE_WHEN_NOT_SWIRLING_MULTIPLIER
	if grounded then
		turbulenceMultiplier *= 0.5
	end

	local turbulenceVector = GetTurbulenceVector(rootPart, os.clock())
	local turbulenceForce = Vector3.zero
	if turbulenceVector.Magnitude > 0 then
		turbulenceForce = turbulenceVector.Unit * (TURBULENCE_STRENGTH * INTENSITY * falloff * turbulenceMultiplier * occlusionMultiplier)
	end

	local totalForce = pullForce + swirlForce + liftForce + turbulenceForce
	local acceleration = totalForce / mass

	local lastAcceleration = LastAcceleration[rootPart] or vector.zero
	local smoothAlpha = 1 - math.exp(-ACCEL_SMOOTHING * deltaTime)
	local smoothAcceleration = lastAcceleration:Lerp(acceleration, smoothAlpha)
	LastAcceleration[rootPart] = smoothAcceleration

	rootPart.AssemblyLinearVelocity += smoothAcceleration * deltaTime

	if tangentUnit and radialUnit then
		local velocity = rootPart.AssemblyLinearVelocity
		local tangentialSpeed = math.abs(velocity:Dot(tangentUnit))
		local radialSpeed = math.abs(velocity:Dot(radialUnit))

		local hasSwirlForce = swirlForce.Magnitude >= MIN_SWIRL_FORCE
		local hasTangential = tangentialSpeed >= MIN_SWIRL_TANGENTIAL_SPEED
		local tangentialDominates = tangentialSpeed >= (radialSpeed * MIN_SWIRL_TANGENTIAL_TO_RADIAL_RATIO)

		local airborneOk = not grounded

		return airborneOk and hasSwirlForce and hasTangential and tangentialDominates
	end

	return false
end

local function ApplyPlayerDamage(rootPart: BasePart, captureData, distance: number, effectiveRadius: number, now: number)
	if distance > DAMAGE_START_DISTANCE then
		return
	end
	if now - captureData.LastDamageTime < DAMAGE_TICK_INTERVAL then
		return
	end
	captureData.LastDamageTime = now

	local proximityScale = 1 - math.clamp(distance / math.max(DAMAGE_START_DISTANCE, 0.001), 0, 1)
	local damageAmount = PLAYER_DAMAGE_PER_TICK * INTENSITY * proximityScale
	if damageAmount <= 0 then
		return
	end

	-- Player damage dealing logic
	local Attackable = CombatModule.canAttackEnemy(rootPart, TornadoPart)
	local CanAttack, HealthContainer = Attackable[1], Attackable[3]
	if CanAttack and HealthContainer then
		DamageModule.dealDamage(HealthContainer, damageAmount, rootPart, {TornadoPart})
		return
	end
end

local function ApplyVehicleDamage(captureData, distance: number, effectiveRadius: number, now: number)
	if not captureData.Vehicle then
		return
	end
	if distance > DAMAGE_START_DISTANCE then
		return
	end
	if now - captureData.LastVehicleDamageTime < DAMAGE_TICK_INTERVAL then
		return
	end
	captureData.LastVehicleDamageTime = now

	local proximityScale = 1 - math.clamp(distance / math.max(DAMAGE_START_DISTANCE, 0.001), 0, 1)
	local damageAmount = VEHICLE_DAMAGE_PER_TICK * INTENSITY * proximityScale
	if damageAmount <= 0 then
		return
	end

	DamageModule.DealDamageToCar(captureData.Vehicle, damageAmount, TornadoPart)
end

local function FireScreenShake(player: Player, signal: string, intensity: number, duration: number, now: number)
	local lastTime = LastScreenShakeTime[player]
	if lastTime and now - lastTime < SCREENSHAKE_RATE_LIMIT then
		return
	end
	LastScreenShakeTime[player] = now
	ScreenShakeEvent:FireClient(player, signal, intensity, duration)
end

local function HandleScreenShake(centerPosition: Vector3, effectiveRadius: number, now: number)
	for _, player in Players:GetPlayers() do
		local character = player.Character
		if not character then
			continue
		end
		local rootPart = character:FindFirstChild("HumanoidRootPart")
		if not rootPart or not rootPart:IsA("BasePart") then
			continue
		end
		local distance = (rootPart.Position - centerPosition).Magnitude
		if distance > effectiveRadius then
			continue
		end

		local normalized = 1 - math.clamp(distance / math.max(effectiveRadius, 0.001), 0, 1)
		local curve = normalized ^ 0.55
		local rawIntensity = MAX_SCREENSHAKE_INTENSITY * (0.25 + 0.75 * curve)
		local intensity = math.clamp(math.floor(rawIntensity + 0.5), 2, MAX_SCREENSHAKE_INTENSITY)

		local signal = "Rumble"
		if distance <= (INNER_CORE_RADIUS * INTENSITY * 1.75) then
			signal = "Quake"
		end

		FireScreenShake(player, signal, intensity, SCREENSHAKE_DURATION, now)
	end
end

local function ThrowCapturedAssembly(rootPart: BasePart, captureData, centerPosition: Vector3, now: number)
	local offset = rootPart.Position - centerPosition
	if offset.Magnitude < 0.001 then
		offset = vector.create(1, 0, 0)
	end
	local throwDirection = (offset.Unit + vector.create(0, 0.5, 0)).Unit
	local throwVelocity = throwDirection * (THROW_FORCE * INTENSITY)
	throwVelocity += vector.create(0, THROW_UPWARD_BOOST * INTENSITY, 0)
	rootPart.AssemblyLinearVelocity += throwVelocity

	if captureData.CharacterModel then
		local player = Players:GetPlayerFromCharacter(captureData.CharacterModel)
		if player then
			FireScreenShake(player, "Explosion", MAX_SCREENSHAKE_INTENSITY, SCREENSHAKE_DURATION * 1.25, now)
		end
	end

	CapturedAssemblies[rootPart] = nil
	LastAcceleration[rootPart] = nil
	TurbulenceSeeds[rootPart] = nil
	PostThrowImmunity[rootPart] = now + POST_THROW_IMMUNITY_DURATION
end

local DetectionAccumulator = 0

RunService.Heartbeat:Connect(function(deltaTime)
	DetectionAccumulator += deltaTime

	local now = os.clock()
	local effectiveRadius = BASE_RADIUS * INTENSITY
	local centerPosition = CenterAttachment.WorldPosition

	if DetectionAccumulator >= DETECTION_REFRESH_RATE then
		DetectionAccumulator = 0
		local overlapParams = BuildOverlapParams()
		local parts = workspace:GetPartBoundsInRadius(centerPosition, effectiveRadius, overlapParams)
		local addedCount = 0
		for _, part in ipairs(parts) do
			if addedCount >= MAX_AFFECTED_ASSEMBLIES then
				break
			end
			local rootPart = ResolveAssemblyRoot(part)
			if not rootPart then
				continue
			end
			if CapturedAssemblies[rootPart] then
				continue
			end
			if not CanBeCaptured(rootPart, now) then
				continue
			end
			EnsureCaptured(rootPart, now)
			addedCount += 1
		end
	end

	local frameDelta = deltaTime

	local activeCount = 0
	for rootPart, captureData in pairs(CapturedAssemblies) do
		if activeCount >= MAX_AFFECTED_ASSEMBLIES then
			break
		end
		if not IsAssemblyValid(rootPart) then
			CapturedAssemblies[rootPart] = nil
			LastAcceleration[rootPart] = nil
			TurbulenceSeeds[rootPart] = nil
			continue
		end

		local distance = (rootPart.Position - centerPosition).Magnitude
		if distance > effectiveRadius then
			CapturedAssemblies[rootPart] = nil
			LastAcceleration[rootPart] = nil
			TurbulenceSeeds[rootPart] = nil
			continue
		end

		local isGettingSwirled = ApplyTornadoForces(rootPart, captureData, centerPosition, effectiveRadius, frameDelta)
		ApplyPlayerDamage(rootPart, captureData, distance, effectiveRadius, now)
		ApplyVehicleDamage(captureData, distance, effectiveRadius, now)

		if isGettingSwirled then
			if not captureData.SwirlStartTime then
				captureData.SwirlStartTime = now
			end
		else
			captureData.SwirlStartTime = nil
		end

		local captureDuration = 0
		if captureData.SwirlStartTime then
			captureDuration = now - captureData.SwirlStartTime
		end

		local humanoid = captureData.Humanoid
		local canThrowCharacter = (not humanoid) or humanoid.Health > 0
		if canThrowCharacter and captureDuration >= CAPTURE_DURATION_BEFORE_THROW then
			ThrowCapturedAssembly(rootPart, captureData, centerPosition, now)
		else
			activeCount += 1
		end
	end

	for trackedPart, immunityEnd in pairs(PostThrowImmunity) do
		if (not trackedPart.Parent) or immunityEnd <= now then
			PostThrowImmunity[trackedPart] = nil
		end
	end

	for player in pairs(LastScreenShakeTime) do
		if not player.Parent then
			LastScreenShakeTime[player] = nil
		end
	end

	HandleScreenShake(centerPosition, effectiveRadius, now)
end)
