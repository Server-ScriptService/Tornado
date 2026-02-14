local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local ServerStorage = game:GetService("ServerStorage")
local Workspace = game:GetService("Workspace")

local CombatModule = require(ServerStorage.Modules.Combat)
local CarModule = require(ServerStorage.Modules.Car)

local ScreenShakeEvent = ReplicatedStorage.Events.Screenshake

-- Core
local BASE_RADIUS = 256
local INNER_CORE_RADIUS = 28
local INTENSITY = 1
local UPDATE_RATE = 1 / 30
local DETECTION_REFRESH_RATE = 0.2

-- Forces
local PULL_STRENGTH = 1200
local PULL_MIN_DISTANCE = 5
local SWIRL_STRENGTH = 500
local SWIRL_SPEED = 1
local SWIRL_MIN_DISTANCE = 6
local LIFT_STRENGTH = 680
local LIFT_THRESHOLD_MULTIPLIER = 0.75
local TURBULENCE_STRENGTH = 5000
local FORCE_FALLOFF_EXPONENT = 2

-- Damage
local PLAYER_DAMAGE_PER_TICK = 1
local VEHICLE_DAMAGE_PER_TICK = 1
local DAMAGE_TICK_INTERVAL = 0.35

-- Throw System
local CAPTURE_DURATION_BEFORE_THROW = 4
local THROW_FORCE = 100
local THROW_UPWARD_BOOST = 80
local POST_THROW_IMMUNITY_DURATION = 2

-- Screenshake
local MAX_SCREENSHAKE_INTENSITY = 10
local SCREENSHAKE_DURATION = 0.25
local SCREENSHAKE_RATE_LIMIT = 0.3

-- Filtering
local IGNORE_ANCHORED = true
local MAX_AFFECTED_ASSEMBLIES = 30
local OCCLUSION_ENABLED = true
local OCCLUSION_PULL_MULTIPLIER = 0.4

local FILTER_MODE = Enum.RaycastFilterType.Exclude
local FILTER_LIST = {}

local TornadoRoot = script.Parent
local CenterAttachment = TornadoRoot:FindFirstChild("Center", true)
assert(CenterAttachment and CenterAttachment:IsA("Attachment"), "Center attachment is required")

local function GetTornadoPart(): BasePart
	if TornadoRoot:IsA("BasePart") then
		return TornadoRoot
	end
	if TornadoRoot:IsA("Model") then
		if TornadoRoot.PrimaryPart then
			return TornadoRoot.PrimaryPart
		end
		local foundPart = TornadoRoot:FindFirstChildWhichIsA("BasePart", true)
		assert(foundPart, "Tornado model requires a BasePart")
		return foundPart
	end
	error("Tornado script parent must be a BasePart or Model")
end

local TornadoPart = GetTornadoPart()

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
	table.insert(filterList, TornadoRoot)
	overlapParams.FilterType = FILTER_MODE
	overlapParams.FilterDescendantsInstances = filterList
	return overlapParams
end

local function BuildOcclusionParams(targetRoot: BasePart): RaycastParams
	local rayParams = RaycastParams.new()
	rayParams.FilterType = Enum.RaycastFilterType.Exclude
	local filterList = { TornadoRoot }
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
	rayParams.FilterDescendantsInstances = { TornadoRoot, rootPart }
	local castDistance = (rootPart.Size.Y * 0.5) + 2
	local hit = Workspace:Raycast(rootPart.Position, Vector3.new(0, -castDistance, 0), rayParams)
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

local function ComputeOcclusionMultiplier(rootPart: BasePart, centerPosition: Vector3): number
	if not OCCLUSION_ENABLED then
		return 1
	end
	local castDirection = centerPosition - rootPart.Position
	local rayParams = BuildOcclusionParams(rootPart)
	local rayResult = Workspace:Raycast(rootPart.Position, castDirection, rayParams)
	if rayResult then
		return OCCLUSION_PULL_MULTIPLIER
	end
	return 1
end

local function ApplyTornadoForces(rootPart: BasePart, centerPosition: Vector3, effectiveRadius: number, deltaTime: number): boolean
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
	local occlusionMultiplier = ComputeOcclusionMultiplier(rootPart, centerPosition)

	local pullForce = Vector3.zero
	if distance > PULL_MIN_DISTANCE then
		pullForce = (-offset.Unit) * (PULL_STRENGTH * INTENSITY * falloff * occlusionMultiplier)
	end

	local swirlForce = Vector3.zero
	local isGettingSwirled = false
	if distance > SWIRL_MIN_DISTANCE then
		local radial = offset.Unit
		local tangent = Vector3.yAxis:Cross(radial)
		if tangent.Magnitude > 0 then
			swirlForce = tangent.Unit * (SWIRL_STRENGTH * SWIRL_SPEED * INTENSITY * falloff * occlusionMultiplier)
			isGettingSwirled = swirlForce.Magnitude > 0
		end
	end

	local liftForce = Vector3.zero
	local desiredLift = LIFT_STRENGTH * INTENSITY * falloff * occlusionMultiplier
	local liftThreshold = mass * Workspace.Gravity * LIFT_THRESHOLD_MULTIPLIER
	local grounded = IsGrounded(rootPart)
	if (not grounded) or desiredLift > liftThreshold then
		liftForce = Vector3.new(0, desiredLift, 0)
	end

	local turbulenceVector = Vector3.new(math.random() - 0.5, math.random() - 0.5, math.random() - 0.5)
	local turbulenceForce = Vector3.zero
	if turbulenceVector.Magnitude > 0 then
		turbulenceForce = turbulenceVector.Unit * (TURBULENCE_STRENGTH * INTENSITY)
	end

	local totalForce = pullForce + swirlForce + liftForce + turbulenceForce
	local acceleration = totalForce / mass
	rootPart.AssemblyLinearVelocity += acceleration * deltaTime

	return isGettingSwirled
end

local function ApplyPlayerDamage(rootPart: BasePart, captureData, distance: number, effectiveRadius: number, now: number)
	if now - captureData.LastDamageTime < DAMAGE_TICK_INTERVAL then
		return
	end
	captureData.LastDamageTime = now
	local canAttackResponse = CombatModule.canAttackEnemy(rootPart, TornadoPart)
	if not canAttackResponse or not canAttackResponse.CanAttack then
		return
	end
	local proximityScale = 1 - math.clamp(distance / math.max(effectiveRadius, 0.001), 0, 1)
	local damageAmount = PLAYER_DAMAGE_PER_TICK * INTENSITY * (0.5 + proximityScale)
	CombatModule.dealDamage(canAttackResponse.HealthContainer, damageAmount, rootPart, {
		Tornado = TornadoPart,
	})
end

local function ApplyVehicleDamage(captureData, distance: number, effectiveRadius: number, now: number)
	if not captureData.Vehicle then
		return
	end
	if now - captureData.LastVehicleDamageTime < DAMAGE_TICK_INTERVAL then
		return
	end
	captureData.LastVehicleDamageTime = now
	local proximityScale = 1 - math.clamp(distance / math.max(effectiveRadius, 0.001), 0, 1)
	local damageAmount = VEHICLE_DAMAGE_PER_TICK * INTENSITY * (0.5 + proximityScale)
	CarModule.DealDamage(captureData.Vehicle, damageAmount)
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
		local intensity = math.clamp(math.floor(MAX_SCREENSHAKE_INTENSITY * normalized + 0.5), 1, MAX_SCREENSHAKE_INTENSITY)
		local signal = "Rumble"
		if distance <= INNER_CORE_RADIUS * INTENSITY then
			signal = "Quake"
		end
		FireScreenShake(player, signal, intensity, SCREENSHAKE_DURATION, now)
	end
end

local function ThrowCapturedAssembly(rootPart: BasePart, captureData, centerPosition: Vector3, now: number)
	local offset = rootPart.Position - centerPosition
	if offset.Magnitude < 0.001 then
		offset = Vector3.new(1, 0, 0)
	end
	local throwDirection = (offset.Unit + Vector3.new(0, 0.5, 0)).Unit
	local throwVelocity = throwDirection * (THROW_FORCE * INTENSITY)
	throwVelocity += Vector3.new(0, THROW_UPWARD_BOOST * INTENSITY, 0)
	rootPart.AssemblyLinearVelocity += throwVelocity

	if captureData.CharacterModel then
		local player = Players:GetPlayerFromCharacter(captureData.CharacterModel)
		if player then
			FireScreenShake(player, "Explosion", math.clamp(MAX_SCREENSHAKE_INTENSITY, 1, 10), SCREENSHAKE_DURATION, now)
		end
	end

	CapturedAssemblies[rootPart] = nil
	PostThrowImmunity[rootPart] = now + POST_THROW_IMMUNITY_DURATION
end

local DetectionAccumulator = 0
local UpdateAccumulator = 0

RunService.Heartbeat:Connect(function(deltaTime)
	DetectionAccumulator += deltaTime
	UpdateAccumulator += deltaTime

	local now = os.clock()
	local effectiveRadius = BASE_RADIUS * INTENSITY
	local centerPosition = CenterAttachment.WorldPosition

	if DetectionAccumulator >= DETECTION_REFRESH_RATE then
		DetectionAccumulator = 0
		local overlapParams = BuildOverlapParams()
		local parts = Workspace:GetPartBoundsInRadius(centerPosition, effectiveRadius, overlapParams)
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

	if UpdateAccumulator < UPDATE_RATE then
		return
	end
	local frameDelta = UpdateAccumulator
	UpdateAccumulator = 0

	local activeCount = 0
	for rootPart, captureData in pairs(CapturedAssemblies) do
		if activeCount >= MAX_AFFECTED_ASSEMBLIES then
			break
		end
		if not IsAssemblyValid(rootPart) then
			CapturedAssemblies[rootPart] = nil
			continue
		end

		local distance = (rootPart.Position - centerPosition).Magnitude
		if distance > effectiveRadius then
			CapturedAssemblies[rootPart] = nil
			continue
		end

		local isGettingSwirled = ApplyTornadoForces(rootPart, centerPosition, effectiveRadius, frameDelta)
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
