-- ScarletPose v1.5 Author: Xiaolongnu -- F12: on/off

local U = require("UEHelpers")

local VER    = "1.5"
local DEBUG  = false
local DRY    = false

local ARH    = "/Script/AssetRegistry.Default__AssetRegistryHelpers"
local EVEBP  = "/Game/Art/Character/PC/CH_P_EVE_01/Blueprints/CH_P_EVE_01_Blueprint.CH_P_EVE_01_Blueprint_C"
local TICKFN = EVEBP .. ":ReceiveTick"
local DIR    = "/Game/DLC_2/Art/Character/Monster/CH_M_NA_961/Animation/"
local VAN    = "/Proto_Idle."
local MENU   = "/Lobby/"
local BS = {
    "/Game/Art/Character/PC/CH_P_EVE_01/Animation/BlendSpace/IdleRun_BS_Peaceful2D.IdleRun_BS_Peaceful2D",
    "/Game/Art/Character/PC/CH_P_EVE_01/Animation/BlendSpace/IdleRun_BS_Peaceful2D_Roll.IdleRun_BS_Peaceful2D_Roll",
}
local POSE = {
    { "N_Scarlet_LookAround", 3 },
    { "N_Scarlet_Humming",    2 },
    { "N_Scarlet_TouchHat",   2 },
    { "N_Scarlet_Find",       1 },
    { "N_Scarlet_Idle",       0 },
}
local REST = #POSE
local NODES = {
    "SBAnimGraphNode_BlendSpacePlayer",
    "SBAnimGraphNode_BlendSpacePlayer_2",
    "SBAnimGraphNode_OverriddenBlendSpacePlayer",
    "SBAnimGraphNode_OverriddenBlendSpacePlayer_1",
    "SBAnimGraphNode_OverriddenBlendSpacePlayer_4",
}
local SPEED, STILL, FALL, TRIES, RETRY = 50, 5, 100, 44, 160
local POLL, QUIET = 0.05, 30
local LOADGAP = 40
local AFTER = 20
local SLOW, BACKOFF = 0.1, 400
local SETTLE = 200
local LEAD = 20
local FRESHWAIT = 2
local DEADAFTER = 3
local MINSW = 50
local LOBBYWAIT = 80
local HITCH, GAP, SUMMARY = 0.05, 2, 10

local HOME = (debug.getinfo(1, "S").source:sub(2):match("^@?(.*)[/\\]") or ".") .. "/.."
local SF = HOME .. "/state.txt"
local LF = HOME .. "/log.txt"

local function safe(f) local o, r = pcall(f) if o then return r end end
local function safe1(f, a) local o, r = pcall(f, a) if o then return r end end
local function _valid(o) return o.IsValid ~= nil and o:IsValid() end
local function _name(o) return o:GetFullName() end
local function _addr(o) return o:GetAddress() end
local function _find(p) return StaticFindObject(p) end
local function _world(c) return c:GetWorld() end
local function _gi(c) return c:GetWorld().OwningGameInstance end
local function _vel(c) return c:GetVelocity() end
local function _ctl(c) return c.Controller end
local function _ai(c) return c:GetSBSkeletalMeshComponent(0):GetAnimInstance() end
local function _node(ai, n) local d = ai[n] return d.BlendWeight, d.InternalTimeAccumulator end
local function _anim(e) return e.Animation end
local function _setanim(e, a) e.Animation = a end
local function _get(d) return d:get() end
local function _num(g) return g.ReferencedObjects:GetArrayNum() end
local function ok(o)
    if o == nil then return false end
    local a, b = pcall(_valid, o)
    return a and b == true
end
local ObjCache = {}

local function sfo(p)
    local o = ObjCache[p]
    if o and ok(o) then return o end
    o = safe1(_find, p)
    if ok(o) then ObjCache[p] = o return o end
    ObjCache[p] = nil
    return nil
end
local function fn(o) return tostring(safe1(_name, o) or "") end

local T0 = os.clock()
local function _append(s) local f = io.open(LF, "a") f:write(s) f:close() end
local function lg(f, ...)
    if not DEBUG then return end
    local o, s = pcall(string.format, f, ...)
    pcall(_append, string.format("%9.3f %s\n", os.clock() - T0, o and s or f))
end
local function hex(a) local o, s = pcall(string.format, "%X", a) return o and s or "-" end
local function clip(p) return p and (p:match("([^/.]+)%.[^.]+$") or p) or "-" end
local function wname(w) return w:match("([^/]+)$") or w end
if DEBUG then pcall(function() local f = io.open(LF, "w") f:close() end) end

local MK, PTH = { VAN }, {}
for i, p in ipairs(POSE) do
    MK[i + 1] = "/" .. p[1] .. "."
    PTH[i] = DIR .. p[1] .. "." .. p[1]
end
local ORDER = { REST }
for k = 1, #POSE - 1 do ORDER[#ORDER + 1] = k end
local function markOf(name)
    for _, m in ipairs(MK) do if name:find(m, 1, true) then return m end end
end

local Want, On, Cur, Van, Nxt, Eve, EveAddr = true, false, 0, nil, nil, nil, nil
local Act = 1
local Ready, Moved, Tries, Wait, Since, LoadAt, Urgent = false, false, 0, 0, 0, 0, false
local Prev, NoHold, Wr, SwAt, Rate = {}, false, {}, -MINSW, {}
local Fresh, FreshAt, PawnAddr = false, 0, nil
local HkA, HkB, FnA, Arh, Dead = nil, nil, nil, nil, {}
local Pre, Wn, AdoptT = false, "", 0

local LastB, Ours, SumT, Fr, Mx, H33, H50, OT, OM, NL = nil, 0, os.clock(), 0, 0, 0, 0, 0, 0, 0

local function save()
    safe(function()
        local f = io.open(SF, "w")
        f:write((Want and "1" or "0") .. "\n" .. (Van or "") .. "\n")
        f:close()
    end)
end
safe(function()
    local f = io.open(SF, "r")
    Want = f:read("*l") ~= "0"
    Van = f:read("*l")
    f:close()
end)
if Van == "" then Van = nil end

-- 修改 1（最重要）：给 hold 加地址缓存，消除 O(N) 全表扫描
local Held = {}   -- addr -> true，已 hold 过的对象地址，避免重复扫全表

local function _hold(g, o)
    local arr, a = g.ReferencedObjects, o:GetAddress()
    local n = arr:GetArrayNum()
    for k = 1, n do
        local e = arr[k]
        if e and e:GetAddress() == a then return false end
    end
    arr[n + 1] = o
    if arr:GetArrayNum() ~= n + 1 then error("no-grow") end
    return true
end
local function hold(o)
    if NoHold or not ok(o) then return end
    local a = safe1(_addr, o)
    if not a or Held[a] then return end          -- ← 命中缓存直接返回
    local gi = safe1(_gi, Eve)
    if not ok(gi) then lg("hold %s FAIL no-gi", clip(fn(o))) return end
    local g, added = pcall(_hold, gi, o)
    if not g then
        NoHold = true
        lg("hold FAIL %s -- tat giu clip ca phien", tostring(added))
    else
        if added then Held[a] = true end		-- 新增的缓存写入
        if DEBUG then
			lg("hold %s gi=%s num=%s", clip(fn(o)), hex(safe1(_addr, gi)), tostring(safe1(_num, gi)))
		end
    end
end

local function dead(p) return (Dead[p] or 0) >= DEADAFTER end


local function fetch(p, why)
    if not ok(Arh) then Arh = sfo(ARH) end
    if not Arh then lg("load %s FAIL no-arh", clip(p)) return nil, "no-arh" end
    local t0 = os.clock()
    safe(function() return Arh:GetAsset({ ObjectPath = U.FindOrAddFName(p) }) end)
    local dt = os.clock() - t0
    LoadAt = math.max(LoadAt, Since + ((dt > SLOW) and BACKOFF or LOADGAP))
    local o = sfo(p)
    if DEBUG then
        NL = NL + 1
        lg("load %s why=%s ms=%.1f ok=%s world=%s t=%.1f since=%d", clip(p), why, dt * 1000,
            tostring(o ~= nil), wname(Wn), os.clock() - AdoptT, Since)
    end
    if o then Dead[p] = nil hold(o) return o, "loaded" end
    Dead[p] = (Dead[p] or 0) + 1
    return nil, "fail"
end


local function load(p, force, why)
    local o = sfo(p)
    if o then return o end
    if dead(p) then return nil, "dead" end
    if not (force and Urgent) and Since < LoadAt then return nil, "wait" end
    Urgent = false
    return fetch(p, why)
end


local function lobby()
    if Pre or not Want or Since < LOBBYWAIT then return end
    Pre = true
    local t0, n = os.clock(), 0
    if Van then local v = sfo(Van) if v then hold(v) end end
    for _, i in ipairs(ORDER) do
        local p = PTH[i]
        local o = sfo(p)
        if o then hold(o)
        elseif not dead(p) then fetch(p, "lobby") n = n + 1 end
    end
    if DEBUG then
        local have = 0
        for _, p in ipairs(PTH) do if sfo(p) then have = have + 1 end end
        local gi = safe1(_gi, Eve)
        lg("lobby preload loads=%d ms=%.1f have=%d/%d gi=%s num=%s", n, (os.clock() - t0) * 1000,
            have, #PTH, hex(gi and safe1(_addr, gi)), tostring(gi and safe1(_num, gi)))
    end
end

math.randomseed(os.time())
local function pick()
    if Cur ~= REST and not dead(PTH[REST]) then return REST end
    for pass = 1, 2 do
        local function w(k)
            if k == Cur or (pass == 1 and k == Act) or dead(PTH[k]) then return 0 end
            return POSE[k][2]
        end
        local tot = 0
        for k = 1, #POSE do tot = tot + w(k) end
        if tot > 0 then
            local r = math.random(tot)
            for k = 1, #POSE do
                local x = w(k)
                if x > 0 then r = r - x if r <= 0 then return k end end
            end
        end
    end
    return Cur > 0 and Cur or REST
end

local function swap(bs, to, mark)
    local hit, good = 0, 0
    local toAddr = safe1(_addr, to)
    safe(function()
        bs.SampleData:ForEach(function(_, e)
            local s = e:get()
            local a = safe1(_anim, s)
            if not ok(a) then return end
            local name = fn(a)
            local m = markOf(name)
            if not m then return end
            hit = hit + 1
            if m == VAN then
                local p = name:match("^%S+%s+(.+)$")
                if p and p ~= Van then Van = p save() end
                hold(a)
            end
            if m == mark then good = good + 1 return end
            pcall(_setanim, s, to)
            local b = safe1(_anim, s)
            if ok(b) and safe1(_addr, b) == toAddr then good = good + 1 end
        end)
    end)
    return hit, good
end


local function bsmark()
    local r
    for j, path in ipairs(BS) do
        local bs = sfo(path)
        if not bs then return nil end
        local m
        safe(function()
            bs.SampleData:ForEach(function(_, e)
                if m then return end
                local a = safe1(_anim, e:get())
                if ok(a) then m = markOf(fn(a)) end
            end)
        end)
        if not m or (j > 1 and m ~= r) then return nil end
        r = m
    end
    for i, k in ipairs(MK) do if k == r then return i - 1 end end
end

local function apply(i, force)
    local t0 = os.clock()
    local to
    if i == 0 then
        if not Van then return false end
        to = load(Van, force, "on")
    else
        to = load(PTH[i], force, "on")
    end
    if not to then return false end
    hold(to)
    for _, path in ipairs(BS) do
        local bs = sfo(path)
        if not bs then return false end
        local hit, good = swap(bs, to, MK[i + 1])
        if hit == 0 or good ~= hit then
            lg("apply %d->%d FAIL hit=%d good=%d", Cur, i, hit, good)
            return false
        end
    end
    lg("apply %d->%d ms=%.1f", Cur, i, (os.clock() - t0) * 1000)
    Cur = i
    if i > 0 and i ~= REST then Act = i end
    LoadAt = math.max(LoadAt, Since + AFTER)
    return true
end
-- +++缓存 AnimInstance 和“有效节点”列表，去掉每 20ms 的 pcall 试错
local AI, NodeOK = nil, nil
local function getAI(c)
    if ok(AI) then return AI end
    local ai = safe1(_ai, c)
    if not ok(ai) then return nil end
    AI, NodeOK = ai, {}
    for k, n in ipairs(NODES) do
        local g, v = pcall(function() return ai[n] end)
        NodeOK[k] = (g and v ~= nil)
    end
    if DEBUG then
        local n2 = 0
        for _, v in ipairs(NodeOK) do if v then n2 = n2 + 1 end end
        lg("ai cached nodes=%d/%d", n2, #NODES)
    end
    return AI
end

local function first(m)
    if m and m > 0 then return m end
    if not dead(PTH[REST]) then return REST end
    for k = 1, #POSE do if not dead(PTH[k]) then return k end end
end

local function work()
    local c = Eve
    if not ok(c) then return end
    local v = safe1(_vel, c)
    if not v then return end
    local s2 = v.X * v.X + v.Y * v.Y

    if not Ready then
        if s2 >= SPEED * SPEED then Moved = true end
        local w = fn(safe1(_world, c))
        if w ~= "" then Wn = w end
        if w:find(MENU, 1, true) then lobby() return end
        if Since >= QUIET and (Moved or ok(safe1(_ctl, c))) then
            Ready = true
            if DEBUG then
                local have = 0
                for _, p in ipairs(PTH) do if sfo(p) then have = have + 1 end end
                lg("ready world=%s t=%.1f have=%d/%d want=%s", wname(Wn), os.clock() - AdoptT,
                    have, #PTH, tostring(Want))
            end
        end
        return
    end

    if Want ~= On then
        if Tries > TRIES then
            Wait = Wait + 1
            if Wait < RETRY then return end
            Wait = 0
        else
            Tries = Tries + 1
        end
        local m = bsmark()
        if not Want and (m == 0 or (m == nil and Cur == 0 and not Van)) then
            On, Tries, Wait = false, 0, 0
            lg("toggle off m=%s (da la dang goc)", tostring(m))
            return
        end
        local i = 0
        if Want then i = first(m) end
        if i and apply(i, true) then
            
            On, Tries, Wait, Prev, SwAt = Want, 0, 0, {}, Since
            Nxt = On and pick() or nil
            lg("toggle want=%s m=%s i=%d nxt=%s", tostring(Want), tostring(m), i, tostring(Nxt))
        end
        return
    end
    if not On then return end

    if s2 > STILL * STILL or v.Z > FALL or v.Z < -FALL then Prev = {} return end

    local ai = getAI(c)
    if not ai then return end
    local bw, bk, ak = 0, nil, nil
    for k, n in ipairs(NODES) do
        if NodeOK[k] then
            local w, t = _node(ai, n)
            if type(t) == "number" then
				local p, r0 = Prev[k], Rate[k]
				
				if p and p > 0.6 and t < p * 0.5 and r0 and r0 * MINSW < 1 then
					Wr[k] = p ak = ak or k
				else
					Wr[k] = nil
				end
				Rate[k] = (p and t > p) and (t - p) or nil
				w = type(w) == "number" and w or -1
				if w > bw then bw, bk = w, k end
				Prev[k] = t
			end
        end
    end
    local k = bw > 0 and bk or ak
    if k and Nxt and Wr[k] and Since - SwAt >= MINSW then
        if DEBUG then
            lg("seam k=%d bk=%s ak=%s bw=%.2f p=%.3f t=%.3f gap=%d", k, tostring(bk), tostring(ak), bw,
                Wr[k], Prev[k], Since - SwAt)
        end
        
        local to = Nxt
        if not sfo(PTH[to]) then to = (Cur ~= REST and sfo(PTH[REST])) and REST or nil end
        if to and apply(to) then
            SwAt = Since
            if to == Nxt then Nxt = pick() end
        end
        return
    end

    
    local r = bk and Rate[bk]
    if Nxt and Since >= LoadAt and r and (1 - Prev[bk]) / r >= LEAD then
        local _, why = load(PTH[Nxt], false, "next")
        if why == "dead" then Nxt = pick() end
    end
end

local Acc, SimT = 0, 0

local function adopt(c, a)
    Eve, EveAddr, Fresh = c, a, false
    Held, AI, NodeOK, ObjCache = {}, nil, nil, {}   -- ← 换角色/关卡，旧缓存全部失效
    
    Tries, Wait, On, Ready, Moved, Since, LoadAt, Urgent, Prev, SwAt, Acc, SimT =
        0, 0, nil, false, false, 0, SETTLE, true, {}, -MINSW, 0, 0
    Pre, AdoptT, LastB = false, os.clock(), nil
    Wn = fn(safe1(_world, c))
    if DEBUG then
        local gi = safe1(_gi, c)
        lg("adopt eve=%s world=%s gi=%s num=%s", hex(a), wname(Wn), hex(gi and safe1(_addr, gi)),
            tostring(gi and safe1(_num, gi)))
    end
end

local function summary(now)
    local span = now - SumT
    lg("sum %.0fs frames=%d fps=%.0f max=%.0fms >33ms=%d >50ms=%d ours=%.1fms ours_max=%.2fms loads=%d world=%s on=%s cur=%d",
        span, Fr, Fr / span, Mx * 1000, H33, H50, OT * 1000, OM * 1000, NL, wname(Wn), tostring(On), Cur)
    SumT, Fr, Mx, H33, H50, OT, OM, NL = now, 0, 0, 0, 0, 0, 0, 0
end


local function monitor(now)
    if LastB then
        local d = now - LastB
        if d > GAP then
            lg("gap %.1fs (tam dung / man hinh load)", d)
        else
            Fr = Fr + 1
            if d > Mx then Mx = d end
            if d > 0.033 then H33 = H33 + 1 end
            if d > HITCH then
                H50 = H50 + 1
                lg("hitch ms=%.0f prev_ours=%.1f world=%s t=%.1f ready=%s on=%s", d * 1000, Ours * 1000,
                    wname(Wn), now - AdoptT, tostring(Ready), tostring(On))
            end
        end
    end
    LastB = now
    if now - SumT >= SUMMARY then summary(now) end
end

local function beat(ctx, p)
    local c = safe1(_get, ctx)
    local a = c and safe1(_addr, c)
    if not a then return end
    if Fresh or a ~= EveAddr then
        local take = a == PawnAddr
            or (Fresh and os.clock() - FreshAt > FRESHWAIT)
            or (not Fresh and not ok(Eve))
        if not take then return end
        adopt(c, a)
    end
    local now = os.clock()
    if DEBUG then monitor(now) Ours = 0 end
    if DRY then return end
    if not Want and On == false then return end
	local dt = (type(p) == "number" and p) or safe1(_get, p)
    if type(dt) ~= "number" or dt <= 0 or dt > 1 then dt = POLL end
    SimT = SimT + dt
    Acc = Acc + dt
    if Acc < POLL then return end
    Acc, Since = 0, Since + 1
    pcall(work)
    if DEBUG then
        Ours = os.clock() - now
        OT = OT + Ours
        if Ours > OM then OM = Ours end
    end
end


RegisterKeyBind(Key.F12, function()
    if DRY then lg("F12 bo qua (DRY)") return end
    Want, Tries, Wait, Urgent = not Want, 0, 0, true
    save()
    lg("F12 want=%s", tostring(Want))
end)

local function reg(src)
    local f = sfo(TICKFN)
    if not f then lg("reg src=%s -- chua co lop BP cua Eve", src) return end
    local fa = safe1(_addr, f)
    if HkA and fa == FnA then return end
    if HkA then
        pcall(UnregisterHook, TICKFN, HkA, HkB)
        HkA, HkB = nil, nil
    end
    local okh, a, b = pcall(RegisterHook, TICKFN, beat)
    if okh and a then HkA, HkB, FnA = a, b, fa end
    lg("reg src=%s ok=%s fn=%s", src, tostring(okh and a ~= nil), hex(fa))
end

lg("start v%s want=%s van=%s dry=%s lobbywait=%d", VER, tostring(Want), clip(Van), tostring(DRY), LOBBYWAIT)

pcall(RegisterHook, "/Script/Engine.PlayerController:ClientRestart", function(_, pawn)
    local pw = pawn and safe1(_get, pawn)
    PawnAddr = ok(pw) and safe1(_addr, pw) or nil
    Fresh, FreshAt = true, os.clock()
    lg("restart pawn=%s", hex(PawnAddr))
    reg("restart")
end)
reg("init")
