-- fileheader (common:header)

args = args or {...}

-- if jit and jit.opt then
--     -- boost jit limits
--     jit.opt.start("maxsnap=1000","loopunroll=500","maxmcode=2048")
-- end

local __LONG_INT_CLASS__

local setmetatable = setmetatable
local assert = assert
local error = error
local bit = bit32
local math = math
local bit_tobit = function(a) return bit.rshift(a,0) end
local bit_arshift = bit.arshift
local bit_rshift = bit.rshift
local bit_lshift = bit.lshift
local bit_band = bit.band
local bit_bor = bit.bor
local bit_bxor = bit.bxor
local bit_ror = bit.rrotate
local bit_rol = bit.lrotate
local math_huge = math.huge
local math_floor = math.floor
local math_ceil = math.ceil
local math_abs = math.abs
local math_max = math.max
local math_min = math.min
local math_pow = math.pow
local math_sqrt = math.sqrt
local math_ldexp = math.ldexp
local math_frexp = math.frexp
local math_log = math.log

if jit and jit.version_num < 20100 then
    function math_frexp(dbl)
        local aDbl = math_abs(dbl)
    
        if dbl ~= 0 and (aDbl ~= math_huge) then
            local exp = math_max(-1023,math_floor(math_log(aDbl,2) + 1))
            local x = aDbl * math_pow(2,-exp)
    
            if dbl < 0 then
                x = -x
            end
    
            return x,exp
        end
    
        return dbl,0
    end
end

local function __TRUNC__(n)
    if n >= 0 then return math_floor(n) end
    return math_ceil(n)
end

local function __LONG_INT__(low,high)
    -- Note: Avoid using tail-calls on builtins
    -- This aborts a JIT trace, and can be avoided by wrapping tail calls in parentheses
    return (setmetatable({low,high},__LONG_INT_CLASS__))
end

local function __LONG_INT_N__(n) -- operates on non-normalized integers
    -- convert a double value to i64 directly
    local high = bit_tobit(math_floor(n / (2^32))) -- manually rshift by 32
    local low = bit_tobit(n % (2^32)) -- wtf? normal bit conversions are not sufficent according to tests
    return (setmetatable({low,high},__LONG_INT_CLASS__))
end

_G.__LONG_INT__ = __LONG_INT__
_G.__LONG_INT_N__ = __LONG_INT_N__

-- Modules are entirely localised and can be modified post load
local __IMPORTS__ = {}
local __GLOBALS__ = {}
local __SETJMP_STATES__ = setmetatable({},{__mode="k"})
local __FUNCS__ = {}
local __EXPORTS__ = {}
local __BINDINGS__ = {}
local __BINDER__ = {arrays = {},ptrArrays = {}}

local module = {
    imports = __IMPORTS__,
    exports = __EXPORTS__,
    globals = __GLOBALS__,
    funcs = __FUNCS__,
    bindings = __BINDINGS__,
    binder = __BINDER__,
}

function module.setImports(imp)
    __IMPORTS__ = imp
    module.imports = imp
end

local function __STACK_POP__(__STACK__)
    local v = __STACK__[#__STACK__]
    __STACK__[#__STACK__] = nil
    return v
end

local function __UNSIGNED__(value)
    if value < 0 then
        value = value + 4294967296
    end

    return value
end

-- Adapted from https://github.com/notcake/glib/blob/master/lua/glib/bitconverter.lua
-- with permission from notcake
local function UInt32ToFloat(int)
    local negative = int < 0 -- check if first bit is 0
    if negative then int = int - 0x80000000 end

    local exponent = bit_rshift(bit_band(int, 0x7F800000), 23) -- and capture lowest 9 bits
    local significand = bit_band(int, 0x007FFFFF) / (2 ^ 23) -- discard lowest 9 bits and turn into a fraction

    local float

    if exponent == 0 then
        -- special case 1
        float = significand == 0 and 0 or math_ldexp(significand,-126)
    elseif exponent == 0xFF then
        -- special case 2
        float = significand == 0 and math_huge or (math_huge - math_huge) -- inf or nan
    else
        float = math_ldexp(significand + 1,exponent - 127)
    end

    return negative and -float or float
end

local function FloatToUInt32(float)
    local int = 0

    -- wtf -0
    if (float < 0) or ((1 / float) < 0) then
        int = int + 0x80000000
        float = -float
    end

    local exponent = 0
    local significand = 0

    if float == math_huge then
        -- special case 2.1
        exponent = 0xFF
        -- significand stays 0
    elseif float ~= float then -- nan
        -- special case 2.2
        exponent = 0xFF
        significand = 1
    elseif float ~= 0 then
        significand,exponent = math_frexp(float)
        exponent = exponent + 126 -- limit to 8 bits (u get what i mean)

        if exponent <= 0 then
            -- denormal float

            significand = math_floor(significand * 2 ^ (23 + exponent) + 0.5)
            -- ^ convert to back to whole number

            exponent = 0
        else
            significand = math_floor((significand * 2 - 1) * 2 ^ 23 + 0.5)
            -- ^ convert to back to whole number
        end
    end

    int = int + bit_lshift(bit_band(exponent, 0xFF), 23) -- stuff high 8 bits with exponent (after first sign bit)
    int = int + bit_band(significand, 0x007FFFFF) -- stuff low 23 bits with significand

    return bit_tobit(int)
end

local function UInt32sToDouble(uint_low,uint_high)
    local negative = false
    -- check if first bit is 0
    if uint_high < 0 then
        uint_high = uint_high - 0x80000000
        -- set first bit to  0 ^
        negative = true
    end

    local exponent = bit_rshift(uint_high, 20) -- and capture lowest 11 bits
    local significand = (bit_band(uint_high, 0x000FFFFF) * 0x100000000 + uint_low) / (2 ^ 52) -- discard low bits and turn into a fraction

    local double = 0

    if exponent == 0 then
        -- special case 1
        double = significand == 0 and 0 or math_ldexp(significand,-1022)
    elseif exponent == 0x07FF then
        -- special case 2
        double = significand == 0 and math_huge or (math_huge - math_huge) -- inf or nan
    else
        double = math_ldexp(significand + 1,exponent - 1023)
    end

    return negative and -double or double
end

local function DoubleToUInt32s(double)
    local uint_low = 0
    local uint_high = 0

    -- wtf -0
    if (double < 0) or ((1 / double) < 0) then
        uint_high = uint_high + 0x80000000
        double = -double
    end

    local exponent = 0
    local significand = 0

    if double == math_huge then
        -- special case 2.1
        exponent = 0x07FF
        -- significand stays 0
    elseif double ~= double then -- nan
        -- special case 2.2
        exponent = 0x07FF
        significand = 1
    elseif double ~= 0 then
        significand,exponent = math_frexp(double)
        exponent = exponent + 1022 -- limit to 10 bits (u get what i mean)

        if exponent <= 0 then
            -- denormal double

            significand = math_floor(significand * 2 ^ (52 + exponent) + 0.5)
            -- ^ convert to back to whole number

            exponent = 0
        else
            significand = math_floor((significand * 2 - 1) * 2 ^ 52 + 0.5)
            -- ^ convert to back to whole number
        end
    end

    -- significand is partially in low and high uints
    uint_low = significand % 0x100000000
    uint_high = uint_high + bit_lshift(bit_band(exponent, 0x07FF), 20)
    uint_high = uint_high + bit_band(math_floor(significand / 0x100000000), 0x000FFFFF)

    return bit_tobit(uint_low), bit_tobit(uint_high)
end
-- pure lua memory lib

local function __MEMORY_GROW__(mem,pages)
    local old_pages = mem._page_count
    local new_pages = old_pages + pages

    -- check if new size exceeds the size limit
    if new_pages > mem._max_pages then
        return -1
    end

    -- 16k cells = 64kb = 1 page
    local cell_start = old_pages * 16 * 1024
    local cell_end = new_pages * 16 * 1024 - 1

    for i = cell_start, cell_end do 
        mem.data[i] = 0
    end

    mem._len = new_pages * 64 * 1024
    mem._page_count = new_pages
    return old_pages
end

--[[
    Float mapping overview:
    - mem._fp_map is a sparse map that indicates where floats and doubles are stored in memory.
    - The mapping system only works when floats are cell-aligned (the float or double's address is a multiple of 4).
    - Any memory write can update the map: writing a byte in a cell occupied by a float will force the entire cell to revert to an integer value.
    - In the interest of speed and local slot conservation, all constants have been inlined. Their values:
        - nil: Cell is occupied by integer data.
        -   1: Cell is occupied by a single-width float.
        -   2: Cell contains the low half of a double-width float. GUARANTEES that a (3) follows.
        -   3: Cell contains the high half of a double-width float. GUARANTEES that a (2) precedes.
]]

local function __MEMORY_READ_8__(mem,loc)
    assert((loc >= 0) and (loc < mem._len),"out of memory access")

    local cell_loc = bit_rshift(loc,2)
    local byte_loc = bit_band(loc,3)

    local cell_value
    local mem_t = mem._fp_map[cell_loc]
    if mem_t == nil then
        cell_value = mem.data[cell_loc]
    else
        if mem_t == 1 then
            cell_value = FloatToUInt32(mem.data[cell_loc])
        else
            local low, high = DoubleToUInt32s(mem.data[cell_loc])
            if mem_t == 2 then
                cell_value = low
            else
                cell_value = high
            end
        end
    end

    return bit_band(bit_rshift(cell_value, byte_loc * 8),255)
end

local function __MEMORY_READ_16__(mem,loc)
    assert((loc >= 0) and (loc < (mem._len - 1)),"out of memory access")
    -- 16 bit reads/writes are less common, they can be optimized later
    return bit_bor(
        __MEMORY_READ_8__(mem,loc),
        bit_lshift(__MEMORY_READ_8__(mem,loc + 1),8)
    )
end

local function __MEMORY_READ_32__(mem,loc)
    assert((loc >= 0) and (loc < (mem._len - 3)),"out of memory access")

    if bit_band(loc,3) == 0 then
        -- aligned read, fast path
        local cell_loc = bit_rshift(loc,2)

        local mem_t = mem._fp_map[cell_loc]
        if mem_t ~= nil then
            if mem_t == 1 then
                return FloatToUInt32(mem.data[cell_loc])
            else
                local low, high = DoubleToUInt32s(mem.data[cell_loc])
                if mem_t == 2 then
                    return low
                else
                    return high
                end
            end
        end

        local val = mem.data[cell_loc]
        -- It breaks in some way I don't understand if you don't normalize the value.
        return bit_tobit(val)
    else
        --print("bad alignment (read 32)",alignment)
        return bit_bor(
            __MEMORY_READ_8__(mem,loc),
            bit_lshift(__MEMORY_READ_8__(mem,loc + 1),8),
            bit_lshift(__MEMORY_READ_8__(mem,loc + 2),16),
            bit_lshift(__MEMORY_READ_8__(mem,loc + 3),24)
        )
    end
end

-- I also tried some weird shift/xor logic,
-- both had similar performance but I kept this becuase it was simpler.
local mask_table = {0xFFFF00FF,0xFF00FFFF,0x00FFFFFF}
mask_table[0] = 0xFFFFFF00
local function __MEMORY_WRITE_8__(mem,loc,val)
    assert((loc >= 0) and (loc < mem._len),"out of memory access")
    val = bit_band(val,255)

    local cell_loc = bit_rshift(loc,2)
    local byte_loc = bit_band(loc,3)

    local mem_t = mem._fp_map[cell_loc]
    local old_cell
    if mem_t == nil then
        -- fast path, the cell is already an integer
        old_cell = mem.data[cell_loc]
    else
        -- bad news, a float is stored here and we have to convert it to an integer
        mem._fp_map[cell_loc] = nil
        if mem_t == 1 then
            -- float
            old_cell = FloatToUInt32(mem.data[cell_loc])
        else
            -- double: we must also update the matching cell
            local low, high = DoubleToUInt32s(mem.data[cell_loc])
            if mem_t == 2 then
                -- this cell is the low half
                old_cell = low

                mem.data[cell_loc + 1] = high
                mem._fp_map[cell_loc + 1] = nil
            else
                -- this cell is the high half
                old_cell = high

                mem.data[cell_loc - 1] = low
                mem._fp_map[cell_loc - 1] = nil
            end
        end
    end

    old_cell = bit_band(old_cell, mask_table[byte_loc])
    local new_cell = bit_bor(old_cell, bit_lshift(val,byte_loc * 8))

    mem.data[cell_loc] = new_cell
end

local function __MEMORY_WRITE_16__(mem,loc,val)
    assert((loc >= 0) and (loc < (mem._len - 1)),"out of memory access")
    -- 16 bit reads/writes are less common, they can be optimized later
    __MEMORY_WRITE_8__(mem,loc,     val)
    __MEMORY_WRITE_8__(mem,loc + 1, bit_rshift(val,8))
end

local function __MEMORY_WRITE_32__(mem,loc,val)
    assert((loc >= 0) and (loc < (mem._len - 3)),"out of memory access")

    if bit_band(loc,3) == 0 then
        -- aligned write, fast path
        local cell_loc = bit_rshift(loc,2)
        mem._fp_map[cell_loc] = nil -- mark this cell as an integer
        mem.data[cell_loc] = val
    else
        --print("bad alignment (write 32)",alignment)
        __MEMORY_WRITE_8__(mem,loc,     val)
        __MEMORY_WRITE_8__(mem,loc + 1, bit_rshift(val,8))
        __MEMORY_WRITE_8__(mem,loc + 2, bit_rshift(val,16))
        __MEMORY_WRITE_8__(mem,loc + 3, bit_rshift(val,24))
    end
end

local function __MEMORY_READ_32F__(mem,loc)
    assert((loc >= 0) and (loc < (mem._len - 3)),"out of memory access")

    local cell_loc = bit_rshift(loc,2)
    local byte_loc = bit_band(loc,3)

    if byte_loc == 0 and mem._fp_map[cell_loc] == 1 then
        return mem.data[cell_loc]
    else
        -- Let __MEMORY_READ_32__ handle any issues.
        return UInt32ToFloat(__MEMORY_READ_32__(mem,loc))
    end
end

local function __MEMORY_READ_64F__(mem,loc)
    assert((loc >= 0) and (loc < (mem._len - 7)),"out of memory access")

    local cell_loc = bit_rshift(loc,2)
    local byte_loc = bit_band(loc,3)

    local mem_t = mem._fp_map[cell_loc]

    if byte_loc == 0 and mem_t == 2 then
        return mem.data[cell_loc]
    else
        -- Let __MEMORY_READ_32__ handle any issues.
        return UInt32sToDouble(__MEMORY_READ_32__(mem,loc),__MEMORY_READ_32__(mem,loc + 4))
    end
end

local function __MEMORY_WRITE_32F__(mem,loc,val)
    assert((loc >= 0) and (loc < (mem._len - 3)),"out of memory access")

    if bit_band(loc,3) == 0 then
        local cell_loc = bit_rshift(loc,2)
        mem._fp_map[cell_loc] = 1
        mem.data[cell_loc] = val
    else
        -- unaligned writes can't use the float map.
        __MEMORY_WRITE_32__(mem,loc,FloatToUInt32(val))
    end
end

local function __MEMORY_WRITE_64F__(mem,loc,val)
    assert((loc >= 0) and (loc < (mem._len - 7)),"out of memory access")

    if bit_band(loc,3) == 0 then
        local cell_loc = bit_rshift(loc,2)
        mem._fp_map[cell_loc] = 2
        mem.data[cell_loc] = val
        mem._fp_map[cell_loc + 1] = 3
        mem.data[cell_loc + 1] = val
    else
        -- unaligned writes can't use the float map.
        local low,high = DoubleToUInt32s(val)
        __MEMORY_WRITE_32__(mem,loc,low)
        __MEMORY_WRITE_32__(mem,loc + 4,high)
    end
end

local function __MEMORY_INIT__(mem,loc,data)
    for i = 1, #data do -- TODO RE-OPTIMIZE
        __MEMORY_WRITE_8__(mem, loc + i-1, data:byte(i))
    end
end

local function __MEMORY_ALLOC__(pages, max_pages)
    local mem = {}
    mem.data = {}
    mem._page_count = pages
    mem._len = pages * 64 * 1024
    mem._fp_map = {}
    mem._max_pages = max_pages or 1024

    local cellLength = pages * 16 * 1024 -- 16k cells = 64kb = 1 page
    for i=0,cellLength - 1 do mem.data[i] = 0 end

    mem.write8 = __MEMORY_WRITE_8__
    mem.write16 = __MEMORY_WRITE_16__
    mem.write32 = __MEMORY_WRITE_32__

    mem.read8 = __MEMORY_READ_8__
    mem.read16 = __MEMORY_READ_16__
    mem.read32 = __MEMORY_READ_32__

    __SETJMP_STATES__[mem] = {}

    return mem
end
-- fileheader (common:footer)

-- extra bit ops

local __clz_tab = {3, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0}
__clz_tab[0] = 4

local function __CLZ__(x)
    local n = 0
    if bit_band(x,-65536)     == 0 then n = 16;    x = bit_lshift(x,16) end
    if bit_band(x,-16777216)  == 0 then n = n + 8; x = bit_lshift(x,8) end
    if bit_band(x,-268435456) == 0 then n = n + 4; x = bit_lshift(x,4) end
    n = n + __clz_tab[bit_rshift(x,28)]
    return n
end

local __ctz_tab = {}

for i = 0,31 do
    __ctz_tab[ bit_rshift( 125613361 * bit_lshift(1,i) , 27 ) ] = i
end

local function __CTZ__(x)
    if x == 0 then return 32 end
    return __ctz_tab[ bit_rshift( bit_band(x,-x) * 125613361 , 27 ) ]
end

local __popcnt_tab = {
      1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
}
__popcnt_tab[0] = 0

local function __POPCNT__(x)
    -- the really cool algorithm uses a multiply that can overflow, so we're stuck with a LUT
    return __popcnt_tab[bit_band(x,255)]
    + __popcnt_tab[bit_band(bit_rshift(x,8),255)]
    + __popcnt_tab[bit_band(bit_rshift(x,16),255)]
    + __popcnt_tab[bit_rshift(x,24)]
end

-- division helpers

local function __IDIV_S__(a,b)
    local res_1 = a / b
    local res_2 = math_floor(res_1)
    if res_1 ~= res_2 and res_2 < 0 then res_2 = res_2 + 1 end
    local int = bit_tobit(res_2)
    if res_2 ~= int then error("bad division") end
    return int
end

local function __IDIV_U__(a,b)
    local res = math_floor(__UNSIGNED__(a) / __UNSIGNED__(b))
    local int = bit_tobit(res)
    if res ~= int then error("bad division") end
    return int
end

local function __IMOD_S__(a,b)
    if b == 0 then error("bad modulo") end
    local res = math_abs(a) % math_abs(b)
    if a < 0 then  res = -res end
    return bit_tobit(res)
end

local function __IMOD_U__(a,b)
    if b == 0 then error("bad modulo") end
    local res = __UNSIGNED__(a) % __UNSIGNED__(b)
    return bit_tobit(res)
end

-- Multiply two 32 bit integers without busting due to precision loss on overflow
local function __IMUL__(a,b)
    local a_low = bit_band(a,65535)
    local b_low = bit_band(b,65535)

    return bit_tobit(
        a_low * b_low +
        bit_lshift(a_low * bit_rshift(b,16),16) +
        bit_lshift(b_low * bit_rshift(a,16),16)
    )
end

-- Extra math functions for floats, stored in their own table since they're not likely to be used often.
local __FLOAT__ = {
    nearest = function(x)
        if x % 1 == .5 then
            -- Must round toward even in the event of a tie.
            local y = math_floor(x)
            return y + (y % 2)
        end
        return math_floor(x + .5)
    end,
    truncate = function(x)
        return x > 0 and math_floor(x) or math_ceil(x)
    end,
    copysign = function(x,y)
        -- Does not handle signed zero, but who really cares?
        local sign = y > 0 and 1 or -1
        return x * sign
    end,
    min = function(x,y)
        if x ~= x or y ~= y then return 0 / 0 end
        return math_min(x,y)
    end,
    max = function(x,y)
        if x ~= x or y ~= y then return 0 / 0 end
        return math_max(x,y)
    end
}

-- Multiply and divide code adapted from 
    -- https://github.com/BixData/lua-long/ which is adapted from
    -- https://github.com/dcodeIO/long.js which is adapted from
    -- https://github.com/google/closure-library

-- This is the core division routine used by other division functions.
local function __LONG_INT_DIVIDE__(rem,divisor)
    assert(divisor[1] ~= 0 or divisor[2] ~= 0,"divide by zero")

    local res = __LONG_INT__(0,0)

    local d_approx = __UNSIGNED__(divisor[1]) + __UNSIGNED__(divisor[2]) * 4294967296

    while rem:_ge_u(divisor) do
        local n_approx = __UNSIGNED__(rem[1]) + __UNSIGNED__(rem[2]) * 4294967296

        -- Don't allow our approximation to be larger than an i64
        n_approx = math_min(n_approx, 18446744073709549568)

        local q_approx = math_max(1, math_floor(n_approx / d_approx))

        -- dark magic from long.js / closure lib
        local log2 = math_ceil(math_log(q_approx, 2))
        local delta = math_pow(2,math_max(0,log2 - 48))

        local res_approx = __LONG_INT_N__(q_approx)
        local rem_approx = res_approx * divisor

        -- decrease approximation until smaller than remainder and the multiply hopefully
        while rem_approx:_gt_u(rem) do
            q_approx = q_approx - delta
            res_approx = __LONG_INT_N__(q_approx)
            rem_approx = res_approx * divisor
        end

        -- res must be at least one, lib I copied the algo from had this check
        -- but I'm not sure is necessary or makes sense
        if res_approx[1] == 0 and res_approx[2] == 0 then
            error("res_approx = 0")
            res_approx[1] = 1
        end

        res = res + res_approx
        rem = rem - rem_approx
    end

    return res, rem
end

__LONG_INT_CLASS__ = {
    __tostring = function(self)
        return "__LONG_INT__(" .. self[1] .. "," .. self[2] .. ")"
    end,
    __add = function(a,b)
        local low = __UNSIGNED__(a[1]) + __UNSIGNED__(b[1])
        local high = a[2] + b[2] + (low >= 4294967296 and 1 or 0)
        return __LONG_INT__( bit_tobit(low), bit_tobit(high) )
    end,
    __sub = function(a,b)
        local low = __UNSIGNED__(a[1]) - __UNSIGNED__(b[1])
        local high = a[2] - b[2] - (low < 0 and 1 or 0)
        return __LONG_INT__( bit_tobit(low), bit_tobit(high) )
    end,
    __mul = function(a,b)
        -- I feel like this is excessive but I'm going to
        -- defer to the better wizard here.

        local a48 = bit_rshift(a[2],16)
        local a32 = bit_band(a[2],65535)
        local a16 = bit_rshift(a[1],16)
        local a00 = bit_band(a[1],65535)

        local b48 = bit_rshift(b[2],16)
        local b32 = bit_band(b[2],65535)
        local b16 = bit_rshift(b[1],16)
        local b00 = bit_band(b[1],65535)

        local c00 = a00 * b00
        local c16 = bit_rshift(c00,16)
        c00 = bit_band(c00,65535)

        c16 = c16 + a16 * b00
        local c32 = bit_rshift(c16,16)
        c16 = bit_band(c16,65535)

        c16 = c16 + a00 * b16
        c32 = c32 + bit_rshift(c16,16)
        c16 = bit_band(c16,65535)

        c32 = c32 + a32 * b00
        local c48 = bit_rshift(c32,16)
        c32 = bit_band(c32,65535)

        c32 = c32 + a16 * b16
        c48 = c48 + bit_rshift(c32,16)
        c32 = bit_band(c32,65535)

        c32 = c32 + a00 * b32
        c48 = c48 + bit_rshift(c32,16)
        c32 = bit_band(c32,65535)

        c48 = c48 + a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48
        c48 = bit_band(c48,65535)

        return __LONG_INT__(
            bit_bor(c00,bit_lshift(c16,16)),
            bit_bor(c32,bit_lshift(c48,16))
        )
    end,
    __eq = function(a,b)
        return a[1] == b[1] and a[2] == b[2]
    end,
    __lt = function(a,b) -- <
        if a[2] == b[2] then return a[1] < b[1] else return a[2] < b[2] end
    end,
    __le = function(a,b) -- <=
        if a[2] == b[2] then return a[1] <= b[1] else return a[2] <= b[2] end
    end,
    __index = {
        store = function(self,mem,loc)
            assert((loc >= 0) and (loc < (mem._len - 7)),"out of memory access")

            local low = self[1]
            local high = self[2]

            __MEMORY_WRITE_32__(mem,loc,low)
            __MEMORY_WRITE_32__(mem,loc + 4,high)
        end,
        load = function(self,mem,loc)

            local low =  __MEMORY_READ_32__(mem,loc)
            local high = __MEMORY_READ_32__(mem,loc + 4)

            self[1] = low
            self[2] = high
        end,
        store32 = function(self,mem,loc)
           __MEMORY_WRITE_32__(mem,loc,self[1])
        end,
        store16 = function(self,mem,loc)
            __MEMORY_WRITE_16__(mem,loc,self[1])
        end,
        store8 = function(self,mem,loc)
            __MEMORY_WRITE_8__(mem,loc,self[1])
        end,
        _div_s = function(a,b)
            local negate_result = false
            if a[2] < 0 then
                a = __LONG_INT__(0,0) - a
                negate_result = not negate_result
            end

            if b[2] < 0 then
                b = __LONG_INT__(0,0) - b
                negate_result = not negate_result
            end

            local res, rem = __LONG_INT_DIVIDE__(a,b)
            if res[2] < 0 then
                error("division overflow")
            end
            if negate_result then
                res = __LONG_INT__(0,0) - res
            end
            return res
        end,
        _div_u = function(a,b)
            local res, rem = __LONG_INT_DIVIDE__(a,b)
            return res
        end,
        _rem_s = function(a,b)
            local negate_result = false
            if a[2] < 0 then
                a = __LONG_INT__(0,0) - a
                negate_result = not negate_result
            end

            if b[2] < 0 then
                b = __LONG_INT__(0,0) - b
            end

            local res, rem = __LONG_INT_DIVIDE__(a,b)

            if negate_result then
                rem = __LONG_INT__(0,0) - rem
            end

            return rem
        end,
        _rem_u = function(a,b)
            local res, rem = __LONG_INT_DIVIDE__(a,b)
            return rem
        end,
        _lt_u = function(a,b)
            if __UNSIGNED__(a[2]) == __UNSIGNED__(b[2]) then
                return __UNSIGNED__(a[1]) < __UNSIGNED__(b[1])
            else
                return __UNSIGNED__(a[2]) < __UNSIGNED__(b[2])
            end
        end,
        _le_u = function(a,b)
            if __UNSIGNED__(a[2]) == __UNSIGNED__(b[2]) then
                return __UNSIGNED__(a[1]) <= __UNSIGNED__(b[1])
            else
                return __UNSIGNED__(a[2]) <= __UNSIGNED__(b[2])
            end
        end,
        _gt_u = function(a,b)
            if __UNSIGNED__(a[2]) == __UNSIGNED__(b[2]) then
                return __UNSIGNED__(a[1]) > __UNSIGNED__(b[1])
            else
                return __UNSIGNED__(a[2]) > __UNSIGNED__(b[2])
            end
        end,
        _ge_u = function(a,b)
            if __UNSIGNED__(a[2]) == __UNSIGNED__(b[2]) then
                return __UNSIGNED__(a[1]) >= __UNSIGNED__(b[1])
            else
                return __UNSIGNED__(a[2]) >= __UNSIGNED__(b[2])
            end
        end,
        _shl = function(a,b)
            local shift = bit_band(b[1],63)

            local low, high
            if shift < 32 then
                high = bit_bor( bit_lshift(a[2],shift), shift == 0 and 0 or bit_rshift(a[1], 32-shift) )
                low = bit_lshift(a[1],shift)
            else
                low = 0
                high = bit_lshift(a[1],shift-32)
            end

            return __LONG_INT__(low,high)
        end,
        _shr_u = function(a,b)
            local shift = bit_band(b[1],63)

            local low, high
            if shift < 32 then
                low = bit_bor( bit_rshift(a[1],shift), shift == 0 and 0 or bit_lshift(a[2], 32-shift) )
                high = bit_rshift(a[2],shift)
            else
                low = bit_rshift(a[2],shift-32)
                high = 0
            end

            return __LONG_INT__(low,high)
        end,
        _shr_s = function(a,b)
            local shift = bit_band(b[1],63)

            local low, high
            if shift < 32 then
                low = bit_bor( bit_rshift(a[1],shift), shift == 0 and 0 or bit_lshift(a[2], 32-shift) )
                high = bit_arshift(a[2],shift)
            else
                low = bit_arshift(a[2],shift-32)
                high = bit_arshift(a[2],31)
            end

            return __LONG_INT__(low,high)
        end,
        _rotr = function(a,b)
            local shift = bit_band(b[1],63)
            local short_shift = bit_band(shift,31)

            local res1, res2
            if short_shift == 0 then
                -- Need this special case because shifts of 32 aren't valid :(
                res1 = a[1]
                res2 = a[2]
            else
                res1 = bit_bor( bit_rshift(a[1],short_shift), bit_lshift(a[2], 32-short_shift) )
                res2 = bit_bor( bit_rshift(a[2],short_shift), bit_lshift(a[1], 32-short_shift) )
            end

            if shift < 32 then
                return __LONG_INT__(res1,res2)
            else
                return __LONG_INT__(res2,res1)
            end
        end,
        _rotl = function(a,b)
            local shift = bit_band(b[1],63)
            local short_shift = bit_band(shift,31)

            local res1, res2
            if short_shift == 0 then
                -- Need this special case because shifts of 32 aren't valid :(
                res1 = a[1]
                res2 = a[2]
            else
                res1 = bit_bor( bit_lshift(a[1],short_shift), bit_rshift(a[2], 32-short_shift) )
                res2 = bit_bor( bit_lshift(a[2],short_shift), bit_rshift(a[1], 32-short_shift) )
            end

            if shift < 32 then
                return __LONG_INT__(res1,res2)
            else
                return __LONG_INT__(res2,res1)
            end
        end,
        _or = function(a,b)
            return __LONG_INT__(bit_bor(a[1],b[1]), bit_bor(a[2],b[2]))
        end,
        _and = function(a,b)
            return __LONG_INT__(bit_band(a[1],b[1]), bit_band(a[2],b[2]))
        end,
        _xor = function(a,b)
            return __LONG_INT__(bit_bxor(a[1],b[1]), bit_bxor(a[2],b[2]))
        end,
        _clz = function(a)
            local result = (a[2] ~= 0) and __CLZ__(a[2]) or 32 + __CLZ__(a[1])
            return __LONG_INT__(result,0)
        end,
        _ctz = function(a)
            local result = (a[1] ~= 0) and __CTZ__(a[1]) or 32 + __CTZ__(a[2])
            return __LONG_INT__(result,0)
        end,
        _popcnt = function(a)
            return __LONG_INT__( __POPCNT__(a[1]) + __POPCNT__(a[2]), 0)
        end,
    }
}

do
    local mem_0 = __MEMORY_ALLOC__(17);
    module.memory = mem_0
    do
        __GLOBALS__[0] = 1048576;
    end
    local __TABLE_FUNCS_0__ = {};
    local __TABLE_OFFSET_0_0__ = {};
    do
        __TABLE_OFFSET_0_0__ = 1 + 1;
    
    end
    __MEMORY_INIT__(mem_0,1048576,'src\\lib.rs\x00\x00\x00\x00\x10\x00\x0a\x00\x00\x004\x00\x00\x00\x10\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00d\x00\x00\x00\x19\x00\x00\x00\xe8\x03\x00\x00\xa8\x00\x00\x00\x10\'\x00\x00\xcd\x04\x00\x00\xa0\x86\x01\x00x%\x00\x00@B\x0f\x00\xa22\x01\x00\x80\x96\x98\x00\x03$\x0a\x00\x00\xe1\xf5\x05\xaf\xe9W\x00\x00\xca\x9a;.\xdf\x07\x03\x00\x00\x10\x00\x0a\x00\x00\x00^\x00\x00\x00\x10\x00\x00\x00, \x0a\x00v\x00\x10\x00\x01\x00\x00\x00Passes: \x80\x00\x10\x00\x08\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Time: \x00\x00\x98\x00\x10\x00\x06\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Avg: \x00\x00\x00\xb0\x00\x10\x00\x05\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Limit: \x00\xc8\x00\x10\x00\x07\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Count1: \xe0\x00\x10\x00\x08\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Count2: \xf8\x00\x10\x00\x08\x00\x00\x00t\x00\x10\x00\x02\x00\x00\x00Valid: \x00\x10\x01\x10\x00\x07\x00\x00\x00v\x00\x10\x00\x01\x00\x00\x00Azgrom;;;1;algorithm=base,faithful=yes\x0a\x00(\x01\x10\x00\x07\x00\x00\x00/\x01\x10\x00\x01\x00\x00\x000\x01\x10\x00\x1f\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x0b\x00\x00\x00\x0c\x00\x00\x00\x0d\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x0e\x00\x00\x00\x0f\x00\x00\x00\x10\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x11\x00\x00\x00\x12\x00\x00\x00\x13\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x14\x00\x00\x00already borrowedalready mutably borrowed\x0a\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x15\x00\x00\x00assertion failed: mid <= self.len()/rustc/59eed8a2aac0230a8b53e89d4e99d55912ba6b35/library/core/src/slice/mod.rs#\x02\x10\x00M\x00\x00\x00\xe1\x05\x00\x00\x09\x00\x00\x00called `Option::unwrap()` on a `None` value\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x16\x00\x00\x00\x17\x00\x00\x00\x10\x00\x00\x00\x04\x00\x00\x00\x18\x00\x00\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x19\x00\x00\x00called `Result::unwrap()` on an `Err` value\x00\x1a\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00\x1b\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x1c\x00\x00\x00\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x1d\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00library/std/src/thread/mod.rsfailed to generate unique thread ID: bitspace exhausted@\x03\x10\x00\x1d\x00\x00\x00\xf6\x03\x00\x00\x11\x00\x00\x00@\x03\x10\x00\x1d\x00\x00\x00\xfc\x03\x00\x00*\x00\x00\x00thread name may not contain interior null bytes\x00@\x03\x10\x00\x1d\x00\x00\x006\x04\x00\x00*\x00\x00\x00\x00\x00\x00\x00\xc8\x01\x10\x00\x00\x00\x00\x00uncategorized errorother errorout of memoryunexpected end of fileunsupportedoperation interruptedargument list too longfilename too longtoo many linkscross-device link or renamedeadlockexecutable file busyresource busyfile too largefilesystem quota exceededseek on unseekable fileno storage spacewrite zerotimed outinvalid datainvalid input parameterstale network file handlefilesystem loop or indirection limit (e.g. symlink loop)read-only filesystem or storage mediumdirectory not emptyis a directorynot a directoryoperation would blockentity already existsbroken pipenetwork downaddress not availableaddress in usenot connectedconnection abortednetwork unreachablehost unreachableconnection resetconnection refusedpermission deniedentity not found (os error )\x00\x00\xc8\x01\x10\x00\x00\x00\x00\x00\xee\x06\x10\x00\x0b\x00\x00\x00\xf9\x06\x10\x00\x01\x00\x00\x00library/std/src/io/stdio.rs\x00\x14\x07\x10\x00\x1b\x00\x00\x00h\x03\x00\x00\x14\x00\x00\x00failed printing to : \x00\x00\x00@\x07\x10\x00\x13\x00\x00\x00S\x07\x10\x00\x02\x00\x00\x00\x14\x07\x10\x00\x1b\x00\x00\x00\xa9\x04\x00\x00\x09\x00\x00\x00stdoutformatter error\x00\x00\x00~\x07\x10\x00\x0f\x00\x00\x00\x1e\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00\x1f\x00\x00\x00 \x00\x00\x00!\x00\x00\x00\x1e\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00"\x00\x00\x00#\x00\x00\x00$\x00\x00\x00library/std/src/sync/once.rs\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00%\x00\x00\x00&\x00\x00\x00\xc8\x07\x10\x00\x1c\x00\x00\x00?\x01\x00\x001\x00\x00\x00assertion failed: state_and_queue & STATE_MASK == RUNNING\x00\x00\x00\xc8\x07\x10\x00\x1c\x00\x00\x00\xa9\x01\x00\x00\x15\x00\x00\x00Once instance has previously been poisoned\x00\x00\xc8\x07\x10\x00\x1c\x00\x00\x00\x88\x01\x00\x00\x15\x00\x00\x00\x02\x00\x00\x00\xc8\x07\x10\x00\x1c\x00\x00\x00\xef\x01\x00\x00\x09\x00\x00\x00\xc8\x07\x10\x00\x1c\x00\x00\x00\xfb\x01\x00\x005\x00\x00\x00PoisonErrorsupplied instant is later than selflibrary/std/src/time.rs\x00\x00\x00\xe2\x08\x10\x00\x17\x00\x00\x00$\x01\x00\x000\x00\x00\x00library/std/src/sys_common/thread_info.rs\x00\x00\x00\x0c\x09\x10\x00)\x00\x00\x00\x15\x00\x00\x00\x16\x00\x00\x00\x0c\x09\x10\x00)\x00\x00\x00\x16\x00\x00\x00\x18\x00\x00\x00\x0c\x09\x10\x00)\x00\x00\x00\x19\x00\x00\x00\x15\x00\x00\x00library/std/src/panicking.rsh\x09\x10\x00\x1c\x00\x00\x00\x03\x02\x00\x00\x1f\x00\x00\x00h\x09\x10\x00\x1c\x00\x00\x00\x04\x02\x00\x00\x1e\x00\x00\x00\'\x00\x00\x00\x10\x00\x00\x00\x04\x00\x00\x00(\x00\x00\x00)\x00\x00\x00\x0a\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00*\x00\x00\x00+\x00\x00\x00,\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00-\x00\x00\x00\x0a\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00.\x00\x00\x00\x0a\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00/\x00\x00\x000\x00\x00\x00NulError\x0a\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x001\x00\x00\x00library/std/src/sys_common/thread_parker/generic.rs\x00\x18\x0a\x10\x003\x00\x00\x00!\x00\x00\x00&\x00\x00\x00inconsistent park state\x00\x18\x0a\x10\x003\x00\x00\x00/\x00\x00\x00\x17\x00\x00\x00park state changed unexpectedly\x00\x84\x0a\x10\x00\x1f\x00\x00\x00\x18\x0a\x10\x003\x00\x00\x00,\x00\x00\x00\x11\x00\x00\x00inconsistent state in unpark\x18\x0a\x10\x003\x00\x00\x00f\x00\x00\x00\x12\x00\x00\x00\x18\x0a\x10\x003\x00\x00\x00t\x00\x00\x00\x1f\x00\x00\x00operation successfultime not implemented on this platformlibrary/std/src/sys/wasm/../unsupported/time.rs1\x0b\x10\x00/\x00\x00\x00\x0d\x00\x00\x00\x09\x00\x00\x00condvar wait not supportedlibrary/std/src/sys/wasm/../unsupported/condvar.rs\x8a\x0b\x10\x002\x00\x00\x00\x17\x00\x00\x00\x09\x00\x00\x00cannot recursively acquire mutex\xcc\x0b\x10\x00 \x00\x00\x00library/std/src/sys/wasm/../unsupported/mutex.rs\xf4\x0b\x10\x000\x00\x00\x00\x17\x00\x00\x00\x09\x00\x00\x00Hash table capacity overflow/cargo/registry/src/github.com-1ecc6299db9ec823/hashbrown-0.11.0/src/raw/mod.rs\x00P\x0c\x10\x00O\x00\x00\x00c\x00\x00\x00(\x00\x00\x00\xff\xff\xff\xfflibrary/alloc/src/raw_vec.rscapacity overflow\x00\x00\x00\xb4\x0c\x10\x00\x1c\x00\x00\x00/\x02\x00\x00\x05\x00\x00\x00assertion failed: edelta >= 0library/core/src/num/diy_float.rs\x00\x00\x11\x0d\x10\x00!\x00\x00\x00L\x00\x00\x00\x09\x00\x00\x00\x11\x0d\x10\x00!\x00\x00\x00N\x00\x00\x00\x09\x00\x00\x00\x01\x00\x00\x00\x0a\x00\x00\x00d\x00\x00\x00\xe8\x03\x00\x00\x10\'\x00\x00\xa0\x86\x01\x00@B\x0f\x00\x80\x96\x98\x00\x00\xe1\xf5\x05\x00\xca\x9a;\x02\x00\x00\x00\x14\x00\x00\x00\xc8\x00\x00\x00\xd0\x07\x00\x00 N\x00\x00@\x0d\x03\x00\x80\x84\x1e\x00\x00-1\x01\x00\xc2\xeb\x0b\x00\x945w\x00\x00\xc1o\xf2\x86#\x00\x00\x00\x00\x00\x81\xef\xac\x85[Am-\xee\x04');
    __MEMORY_INIT__(mem_0,1052100,'\x01\x1fj\xbfd\xed8n\xed\x97\xa7\xda\xf4\xf9?\xe9\x03O\x18');
    __MEMORY_INIT__(mem_0,1052136,'\x01>\x95.\x09\x99\xdf\x03\xfd8\x15\x0f/\xe4t#\xec\xf5\xcf\xd3\x08\xdc\x04\xc4\xda\xb0\xcd\xbc\x19\x7f3\xa6\x03&\x1f\xe9N\x02');
    __MEMORY_INIT__(mem_0,1052208,'\x01|.\x98[\x87\xd3\xber\x9f\xd9\xd8\x87/\x15\x12\xc6P\xdekpnJ\xcf\x0f\xd8\x95\xd5nq\xb2&\xb0f\xc6\xad$6\x15\x1dZ\xd3B<\x0eT\xffc\xc0sU\xcc\x17\xef\xf9e\xf2(\xbcU\xf7\xc7\xdc\x80\xdc\xedn\xf4\xce\xef\xdc_\xf7S\x05\x00library/core/src/num/flt2dec/strategy/dragon.rsassertion failed: d.mant > 0\x00|\x0e\x10\x00/\x00\x00\x00u\x00\x00\x00\x05\x00\x00\x00assertion failed: d.minus > 0\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00v\x00\x00\x00\x05\x00\x00\x00assertion failed: d.plus > 0|\x0e\x10\x00/\x00\x00\x00w\x00\x00\x00\x05\x00\x00\x00assertion failed: d.mant.checked_add(d.plus).is_some()\x00\x00|\x0e\x10\x00/\x00\x00\x00x\x00\x00\x00\x05\x00\x00\x00assertion failed: d.mant.checked_sub(d.minus).is_some()\x00|\x0e\x10\x00/\x00\x00\x00y\x00\x00\x00\x05\x00\x00\x00assertion failed: buf.len() >= MAX_SIG_DIGITS\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00z\x00\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\xc1\x00\x00\x00\x09\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\xf9\x00\x00\x00T\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\xfa\x00\x00\x00\x0d\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x01\x01\x00\x003\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x0a\x01\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x0b\x01\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x0c\x01\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x0d\x01\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x0e\x01\x00\x00\x05\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00K\x01\x00\x00\x1f\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00e\x01\x00\x00\x0d\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00q\x01\x00\x00&\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00v\x01\x00\x00T\x00\x00\x00|\x0e\x10\x00/\x00\x00\x00\x83\x01\x00\x003\x00\x00\x00\x00\x00\x00\x00\xdfE\x1a=\x03\xcf\x1a\xe6\xc1\xfb\xcc\xfe\x00\x00\x00\x00\xca\xc6\x9a\xc7\x17\xfep\xab\xdc\xfb\xd4\xfe\x00\x00\x00\x00O\xdc\xbc\xbe\xfc\xb1w\xff\xf6\xfb\xdc\xfe\x00\x00\x00\x00\x0c\xd6kA\xef\x91V\xbe\x11\xfc\xe4\xfe\x00\x00\x00\x00<\xfc\x7f\x90\xad\x1f\xd0\x8d,\xfc\xec\xfe\x00\x00\x00\x00\x83\x9aU1(\\Q\xd3F\xfc\xf4\xfe\x00\x00\x00\x00\xb5\xc9\xa6\xad\x8f\xacq\x9da\xfc\xfc\xfe\x00\x00\x00\x00\xcb\x8b\xee#w"\x9c\xea{\xfc\x04\xff\x00\x00\x00\x00mSx@\x91I\xcc\xae\x96\xfc\x0c\xff\x00\x00\x00\x00W\xce\xb6]y\x12<\x82\xb1\xfc\x14\xff\x00\x00\x00\x007V\xfbM6\x94\x10\xc2\xcb\xfc\x1c\xff\x00\x00\x00\x00O\x98H8o\xea\x96\x90\xe6\xfc$\xff\x00\x00\x00\x00\xc7:\x82%\xcb\x85t\xd7\x00\xfd,\xff\x00\x00\x00\x00\xf4\x97\xbf\x97\xcd\xcf\x86\xa0\x1b\xfd4\xff\x00\x00\x00\x00\xe5\xac*\x17\x98\x0a4\xef5\xfd<\xff\x00\x00\x00\x00\x8e\xb25*\xfbg8\xb2P\xfdD\xff\x00\x00\x00\x00;?\xc6\xd2\xdf\xd4\xc8\x84k\xfdL\xff\x00\x00\x00\x00\xba\xcd\xd3\x1a\'D\xdd\xc5\x85\xfdT\xff\x00\x00\x00\x00\x96\xc9%\xbb\xce\x9fk\x93\xa0\xfd\\\xff\x00\x00\x00\x00\x84\xa5b}$l\xac\xdb\xba\xfdd\xff\x00\x00\x00\x00\xf6\xda_\x0dXf\xab\xa3\xd5\xfdl\xff\x00\x00\x00\x00&\xf1\xc3\xde\x93\xf8\xe2\xf3\xef\xfdt\xff\x00\x00\x00\x00\xb8\x80\xff\xaa\xa8\xad\xb5\xb5\x0a\xfe|\xff\x00\x00\x00\x00\x8bJ|l\x05_b\x87%\xfe\x84\xff\x00\x00\x00\x00S0\xc14`\xff\xbc\xc9?\xfe\x8c\xff\x00\x00\x00\x00U&\xba\x91\x8c\x85N\x96Z\xfe\x94\xff\x00\x00\x00\x00\xbd~)p$w\xf9\xdft\xfe\x9c\xff\x00\x00\x00\x00\x8f\xb8\xe5\xb8\x9f\xbd\xdf\xa6\x8f\xfe\xa4\xff\x00\x00\x00\x00\x94}t\x88\xcf_\xa9\xf8\xa9\xfe\xac\xff\x00\x00\x00\x00\xcf\x9b\xa8\x8f\x93pD\xb9\xc4\xfe\xb4\xff\x00\x00\x00\x00k\x15\x0f\xbf\xf8\xf0\x08\x8a\xdf\xfe\xbc\xff\x00\x00\x00\x00\xb611eU%\xb0\xcd\xf9\xfe\xc4\xff\x00\x00\x00\x00\xac\x7f{\xd0\xc6\xe2?\x99\x14\xff\xcc\xff\x00\x00\x00\x00\x06;+*\xc4\x10\\\xe4.\xff\xd4\xff\x00\x00\x00\x00\xd3\x92si\x99$$\xaaI\xff\xdc\xff\x00\x00\x00\x00\x0e\xca\x00\x83\xf2\xb5\x87\xfdc\xff\xe4\xff\x00\x00\x00\x00\xeb\x1a\x11\x92d\x08\xe5\xbc~\xff\xec\xff\x00\x00\x00\x00\xcc\x88Po\x09\xcc\xbc\x8c\x99\xff\xf4\xff\x00\x00\x00\x00,e\x19\xe2X\x17\xb7\xd1\xb3\xff\xfc\xff');
    __MEMORY_INIT__(mem_0,1053534,'@\x9c\xce\xff\x04');
    __MEMORY_INIT__(mem_0,1053548,'\x10\xa5\xd4\xe8\xe8\xff\x0c\x00\x00\x00\x00\x00\x00\x00b\xac\xc5\xebx\xad\x03\x00\x14\x00\x00\x00\x00\x00\x84\x09\x94\xf8x9?\x81\x1e\x00\x1c\x00\x00\x00\x00\x00\xb3\x15\x07\xc9{\xce\x97\xc08\x00$\x00\x00\x00\x00\x00p\\\xea{\xce2~\x8fS\x00,\x00\x00\x00\x00\x00h\x80\xe9\xab\xa48\xd2\xd5m\x004\x00\x00\x00\x00\x00E"\x9a\x17&\'O\x9f\x88\x00<\x00\x00\x00\x00\x00\'\xfb\xc4\xd41\xa2c\xed\xa2\x00D\x00\x00\x00\x00\x00\xa8\xad\xc8\x8c8e\xde\xb0\xbd\x00L\x00\x00\x00\x00\x00\xdbe\xab\x1a\x8e\x08\xc7\x83\xd8\x00T\x00\x00\x00\x00\x00\x9a\x1dqB\xf9\x1d]\xc4\xf2\x00\\\x00\x00\x00\x00\x00X\xe7\x1b\xa6,iM\x92\x0d\x01d\x00\x00\x00\x00\x00\xea\x8dp\x1ad\xee\x01\xda\'\x01l\x00\x00\x00\x00\x00Jw\xef\x9a\x99\xa3m\xa2B\x01t\x00\x00\x00\x00\x00\x85k}\xb4{x\x09\xf2\\\x01|\x00\x00\x00\x00\x00w\x18\xddy\xa1\xe4T\xb4w\x01\x84\x00\x00\x00\x00\x00\xc2\xc5\x9b[\x92\x86[\x86\x92\x01\x8c\x00\x00\x00\x00\x00=]\x96\xc8\xc5S5\xc8\xac\x01\x94\x00\x00\x00\x00\x00\xb3\xa0\x97\xfa\\\xb4*\x95\xc7\x01\x9c\x00\x00\x00\x00\x00\xe3_\xa0\x99\xbd\x9fF\xde\xe1\x01\xa4\x00\x00\x00\x00\x00%\x8c9\xdb4\xc2\x9b\xa5\xfc\x01\xac\x00\x00\x00\x00\x00\\\x9f\x98\xa3r\x9a\xc6\xf6\x16\x02\xb4\x00\x00\x00\x00\x00\xce\xbe\xe9TS\xbf\xdc\xb71\x02\xbc\x00\x00\x00\x00\x00\xe2A"\xf2\x17\xf3\xfc\x88L\x02\xc4\x00\x00\x00\x00\x00\xa5x\\\xd3\x9b\xce \xccf\x02\xcc\x00\x00\x00\x00\x00\xdfS!{\xf3Z\x16\x98\x81\x02\xd4\x00\x00\x00\x00\x00:0\x1f\x97\xdc\xb5\xa0\xe2\x9b\x02\xdc\x00\x00\x00\x00\x00\x96\xb3\xe3\\S\xd1\xd9\xa8\xb6\x02\xe4\x00\x00\x00\x00\x00<D\xa7\xa4\xd9|\x9b\xfb\xd0\x02\xec\x00\x00\x00\x00\x00\x10D\xa4\xa7LLv\xbb\xeb\x02\xf4\x00\x00\x00\x00\x00\x1a\x9c@\xb6\xef\x8e\xab\x8b\x06\x03\xfc\x00\x00\x00\x00\x00,\x84W\xa6\x10\xef\x1f\xd0 \x03\x04\x01\x00\x00\x00\x00)1\x91\xe9\xe5\xa4\x10\x9b;\x03\x0c\x01\x00\x00\x00\x00\x9d\x0c\x9c\xa1\xfb\x9b\x10\xe7U\x03\x14\x01\x00\x00\x00\x00)\xf4;b\xd9 (\xacp\x03\x1c\x01\x00\x00\x00\x00\x85\xcf\xa7z^KD\x80\x8b\x03$\x01\x00\x00\x00\x00-\xdd\xac\x03@\xe4!\xbf\xa5\x03,\x01\x00\x00\x00\x00\x8f\xffD^/\x9cg\x8e\xc0\x034\x01\x00\x00\x00\x00A\xb8\x8c\x9c\x9d\x173\xd4\xda\x03<\x01\x00\x00\x00\x00\xa9\x1b\xe3\xb4\x92\xdb\x19\x9e\xf5\x03D\x01\x00\x00\x00\x00\xd9w\xdf\xban\xbf\x96\xeb\x0f\x04L\x01\x00\x00\x00\x00library/core/src/num/flt2dec/strategy/grisu.rs\x00\x00\xf8\x15\x10\x00.\x00\x00\x00}\x00\x00\x00\x15\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xa9\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xaa\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xab\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xac\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xad\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xae\x00\x00\x00\x05\x00\x00\x00assertion failed: d.mant + d.plus < (1 << 61)\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xaf\x00\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\x0b\x01\x00\x00\x11');
    __MEMORY_INIT__(mem_0,1054448,'attempt to divide by zero\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\x0e\x01\x00\x00\x09\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\x17\x01\x00\x00B\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00C\x01\x00\x00\x09\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00J\x01\x00\x00B\x00\x00\x00assertion failed: !buf.is_empty()\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xe0\x01\x00\x00\x05\x00\x00\x00assertion failed: d.mant < (1 << 61)\xf8\x15\x10\x00.\x00\x00\x00\xe1\x01\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xe2\x01\x00\x00\x05\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\'\x02\x00\x00\x11\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00*\x02\x00\x00\x09\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00`\x02\x00\x00\x09\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xc0\x02\x00\x00G\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xd7\x02\x00\x00K\x00\x00\x00\xf8\x15\x10\x00.\x00\x00\x00\xe3\x02\x00\x00G\x00\x00\x00library/core/src/num/flt2dec/mod.rs\x00$\x18\x10\x00#\x00\x00\x00\xbc\x00\x00\x00\x05\x00\x00\x00assertion failed: buf[0] > b\\\'0\\\'\x00\x00\x00$\x18\x10\x00#\x00\x00\x00\xbd\x00\x00\x00\x05\x00\x00\x00assertion failed: parts.len() >= 4\x00\x00$\x18\x10\x00#\x00\x00\x00\xbe\x00\x00\x00\x05\x00\x00\x000..-+\x00\x00\x000infNaNassertion failed: buf.len() >= maxlen$\x18\x10\x00#\x00\x00\x00\x7f\x02\x00\x00\x0d\x00\x00\x00..\x00\x00\x04\x19\x10\x00\x02\x00\x00\x00BorrowErrorBorrowMutErrorcalled `Option::unwrap()` on a `None` value\xc8\x18\x10\x00\x00\x00\x00\x009\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00:\x00\x00\x00index out of bounds: the len is  but the index is \x00\x00l\x19\x10\x00 \x00\x00\x00\x8c\x19\x10\x00\x12\x00\x00\x009\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00;\x00\x00\x00matches!===assertion failed: `(left  right)`\x0a  left: ``,\x0a right: ``: \x00\x00\x00\xcb\x19\x10\x00\x19\x00\x00\x00\xe4\x19\x10\x00\x12\x00\x00\x00\xf6\x19\x10\x00\x0c\x00\x00\x00\x02\x1a\x10\x00\x03\x00\x00\x00`\x00\x00\x00\xcb\x19\x10\x00\x19\x00\x00\x00\xe4\x19\x10\x00\x12\x00\x00\x00\xf6\x19\x10\x00\x0c\x00\x00\x00(\x1a\x10\x00\x01\x00\x00\x00: \x00\x00\xc8\x18\x10\x00\x00\x00\x00\x00L\x1a\x10\x00\x02\x00\x00\x009\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00<\x00\x00\x00=\x00\x00\x00>\x00\x00\x00    library/core/src/fmt/builders.rs|\x1a\x10\x00 \x00\x00\x00/\x00\x00\x00!\x00\x00\x00|\x1a\x10\x00 \x00\x00\x000\x00\x00\x00\x12\x00\x00\x00,\x0a, ..\x0a}, .. } { .. }(\x0a(,)\x0a[]library/core/src/fmt/num.rs\xd9\x1a\x10\x00\x1b\x00\x00\x00e\x00\x00\x00\x14\x00\x00\x000x00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899\x00\x009\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00?\x00\x00\x00@\x00\x00\x00A\x00\x00\x00library/core/src/fmt/mod.rs\x00\xe8\x1b\x10\x00\x1b\x00\x00\x00\x08\x06\x00\x00\x1e\x00\x00\x000000000000000000000000000000000000000000000000000000000000000000\xe8\x1b\x10\x00\x1b\x00\x00\x00\x02\x06\x00\x00-\x00\x00\x00truefalselibrary/core/src/slice/memchr.rs\x00\x00\x00m\x1c\x10\x00 \x00\x00\x00Z\x00\x00\x00\x05\x00\x00\x00m\x1c\x10\x00 \x00\x00\x00s\x00\x00\x00\x1a\x00\x00\x00m\x1c\x10\x00 \x00\x00\x00\x8f\x00\x00\x00\x05\x00\x00\x00range start index  out of range for slice of length \xc0\x1c\x10\x00\x12\x00\x00\x00\xd2\x1c\x10\x00"\x00\x00\x00range end index \x04\x1d\x10\x00\x10\x00\x00\x00\xd2\x1c\x10\x00"\x00\x00\x00slice index starts at  but ends at \x00$\x1d\x10\x00\x16\x00\x00\x00:\x1d\x10\x00\x0d\x00\x00\x00library/core/src/str/validations.rs\x00X\x1d\x10\x00#\x00\x00\x00\x11\x01\x00\x00\x11\x00\x00\x00[...]byte index  is out of bounds of `\x00\x00\x91\x1d\x10\x00\x0b\x00\x00\x00\x9c\x1d\x10\x00\x16\x00\x00\x00(\x1a\x10\x00\x01\x00\x00\x00begin <= end ( <= ) when slicing `\x00\x00\xcc\x1d\x10\x00\x0e\x00\x00\x00\xda\x1d\x10\x00\x04\x00\x00\x00\xde\x1d\x10\x00\x10\x00\x00\x00(\x1a\x10\x00\x01\x00\x00\x00 is not a char boundary; it is inside  (bytes ) of `\x91\x1d\x10\x00\x0b\x00\x00\x00\x10\x1e\x10\x00&\x00\x00\x006\x1e\x10\x00\x08\x00\x00\x00>\x1e\x10\x00\x06\x00\x00\x00(\x1a\x10\x00\x01\x00\x00\x00library/core/src/time.rsdivide by zero error when dividing duration by scalar\x00\x00\x00l\x1e\x10\x00\x18\x00\x00\x00\xdc\x03\x00\x00\x1f\x00\x00\x00\xc4\x18\x10\x00\x01\x00\x00\x00sms\xc2\xb5snsl\x1e\x10\x00\x18\x00\x00\x00/\x04\x00\x00#\x00\x00\x00l\x1e\x10\x00\x18\x00\x00\x00/\x04\x00\x00\x11\x00\x00\x00l\x1e\x10\x00\x18\x00\x00\x00d\x04\x00\x00C\x00\x00\x00\xc8\x18\x10\x00\x00\x00\x00\x00\xc2\x18\x10\x00\x01\x00\x00\x00\x00\x00\x00\x00 \x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x01\x00\x00\x000\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00library/core/src/unicode/printable.rs\x00\x00\x00\\\x1f\x10\x00%\x00\x00\x00\x0a\x00\x00\x00\x1c\x00\x00\x00\\\x1f\x10\x00%\x00\x00\x00\x1a\x00\x00\x006\x00\x00\x00\x00\x01\x03\x05\x05\x06\x06\x03\x07\x06\x08\x08\x09\x11\x0a\x1c\x0b\x19\x0c\x14\x0d\x10\x0e\x0d\x0f\x04\x10\x03\x12\x12\x13\x09\x16\x01\x17\x05\x18\x02\x19\x03\x1a\x07\x1c\x02\x1d\x01\x1f\x16 \x03+\x03,\x02-\x0b.\x010\x031\x022\x01\xa7\x02\xa9\x02\xaa\x04\xab\x08\xfa\x02\xfb\x05\xfd\x04\xfe\x03\xff\x09\xadxy\x8b\x8d\xa20WX\x8b\x8c\x90\x1c\x1d\xdd\x0e\x0fKL\xfb\xfc./?\\]_\xb5\xe2\x84\x8d\x8e\x91\x92\xa9\xb1\xba\xbb\xc5\xc6\xc9\xca\xde\xe4\xe5\xff\x00\x04\x11\x12)147:;=IJ]\x84\x8e\x92\xa9\xb1\xb4\xba\xbb\xc6\xca\xce\xcf\xe4\xe5\x00\x04\x0d\x0e\x11\x12)14:;EFIJ^de\x84\x91\x9b\x9d\xc9\xce\xcf\x0d\x11)EIWde\x8d\x91\xa9\xb4\xba\xbb\xc5\xc9\xdf\xe4\xe5\xf0\x0d\x11EIde\x80\x84\xb2\xbc\xbe\xbf\xd5\xd7\xf0\xf1\x83\x85\x8b\xa4\xa6\xbe\xbf\xc5\xc7\xce\xcf\xda\xdbH\x98\xbd\xcd\xc6\xce\xcfINOWY^_\x89\x8e\x8f\xb1\xb6\xb7\xbf\xc1\xc6\xc7\xd7\x11\x16\x17[\\\xf6\xf7\xfe\xff\x80\x0dmq\xde\xdf\x0e\x0f\x1fno\x1c\x1d_}~\xae\xaf\xbb\xbc\xfa\x16\x17\x1e\x1fFGNOXZ\\^~\x7f\xb5\xc5\xd4\xd5\xdc\xf0\xf1\xf5rs\x8ftu\x96/_&./\xa7\xaf\xb7\xbf\xc7\xcf\xd7\xdf\x9a@\x97\x980\x8f\x1f\xc0\xc1\xce\xffNOZ[\x07\x08\x0f\x10\'/\xee\xefno7=?BE\x90\x91\xfe\xffSgu\xc8\xc9\xd0\xd1\xd8\xd9\xe7\xfe\xff\x00 _"\x82\xdf\x04\x82D\x08\x1b\x04\x06\x11\x81\xac\x0e\x80\xab5(\x0b\x80\xe0\x03\x19\x08\x01\x04/\x044\x04\x07\x03\x01\x07\x06\x07\x11\x0aP\x0f\x12\x07U\x07\x03\x04\x1c\x0a\x09\x03\x08\x03\x07\x03\x02\x03\x03\x03\x0c\x04\x05\x03\x0b\x06\x01\x0e\x15\x05:\x03\x11\x07\x06\x05\x10\x07W\x07\x02\x07\x15\x0dP\x04C\x03-\x03\x01\x04\x11\x06\x0f\x0c:\x04\x1d%_ m\x04j%\x80\xc8\x05\x82\xb0\x03\x1a\x06\x82\xfd\x03Y\x07\x15\x0b\x17\x09\x14\x0c\x14\x0cj\x06\x0a\x06\x1a\x06Y\x07+\x05F\x0a,\x04\x0c\x04\x01\x031\x0b,\x04\x1a\x06\x0b\x03\x80\xac\x06\x0a\x06!?L\x04-\x03t\x08<\x03\x0f\x03<\x078\x08+\x05\x82\xff\x11\x18\x08/\x11-\x03 \x10!\x0f\x80\x8c\x04\x82\x97\x19\x0b\x15\x88\x94\x05/\x05;\x07\x02\x0e\x18\x09\x80\xb3-t\x0c\x80\xd6\x1a\x0c\x05\x80\xff\x05\x80\xdf\x0c\xee\x0d\x03\x84\x8d\x037\x09\x81\\\x14\x80\xb8\x08\x80\xcb*8\x03\x0a\x068\x08F\x08\x0c\x06t\x0b\x1e\x03Z\x04Y\x09\x80\x83\x18\x1c\x0a\x16\x09L\x04\x80\x8a\x06\xab\xa4\x0c\x17\x041\xa1\x04\x81\xda&\x07\x0c\x05\x05\x80\xa5\x11\x81m\x10x(*\x06L\x04\x80\x8d\x04\x80\xbe\x03\x1b\x03\x0f\x0d\x00\x06\x01\x01\x03\x01\x04\x02\x08\x08\x09\x02\x0a\x05\x0b\x02\x0e\x04\x10\x01\x11\x02\x12\x05\x13\x11\x14\x01\x15\x02\x17\x02\x19\x0d\x1c\x05\x1d\x08$\x01j\x03k\x02\xbc\x02\xd1\x02\xd4\x0c\xd5\x09\xd6\x02\xd7\x02\xda\x01\xe0\x05\xe1\x02\xe8\x02\xee \xf0\x04\xf8\x02\xf9\x02\xfa\x02\xfb\x01\x0c\';>NO\x8f\x9e\x9e\x9f\x06\x07\x096=>V\xf3\xd0\xd1\x04\x14\x1867VW\x7f\xaa\xae\xaf\xbd5\xe0\x12\x87\x89\x8e\x9e\x04\x0d\x0e\x11\x12)14:EFIJNOde\\\xb6\xb7\x1b\x1c\x07\x08\x0a\x0b\x14\x1769:\xa8\xa9\xd8\xd9\x097\x90\x91\xa8\x07\x0a;>fi\x8f\x92o_\xee\xefZb\x9a\x9b\'(U\x9d\xa0\xa1\xa3\xa4\xa7\xa8\xad\xba\xbc\xc4\x06\x0b\x0c\x15\x1d:?EQ\xa6\xa7\xcc\xcd\xa0\x07\x19\x1a"%>?\xc5\xc6\x04 #%&(38:HJLPSUVXZ\\^`cefksx}\x7f\x8a\xa4\xaa\xaf\xb0\xc0\xd0\xae\xafy\xccno\x93^"{\x05\x03\x04-\x03f\x03\x01/.\x80\x82\x1d\x031\x0f\x1c\x04$\x09\x1e\x05+\x05D\x04\x0e*\x80\xaa\x06$\x04$\x04(\x084\x0b\x01\x80\x90\x817\x09\x16\x0a\x08\x80\x989\x03c\x08\x090\x16\x05!\x03\x1b\x05\x01@8\x04K\x05/\x04\x0a\x07\x09\x07@ \'\x04\x0c\x096\x03:\x05\x1a\x07\x04\x0c\x07PI73\x0d3\x07.\x08\x0a\x81&RN(\x08*V\x1c\x14\x17\x09N\x04\x1e\x0fC\x0e\x19\x07\x0a\x06H\x08\'\x09u\x0b?A*\x06;\x05\x0a\x06Q\x06\x01\x05\x10\x03\x05\x80\x8bb\x1eH\x08\x0a\x80\xa6^"E\x0b\x0a\x06\x0d\x139\x07\x0a6,\x04\x10\x80\xc0<dS\x0cH\x09\x0aFE\x1bH\x08S\x1d9\x81\x07F\x0a\x1d\x03GI7\x03\x0e\x08\x0a\x069\x07\x0a\x816\x19\x80\xb7\x01\x0f2\x0d\x83\x9bfu\x0b\x80\xc4\x8a\xbc\x84/\x8f\xd1\x82G\xa1\xb9\x829\x07*\x04\x02`&\x0aF\x0a(\x05\x13\x82\xb0[eK\x049\x07\x11@\x05\x0b\x02\x0e\x97\xf8\x08\x84\xd6*\x09\xa2\xf7\x81\x1f1\x03\x11\x04\x08\x81\x8c\x89\x04k\x05\x0d\x03\x09\x07\x10\x93`\x80\xf6\x0as\x08n\x17F\x80\x9a\x14\x0cW\x09\x19\x80\x87\x81G\x03\x85B\x0f\x15\x85P+\x80\xd5-\x03\x1a\x04\x02\x81p:\x05\x01\x85\x00\x80\xd7)L\x04\x0a\x04\x02\x83\x11DL=\x80\xc2<\x06\x01\x04U\x05\x1b4\x02\x81\x0e,\x04d\x0cV\x0a\x80\xae8\x1d\x0d,\x04\x09\x07\x02\x0e\x06\x80\x9a\x83\xd8\x08\x0d\x03\x0d\x03t\x0cY\x07\x0c\x14\x0c\x048\x08\x0a\x06(\x08"N\x81T\x0c\x15\x03\x03\x05\x07\x09\x19\x07\x07\x09\x03\x0d\x07)\x80\xcb%\x0a\x84\x06library/core/src/unicode/unicode_data.rs\x00\xeb$\x10\x00(\x00\x00\x00K\x00\x00\x00(\x00\x00\x00\xeb$\x10\x00(\x00\x00\x00W\x00\x00\x00\x16\x00\x00\x00\xeb$\x10\x00(\x00\x00\x00R\x00\x00\x00>\x00\x00\x00library/core/src/num/bignum.rs\x00\x00D%\x10\x00\x1e\x00\x00\x00\xd5\x01\x00\x00\x01\x00\x00\x00assertion failed: noborrowassertion failed: digits < 40assertion failed: other > 0\x00\x00\x00\x03\x00\x00\x83\x04 \x00\x91\x05`\x00]\x13\xa0\x00\x12\x17\xa0\x1e\x0c \xe0\x1e\xef, +*0\xa0+o\xa6`,\x02\xa8\xe0,\x1e\xfb\xe0-\x00\xfe\xa05\x9e\xff\xe05\xfd\x01a6\x01\x0a\xa16$\x0da7\xab\x0e\xe18/\x18!90\x1caF\xf3\x1e\xa1J\xf0jaNOo\xa1N\x9d\xbc!Oe\xd1\xe1O\x00\xda!P\x00\xe0\xe1Q0\xe1aS\xec\xe2\xa1T\xd0\xe8\xe1T \x00.U\xf0\x01\xbfU\x00p\x00\x07\x00-\x01\x01\x01\x02\x01\x02\x01\x01H\x0b0\x15\x10\x01e\x07\x02\x06\x02\x02\x01\x04#\x01\x1e\x1b[\x0b:\x09\x09\x01\x18\x04\x01\x09\x01\x03\x01\x05+\x03w\x0f\x01 7\x01\x01\x01\x04\x08\x04\x01\x03\x07\x0a\x02\x1d\x01:\x01\x01\x01\x02\x04\x08\x01\x09\x01\x0a\x02\x1a\x01\x02\x029\x01\x04\x02\x04\x02\x02\x03\x03\x01\x1e\x02\x03\x01\x0b\x029\x01\x04\x05\x01\x02\x04\x01\x14\x02\x16\x06\x01\x01:\x01\x01\x02\x01\x04\x08\x01\x07\x03\x0a\x02\x1e\x01;\x01\x01\x01\x0c\x01\x09\x01(\x01\x03\x019\x03\x05\x03\x01\x04\x07\x02\x0b\x02\x1d\x01:\x01\x02\x01\x02\x01\x03\x01\x05\x02\x07\x02\x0b\x02\x1c\x029\x02\x01\x01\x02\x04\x08\x01\x09\x01\x0a\x02\x1d\x01H\x01\x04\x01\x02\x03\x01\x01\x08\x01Q\x01\x02\x07\x0c\x08b\x01\x02\x09\x0b\x06J\x02\x1b\x01\x01\x01\x01\x017\x0e\x01\x05\x01\x02\x05\x0b\x01$\x09\x01f\x04\x01\x06\x01\x02\x02\x02\x19\x02\x04\x03\x10\x04\x0d\x01\x02\x02\x06\x01\x0f\x01\x00\x03\x00\x03\x1d\x03\x1d\x02\x1e\x02@\x02\x01\x07\x08\x01\x02\x0b\x09\x01-\x03w\x02"\x01v\x03\x04\x02\x09\x01\x06\x03\xdb\x02\x02\x01:\x01\x01\x07\x01\x01\x01\x01\x02\x08\x06\x0a\x02\x010\x11?\x040\x07\x01\x01\x05\x01(\x09\x0c\x02 \x04\x02\x02\x01\x038\x01\x01\x02\x03\x01\x01\x03:\x08\x02\x02\x98\x03\x01\x0d\x01\x07\x04\x01\x06\x01\x03\x02\xc6:\x01\x05\x00\x01\xc3!\x00\x03\x8d\x01` \x00\x06i\x02\x00\x04\x01\x0a \x02P\x02\x00\x01\x03\x01\x04\x01\x19\x02\x05\x01\x97\x02\x1a\x12\x0d\x01&\x08\x19\x0b.\x030\x01\x02\x04\x02\x02\'\x01C\x06\x02\x02\x02\x02\x0c\x01\x08\x01/\x013\x01\x01\x03\x02\x02\x05\x02\x01\x01*\x02\x08\x01\xee\x01\x02\x01\x04\x01\x00\x01\x00\x10\x10\x10\x00\x02\x00\x01\xe2\x01\x95\x05\x00\x03\x01\x02\x05\x04(\x03\x04\x01\xa5\x02\x00\x04\x00\x02\x99\x0b\xb0\x016\x0f8\x031\x04\x02\x02E\x03$\x05\x01\x08>\x01\x0c\x024\x09\x0a\x04\x02\x01_\x03\x02\x01\x01\x02\x06\x01\xa0\x01\x03\x08\x15\x029\x02\x01\x01\x01\x01\x16\x01\x0e\x07\x03\x05\xc3\x08\x02\x03\x01\x01\x17\x01Q\x01\x02\x06\x01\x01\x02\x01\x01\x02\x01\x02\xeb\x01\x02\x04\x06\x02\x01\x02\x1b\x02U\x08\x02\x01\x01\x02j\x01\x01\x01\x02\x06\x01\x01e\x03\x02\x04\x01\x05\x00\x09\x01\x02\xf5\x01\x0a\x02\x01\x01\x04\x01\x90\x04\x02\x02\x04\x01 \x0a(\x06\x02\x04\x08\x01\x09\x06\x02\x03.\x0d\x01\x02\x00\x07\x01\x06\x01\x01R\x16\x02\x07\x01\x02\x01\x02z\x06\x03\x01\x01\x02\x01\x07\x01\x01H\x02\x03\x01\x01\x01\x00\x02\x00\x05;\x07\x00\x01?\x04Q\x01\x00\x02\x00\x01\x01\x03\x04\x05\x08\x08\x02\x07\x1e\x04\x94\x03\x007\x042\x08\x01\x0e\x01\x16\x05\x01\x0f\x00\x07\x01\x11\x02\x07\x01\x02\x01\x05\x00\x07\x00\x04\x00\x07m\x07\x00`\x80\xf0');
    __MEMORY_INIT__(mem_0,1059064,'\x01');
    function __FUNCS__.func_0(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19,reg20,reg21,reg22,reg23,reg24,reg25,reg26,reg27,reg28,reg29,reg30,reg31,reg32,reg33,reg34,reg35,reg36,reg37,reg38,reg39,reg40,reg41;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 1344));
        __GLOBALS__[0] = reg4;
        
            
                
                    
                        
                            
                                
                                    
                                        
                                            
                                                
                                                    
                                                        
                                                            
                                                                
                                                                    
                                                                        
                                                                            
                                                                                
                                                                                    
                                                                                        reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1);
                                                                                        reg5 = reg3;
                                                                                        if (((((reg5)[1] == 0) and ((reg5)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_33_fin end 
                                                                                            reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1+8);
                                                                                            reg6 = reg3;
                                                                                            if (((reg6)[1] == 0) and ((reg6)[2] == 0) and 1 or 0)~=0 then goto block_27_fin; end;
                                                                                            reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1+16);
                                                                                            reg7 = reg3;
                                                                                            if (((reg7)[1] == 0) and ((reg7)[2] == 0) and 1 or 0)~=0 then goto block_26_fin; end;
                                                                                            reg3 = (reg5 + reg7);
                                                                                            if ((reg3):_lt_u(reg5) and 1 or 0)~=0 then goto block_25_fin; end;
                                                                                            if (((reg5 - reg6)):_gt_u(reg5) and 1 or 0)~=0 then goto block_24_fin; end;
                                                                                            reg8 = __MEMORY_READ_8__(mem_0,reg1+26);reg8=bit_arshift(bit_lshift(reg8,24),24);
                                                                                            reg9 = reg8;
                                                                                            reg8 = __MEMORY_READ_16__(mem_0,reg1+24);
                                                                                            reg1 = reg8;
                                                                                            (reg5):store32(mem_0,reg4+4);
                                                                                            reg8 = ((reg5):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 8)),((reg8 == 0) and ((((reg5):_shr_u(__LONG_INT__(32,0))))[1]) or 0));
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4,((reg8 == 0) and 2 or 1));
                                                                                            reg10 = __FUNCS__.func_65((bit_tobit(reg4 + 12)),0,152);
                                                                                            (reg6):store32(mem_0,reg4+172);
                                                                                            reg8 = ((reg6):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 176)),((reg8 == 0) and ((((reg6):_shr_u(__LONG_INT__(32,0))))[1]) or 0));
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4+168,((reg8 == 0) and 2 or 1));
                                                                                            reg6 = __FUNCS__.func_65((bit_tobit(reg4 + 180)),0,152);
                                                                                            (reg7):store32(mem_0,reg4+340);
                                                                                            reg8 = ((reg7):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 344)),((reg8 == 0) and ((((reg7):_shr_u(__LONG_INT__(32,0))))[1]) or 0));
                                                                                            
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4+336,((reg8 == 0) and 2 or 1));
                                                                                            reg6 = __FUNCS__.func_65((bit_tobit(reg4 + 348)),0,152);
                                                                                            reg6 = __FUNCS__.func_65((bit_tobit(reg4 + 512)),0,156);
                                                                                            (__LONG_INT__(1,1)):store(mem_0,reg4+504);
                                                                                            reg8 = ((((((((((((__LONG_INT__(reg1,0))):_shl(__LONG_INT__(48,0)))):_shr_s(__LONG_INT__(48,0))) - ((reg3 + __LONG_INT__(-1,-1)):_clz())) * __LONG_INT__(1292913986,0)) + __LONG_INT__(1142116480,19))):_shr_u(__LONG_INT__(32,0))))[1]);
                                                                                            reg3 = (bit_arshift((bit_lshift(reg8,16)),16));
                                                                                            
                                                                                                reg6 = (bit_arshift((bit_lshift(reg1,16)),16));
                                                                                                if ((reg6 >= 0) and 1 or 0)==0 then goto if_196_fin end 
                                                                                                    reg7 = __FUNCS__.func_6(reg4,reg1);
                                                                                                    reg7 = __FUNCS__.func_6((bit_tobit(reg4 + 168)),reg1);
                                                                                                    reg7 = __FUNCS__.func_6((bit_tobit(reg4 + 336)),reg1);
                                                                                                    goto block_187_fin;
                                                                                                ::if_196_fin::
                                                                                                reg7 = __FUNCS__.func_6((bit_tobit(reg4 + 504)),(bit_arshift((bit_lshift((bit_tobit(0 - reg6)),16)),16)));
                                                                                            ::block_187_fin::
                                                                                            
                                                                                                if ((reg3 <= -1) and 1 or 0)==0 then goto if_232_fin end 
                                                                                                    reg1 = (bit_arshift((bit_lshift((bit_tobit(0 - reg3)),16)),16));
                                                                                                    __FUNCS__.func_15(reg4,reg1);
                                                                                                    __FUNCS__.func_15((bit_tobit(reg4 + 168)),reg1);
                                                                                                    __FUNCS__.func_15((bit_tobit(reg4 + 336)),reg1);
                                                                                                    goto block_228_fin;
                                                                                                ::if_232_fin::
                                                                                                __FUNCS__.func_15((bit_tobit(reg4 + 504)),(bit_band(reg8,65535)));
                                                                                            ::block_228_fin::
                                                                                            reg7 = __MEMORY_READ_32__(mem_0,reg4);
                                                                                            reg10 = reg7;
                                                                                            reg7 = (bit_bor(reg4,4));
                                                                                            reg11 = __FUNCS__.func_64((bit_bor((bit_tobit(reg4 + 1176)),4)),reg7,160);
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4+1176,reg10);
                                                                                            
                                                                                                
                                                                                                    
                                                                                                        reg11 = __MEMORY_READ_32__(mem_0,reg4+336);
                                                                                                        reg12 = reg11;
                                                                                                        
                                                                                                        reg11 = ((((__UNSIGNED__(reg10) > __UNSIGNED__(reg12)) and 1 or 0) == 0) and reg12 or reg10);
                                                                                                        if ((__UNSIGNED__(reg11) <= __UNSIGNED__(40)) and 1 or 0)==0 then goto if_295_fin end 
                                                                                                            if ((reg11 == 0) and 1 or 0)==0 then goto if_298_fin end 
                                                                                                                reg11 = 0;
                                                                                                                goto block_281_fin;
                                                                                                            ::if_298_fin::
                                                                                                            reg13 = (bit_band(reg11,1));
                                                                                                            if ((reg11 ~= 1) and 1 or 0)~=0 then goto block_283_fin; end;
                                                                                                            goto block_282_fin;
                                                                                                        ::if_295_fin::
                                                                                                        goto block_12_fin;
                                                                                                    ::block_283_fin::
                                                                                                    reg14 = (bit_band(reg11,-2));
                                                                                                    reg8 = (bit_tobit(reg4 + 344));
                                                                                                    reg1 = (bit_tobit(reg4 + 1184));
                                                                                                    -- FORCE INIT VAR | i32
                                                                                                    reg15 = 0;
                                                                                                    -- FORCE INIT VAR | i32
                                                                                                    reg16 = 0;
                                                                                                    
                                                                                                    while true do ::loop_327_start::
                                                                                                        reg6 = (bit_tobit(reg1 + -4));
                                                                                                        reg17 = __MEMORY_READ_32__(mem_0,reg6);
                                                                                                        reg18 = reg17;
                                                                                                        reg17 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                        reg19 = reg6;
                                                                                                        reg6 = (bit_tobit(reg18 + reg17));
                                                                                                        reg17 = (bit_tobit(reg6 + reg15));
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg19,reg17);
                                                                                                        reg19 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                        reg20 = reg19;
                                                                                                        reg19 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                        reg21 = (bit_tobit(reg20 + reg19));
                                                                                                        reg19 = bit_tobit(reg21 + (bit_bor(((__UNSIGNED__(reg6) < __UNSIGNED__(reg18)) and 1 or 0),((__UNSIGNED__(reg17) < __UNSIGNED__(reg6)) and 1 or 0))));
                                                                                                        reg6 = reg19;
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg1,reg6);
                                                                                                        reg15 = (bit_bor(((__UNSIGNED__(reg21) < __UNSIGNED__(reg20)) and 1 or 0),((__UNSIGNED__(reg6) < __UNSIGNED__(reg21)) and 1 or 0)));
                                                                                                        reg19 = bit_tobit(reg8 + 8);
                                                                                                        reg8 = reg19;
                                                                                                        reg19 = bit_tobit(reg1 + 8);
                                                                                                        reg1 = reg19;
                                                                                                        reg19 = bit_tobit(reg16 + 2);
                                                                                                        reg16 = reg19;
                                                                                                        if ((reg14 ~= reg16) and 1 or 0)~=0 then goto loop_327_start; end;
                                                                                                        break
                                                                                                    end
                                                                                                    
                                                                                                ::block_282_fin::
                                                                                                if reg13==0 then goto if_389_else end 
                                                                                                    reg1 = (bit_lshift(reg16,2));
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 1180));
                                                                                                    reg22 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg23 = reg8;
                                                                                                    reg8 = reg22;
                                                                                                    reg22 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg4)) + 340)));
                                                                                                    reg1 = (bit_tobit(reg8 + reg22));
                                                                                                    reg6 = (bit_tobit(reg1 + reg15));
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg23,reg6);
                                                                                                    reg19 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg6) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                                goto if_389_fin
                                                                                                ::if_389_else::
                                                                                                    reg19 = reg15
                                                                                                    -- BLOCK RET (if):
                                                                                                ::if_389_fin::
                                                                                                if ((reg19 == 0) and 1 or 0)~=0 then goto block_281_fin; end;
                                                                                                if ((__UNSIGNED__(reg11) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_23_fin; end;
                                                                                                __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit((bit_lshift(reg11,2)) + reg4)) + 1180)),1);
                                                                                                reg19 = bit_tobit(reg11 + 1);
                                                                                                reg11 = reg19;
                                                                                            ::block_281_fin::
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4+1176,reg11);
                                                                                            reg19 = __MEMORY_READ_32__(mem_0,reg4+504);
                                                                                            reg18 = reg19;
                                                                                            
                                                                                            reg1 = ((((__UNSIGNED__(reg18) > __UNSIGNED__(reg11)) and 1 or 0) == 0) and reg11 or reg18);
                                                                                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                                                                            reg21 = (bit_bor((bit_tobit(reg4 + 336)),4));
                                                                                            reg13 = (bit_bor((bit_tobit(reg4 + 168)),4));
                                                                                            reg14 = (bit_bor(reg4,4));
                                                                                            reg19 = bit_lshift(reg1,2);
                                                                                            reg1 = reg19;
                                                                                            
                                                                                            while true do ::loop_478_start::
                                                                                                
                                                                                                    if ((reg1 == 0) and 1 or 0)==0 then goto if_482_fin end 
                                                                                                        
                                                                                                        reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                        goto block_479_fin;
                                                                                                    ::if_482_fin::
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + 1176)) + reg1));
                                                                                                    reg6 = (bit_tobit((bit_tobit(reg4 + 504)) + reg1));
                                                                                                    reg19 = bit_tobit(reg1 + -4);
                                                                                                    reg1 = reg19;
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg6);
                                                                                                    reg6 = reg19;
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg8 = reg19;
                                                                                                    
                                                                                                    reg19 = (((__UNSIGNED__(reg6) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg6 ~= reg8) and 1 or 0) or -1;
                                                                                                    reg8 = reg19;
                                                                                                    if ((reg8 == 0) and 1 or 0)~=0 then goto loop_478_start; end;
                                                                                                ::block_479_fin::
                                                                                                break
                                                                                            end
                                                                                            
                                                                                            if ((reg8 >= reg9) and 1 or 0)==0 then goto if_526_fin end 
                                                                                                if ((__UNSIGNED__(reg10) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_10_fin; end;
                                                                                                if ((reg10 == 0) and 1 or 0)==0 then goto if_533_fin end 
                                                                                                    reg10 = 0;
                                                                                                    goto block_21_fin;
                                                                                                ::if_533_fin::
                                                                                                reg11 = (bit_lshift(reg10,2));
                                                                                                reg1 = (bit_tobit(reg11 + -4));
                                                                                                reg8 = (bit_tobit((bit_rshift(reg1,2)) + 1));
                                                                                                reg6 = (bit_band(reg8,3));
                                                                                                if ((__UNSIGNED__(reg1) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_556_fin end 
                                                                                                    reg5 = __LONG_INT__(0,0);
                                                                                                    reg1 = reg14;
                                                                                                    goto block_22_fin;
                                                                                                ::if_556_fin::
                                                                                                reg19 = bit_tobit(0 - (bit_band(reg8,2147483644)));
                                                                                                reg8 = reg19;
                                                                                                reg5 = __LONG_INT__(0,0);
                                                                                                reg1 = reg14;
                                                                                                
                                                                                                while true do ::loop_573_start::
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                                                                    reg5 = reg22;
                                                                                                    (reg5):store32(mem_0,reg1);
                                                                                                    reg17 = (bit_tobit(reg1 + 4));
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                    reg5 = reg22;
                                                                                                    (reg5):store32(mem_0,reg17);
                                                                                                    reg17 = (bit_tobit(reg1 + 8));
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                    reg5 = reg22;
                                                                                                    (reg5):store32(mem_0,reg17);
                                                                                                    reg17 = (bit_tobit(reg1 + 12));
                                                                                                    reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                    reg5 = reg22;
                                                                                                    (reg5):store32(mem_0,reg17);
                                                                                                    reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                    reg5 = reg19;
                                                                                                    reg19 = bit_tobit(reg1 + 16);
                                                                                                    reg1 = reg19;
                                                                                                    reg19 = bit_tobit(reg8 + 4);
                                                                                                    reg8 = reg19;
                                                                                                    if reg8~=0 then goto loop_573_start; end;
                                                                                                    break
                                                                                                end
                                                                                                
                                                                                                goto block_22_fin;
                                                                                            ::if_526_fin::
                                                                                            reg19 = bit_tobit(reg3 + 1);
                                                                                            reg3 = reg19;
                                                                                            goto block_15_fin;
                                                                                        ::if_33_fin::
                                                                                        __FUNCS__.func_110(1052331,28,1052360);
                                                                                        error('unreachable');
                                                                                    ::block_27_fin::
                                                                                    __FUNCS__.func_110(1052376,29,1052408);
                                                                                    error('unreachable');
                                                                                ::block_26_fin::
                                                                                __FUNCS__.func_110(1052424,28,1052452);
                                                                                error('unreachable');
                                                                            ::block_25_fin::
                                                                            __FUNCS__.func_110(1052468,54,1052524);
                                                                            error('unreachable');
                                                                        ::block_24_fin::
                                                                        __FUNCS__.func_110(1052540,55,1052596);
                                                                        error('unreachable');
                                                                    ::block_23_fin::
                                                                    __FUNCS__.func_82(reg11,40,1058148);
                                                                    error('unreachable');
                                                                ::block_22_fin::
                                                                if reg6==0 then goto if_684_fin end 
                                                                    reg8 = (bit_tobit(0 - reg6));
                                                                    
                                                                    while true do ::loop_689_start::
                                                                        reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                                        reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                                        reg5 = reg22;
                                                                        (reg5):store32(mem_0,reg1);
                                                                        reg19 = bit_tobit(reg1 + 4);
                                                                        reg1 = reg19;
                                                                        reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                        reg5 = reg19;
                                                                        reg6 = (bit_tobit(reg8 + 1));
                                                                        reg19 = (__UNSIGNED__(reg6) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                                        reg8 = reg6;
                                                                        if reg19~=0 then goto loop_689_start; end;
                                                                        break
                                                                    end
                                                                    
                                                                ::if_684_fin::
                                                                reg1 = ((reg5)[1]);
                                                                if ((reg1 == 0) and 1 or 0)~=0 then goto block_21_fin; end;
                                                                if ((__UNSIGNED__(reg10) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_20_fin; end;
                                                                __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg11)) + 4)),reg1);
                                                                reg19 = bit_tobit(reg10 + 1);
                                                                reg10 = reg19;
                                                            ::block_21_fin::
                                                            __MEMORY_WRITE_32__(mem_0,reg4,reg10);
                                                            reg19 = __MEMORY_READ_32__(mem_0,reg4+168);
                                                            reg10 = reg19;
                                                            if ((__UNSIGNED__(reg10) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_10_fin; end;
                                                            if ((reg10 == 0) and 1 or 0)==0 then goto if_750_fin end 
                                                                reg10 = 0;
                                                                goto block_18_fin;
                                                            ::if_750_fin::
                                                            reg11 = (bit_lshift(reg10,2));
                                                            reg1 = (bit_tobit(reg11 + -4));
                                                            reg8 = (bit_tobit((bit_rshift(reg1,2)) + 1));
                                                            reg6 = (bit_band(reg8,3));
                                                            if ((__UNSIGNED__(reg1) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_773_fin end 
                                                                reg5 = __LONG_INT__(0,0);
                                                                reg1 = reg13;
                                                                goto block_19_fin;
                                                            ::if_773_fin::
                                                            reg19 = bit_tobit(0 - (bit_band(reg8,2147483644)));
                                                            reg8 = reg19;
                                                            reg5 = __LONG_INT__(0,0);
                                                            reg1 = reg13;
                                                            
                                                            while true do ::loop_790_start::
                                                                reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                                reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                                reg5 = reg22;
                                                                (reg5):store32(mem_0,reg1);
                                                                reg17 = (bit_tobit(reg1 + 4));
                                                                reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                reg5 = reg22;
                                                                (reg5):store32(mem_0,reg17);
                                                                reg17 = (bit_tobit(reg1 + 8));
                                                                reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                reg5 = reg22;
                                                                (reg5):store32(mem_0,reg17);
                                                                reg17 = (bit_tobit(reg1 + 12));
                                                                reg19 = __MEMORY_READ_32__(mem_0,reg17);reg19=__LONG_INT__(reg19,0);
                                                                reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                reg5 = reg22;
                                                                (reg5):store32(mem_0,reg17);
                                                                reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                reg5 = reg19;
                                                                reg19 = bit_tobit(reg1 + 16);
                                                                reg1 = reg19;
                                                                reg19 = bit_tobit(reg8 + 4);
                                                                reg8 = reg19;
                                                                if reg8~=0 then goto loop_790_start; end;
                                                                break
                                                            end
                                                            
                                                            goto block_19_fin;
                                                        ::block_20_fin::
                                                        __FUNCS__.func_82(reg10,40,1058148);
                                                        error('unreachable');
                                                    ::block_19_fin::
                                                    if reg6==0 then goto if_865_fin end 
                                                        reg8 = (bit_tobit(0 - reg6));
                                                        
                                                        while true do ::loop_870_start::
                                                            reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                            reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                            reg5 = reg22;
                                                            (reg5):store32(mem_0,reg1);
                                                            reg19 = bit_tobit(reg1 + 4);
                                                            reg1 = reg19;
                                                            reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                            reg5 = reg19;
                                                            reg6 = (bit_tobit(reg8 + 1));
                                                            reg19 = (__UNSIGNED__(reg6) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                            reg8 = reg6;
                                                            if reg19~=0 then goto loop_870_start; end;
                                                            break
                                                        end
                                                        
                                                    ::if_865_fin::
                                                    reg1 = ((reg5)[1]);
                                                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_18_fin; end;
                                                    if ((__UNSIGNED__(reg10) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_17_fin; end;
                                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg11)) + 172)),reg1);
                                                    reg19 = bit_tobit(reg10 + 1);
                                                    reg10 = reg19;
                                                ::block_18_fin::
                                                __MEMORY_WRITE_32__(mem_0,reg4+168,reg10);
                                                if ((__UNSIGNED__(reg12) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_8_fin; end;
                                                if ((reg12 == 0) and 1 or 0)==0 then goto if_929_fin end 
                                                    __MEMORY_WRITE_32__(mem_0,reg4+336,0);
                                                    goto block_15_fin;
                                                ::if_929_fin::
                                                reg10 = (bit_lshift(reg12,2));
                                                reg1 = (bit_tobit(reg10 + -4));
                                                reg8 = (bit_tobit((bit_rshift(reg1,2)) + 1));
                                                reg6 = (bit_band(reg8,3));
                                                if ((__UNSIGNED__(reg1) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_953_fin end 
                                                    reg5 = __LONG_INT__(0,0);
                                                    reg1 = reg21;
                                                    goto block_16_fin;
                                                ::if_953_fin::
                                                reg19 = bit_tobit(0 - (bit_band(reg8,2147483644)));
                                                reg8 = reg19;
                                                reg5 = __LONG_INT__(0,0);
                                                reg1 = reg21;
                                                
                                                while true do ::loop_970_start::
                                                    reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                    reg5 = reg22;
                                                    (reg5):store32(mem_0,reg1);
                                                    reg11 = (bit_tobit(reg1 + 4));
                                                    reg19 = __MEMORY_READ_32__(mem_0,reg11);reg19=__LONG_INT__(reg19,0);
                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                    reg5 = reg22;
                                                    (reg5):store32(mem_0,reg11);
                                                    reg11 = (bit_tobit(reg1 + 8));
                                                    reg19 = __MEMORY_READ_32__(mem_0,reg11);reg19=__LONG_INT__(reg19,0);
                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                    reg5 = reg22;
                                                    (reg5):store32(mem_0,reg11);
                                                    reg11 = (bit_tobit(reg1 + 12));
                                                    reg19 = __MEMORY_READ_32__(mem_0,reg11);reg19=__LONG_INT__(reg19,0);
                                                    reg22 = (reg19 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                    reg5 = reg22;
                                                    (reg5):store32(mem_0,reg11);
                                                    reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                    reg5 = reg19;
                                                    reg19 = bit_tobit(reg1 + 16);
                                                    reg1 = reg19;
                                                    reg19 = bit_tobit(reg8 + 4);
                                                    reg8 = reg19;
                                                    if reg8~=0 then goto loop_970_start; end;
                                                    break
                                                end
                                                
                                                goto block_16_fin;
                                            ::block_17_fin::
                                            __FUNCS__.func_82(reg10,40,1058148);
                                            error('unreachable');
                                        ::block_16_fin::
                                        if reg6==0 then goto if_1045_fin end 
                                            reg8 = (bit_tobit(0 - reg6));
                                            
                                            while true do ::loop_1050_start::
                                                reg19 = __MEMORY_READ_32__(mem_0,reg1);reg19=__LONG_INT__(reg19,0);
                                                reg22 = (reg19 * __LONG_INT__(10,0)) + reg5;
                                                reg5 = reg22;
                                                (reg5):store32(mem_0,reg1);
                                                reg19 = bit_tobit(reg1 + 4);
                                                reg1 = reg19;
                                                reg19 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                reg5 = reg19;
                                                reg6 = (bit_tobit(reg8 + 1));
                                                reg19 = (__UNSIGNED__(reg6) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                reg8 = reg6;
                                                if reg19~=0 then goto loop_1050_start; end;
                                                break
                                            end
                                            
                                        ::if_1045_fin::
                                        reg1 = ((reg5)[1]);
                                        if reg1==0 then goto if_1083_else end 
                                            if ((__UNSIGNED__(reg12) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_14_fin; end;
                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg10)) + 340)),reg1);
                                            reg19 = (bit_tobit(reg12 + 1))
                                        goto if_1083_fin
                                        ::if_1083_else::
                                            reg19 = reg12
                                            -- BLOCK RET (if):
                                        ::if_1083_fin::
                                        __MEMORY_WRITE_32__(mem_0,reg4+336,reg19);
                                    ::block_15_fin::
                                    reg1 = (bit_bor((bit_tobit(reg4 + 504)),4));
                                    reg19 = __FUNCS__.func_64((bit_bor((bit_tobit(reg4 + 672)),4)),reg1,160);
                                    __MEMORY_WRITE_32__(mem_0,reg4+672,reg18);
                                    reg19 = __FUNCS__.func_6((bit_tobit(reg4 + 672)),1);
                                    reg22 = reg19;
                                    reg19 = __MEMORY_READ_32__(mem_0,reg4+504);
                                    reg8 = reg19;
                                    reg19 = __FUNCS__.func_64((bit_bor((bit_tobit(reg4 + 840)),4)),reg1,160);
                                    __MEMORY_WRITE_32__(mem_0,reg4+840,reg8);
                                    reg19 = __FUNCS__.func_6((bit_tobit(reg4 + 840)),2);
                                    reg23 = reg19;
                                    reg19 = __MEMORY_READ_32__(mem_0,reg4+504);
                                    reg8 = reg19;
                                    reg19 = __FUNCS__.func_64((bit_bor((bit_tobit(reg4 + 1008)),4)),reg1,160);
                                    __MEMORY_WRITE_32__(mem_0,reg4+1008,reg8);
                                    reg19 = __FUNCS__.func_6((bit_tobit(reg4 + 1008)),3);
                                    reg24 = reg19;
                                    
                                        
                                            
                                                
                                                    
                                                        
                                                            
                                                                
                                                                    
                                                                        
                                                                            reg19 = __MEMORY_READ_32__(mem_0,reg4);
                                                                            reg12 = reg19;
                                                                            reg19 = __MEMORY_READ_32__(mem_0,reg4+1008);
                                                                            reg25 = reg19;
                                                                            
                                                                            reg11 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg25)) and 1 or 0) == 0) and reg25 or reg12);
                                                                            if ((__UNSIGNED__(reg11) <= __UNSIGNED__(40)) and 1 or 0)==0 then goto if_1190_fin end 
                                                                                reg19 = (bit_bor((bit_tobit(reg4 + 1176)),4));
                                                                                reg26 = __MEMORY_READ_32__(mem_0,reg4+504);
                                                                                reg27 = reg26;
                                                                                reg26 = __MEMORY_READ_32__(mem_0,reg4+672);
                                                                                reg28 = reg26;
                                                                                reg26 = __MEMORY_READ_32__(mem_0,reg4+840);
                                                                                reg29 = reg26;
                                                                                reg17 = (bit_tobit(reg4 + 344));
                                                                                reg20 = (bit_tobit(reg4 + 1184));
                                                                                reg26 = (bit_tobit(reg4 + 512));
                                                                                reg30 = (bit_tobit(reg4 + 680));
                                                                                reg31 = (bit_tobit(reg4 + 848));
                                                                                reg32 = (bit_tobit(reg4 + 1016));
                                                                                reg6 = (bit_tobit(reg4 + 8));
                                                                                reg10 = 0;
                                                                                
                                                                                while true do ::loop_1236_start::
                                                                                    reg18 = reg10;
                                                                                    reg1 = (bit_lshift(reg11,2));
                                                                                    
                                                                                    while true do ::loop_1243_start::
                                                                                        
                                                                                            if ((reg1 == 0) and 1 or 0)==0 then goto if_1247_fin end 
                                                                                                
                                                                                                reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                goto block_1244_fin;
                                                                                            ::if_1247_fin::
                                                                                            reg8 = (bit_tobit((bit_tobit(reg4 + 1008)) + reg1));
                                                                                            reg10 = (bit_tobit(reg1 + reg4));
                                                                                            reg33 = bit_tobit(reg1 + -4);
                                                                                            reg1 = reg33;
                                                                                            reg33 = __MEMORY_READ_32__(mem_0,reg10);
                                                                                            reg10 = reg33;
                                                                                            reg33 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                            reg8 = reg33;
                                                                                            
                                                                                            reg33 = (((__UNSIGNED__(reg10) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg10 ~= reg8) and 1 or 0) or -1;
                                                                                            reg8 = reg33;
                                                                                            if ((reg8 == 0) and 1 or 0)~=0 then goto loop_1243_start; end;
                                                                                        ::block_1244_fin::
                                                                                        break
                                                                                    end
                                                                                    
                                                                                    reg33 = 0;
                                                                                    
                                                                                        if ((__UNSIGNED__((bit_band(reg8,255))) >= __UNSIGNED__(2)) and 1 or 0)~=0 then goto block_1288_fin; end;
                                                                                        
                                                                                            if reg11==0 then goto if_1297_fin end 
                                                                                                reg15 = 1;
                                                                                                reg16 = 0;
                                                                                                if ((reg11 ~= 1) and 1 or 0)==0 then goto if_1305_fin end 
                                                                                                    reg33 = (bit_band(reg11,-2));
                                                                                                    reg8 = reg32;
                                                                                                    reg1 = reg6;
                                                                                                    
                                                                                                    while true do ::loop_1314_start::
                                                                                                        reg10 = (bit_tobit(reg1 + -4));
                                                                                                        reg34 = __MEMORY_READ_32__(mem_0,reg10);
                                                                                                        reg35 = reg15;
                                                                                                        reg15 = reg34;
                                                                                                        reg34 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                        reg36 = reg10;
                                                                                                        reg10 = (bit_tobit(reg15 + (bit_bxor(reg34,-1))));
                                                                                                        reg34 = (bit_tobit(reg35 + reg10));
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg36,reg34);
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                        reg36 = reg35;
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                        reg12 = (bit_tobit(reg36 + (bit_bxor(reg35,-1))));
                                                                                                        reg35 = bit_tobit(reg12 + (bit_bor(((__UNSIGNED__(reg10) < __UNSIGNED__(reg15)) and 1 or 0),((__UNSIGNED__(reg34) < __UNSIGNED__(reg10)) and 1 or 0))));
                                                                                                        reg10 = reg35;
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg1,reg10);
                                                                                                        reg15 = (bit_bor(((__UNSIGNED__(reg12) < __UNSIGNED__(reg36)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg12)) and 1 or 0)));
                                                                                                        reg35 = bit_tobit(reg8 + 8);
                                                                                                        reg8 = reg35;
                                                                                                        reg35 = bit_tobit(reg1 + 8);
                                                                                                        reg1 = reg35;
                                                                                                        reg35 = bit_tobit(reg16 + 2);
                                                                                                        reg16 = reg35;
                                                                                                        if ((reg33 ~= reg16) and 1 or 0)~=0 then goto loop_1314_start; end;
                                                                                                        break
                                                                                                    end
                                                                                                    
                                                                                                ::if_1305_fin::
                                                                                                if (bit_band(reg11,1))==0 then goto if_1382_else end 
                                                                                                    reg1 = (bit_lshift(reg16,2));
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 4));
                                                                                                    reg37 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg38 = reg8;
                                                                                                    reg8 = reg37;
                                                                                                    reg37 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg24)) + 4)));
                                                                                                    reg1 = (bit_tobit(reg8 + (bit_bxor(reg37,-1))));
                                                                                                    reg10 = (bit_tobit(reg1 + reg15));
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg38,reg10);
                                                                                                    reg35 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                                goto if_1382_fin
                                                                                                ::if_1382_else::
                                                                                                    reg35 = reg15
                                                                                                    -- BLOCK RET (if):
                                                                                                ::if_1382_fin::
                                                                                                if ((reg35 == 0) and 1 or 0)~=0 then goto block_1295_fin; end;
                                                                                            ::if_1297_fin::
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4,reg11);
                                                                                            reg33 = 8;
                                                                                            reg12 = reg11;
                                                                                            goto block_1288_fin;
                                                                                        ::block_1295_fin::
                                                                                        goto block_9_fin;
                                                                                    ::block_1288_fin::
                                                                                    
                                                                                        
                                                                                        reg11 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg29)) and 1 or 0) == 0) and reg29 or reg12);
                                                                                        if ((__UNSIGNED__(reg11) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_1442_fin end 
                                                                                            reg1 = (bit_lshift(reg11,2));
                                                                                            
                                                                                            while true do ::loop_1447_start::
                                                                                                
                                                                                                    if ((reg1 == 0) and 1 or 0)==0 then goto if_1451_fin end 
                                                                                                        
                                                                                                        reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                        goto block_1448_fin;
                                                                                                    ::if_1451_fin::
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + 840)) + reg1));
                                                                                                    reg10 = (bit_tobit(reg1 + reg4));
                                                                                                    reg35 = bit_tobit(reg1 + -4);
                                                                                                    reg1 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg10);
                                                                                                    reg10 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg8 = reg35;
                                                                                                    
                                                                                                    reg35 = (((__UNSIGNED__(reg10) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg10 ~= reg8) and 1 or 0) or -1;
                                                                                                    reg8 = reg35;
                                                                                                    if ((reg8 == 0) and 1 or 0)~=0 then goto loop_1447_start; end;
                                                                                                ::block_1448_fin::
                                                                                                break
                                                                                            end
                                                                                            
                                                                                            if ((__UNSIGNED__((bit_band(reg8,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1495_fin end 
                                                                                                reg11 = reg12;
                                                                                                goto block_1432_fin;
                                                                                            ::if_1495_fin::
                                                                                            if reg11==0 then goto if_1501_fin end 
                                                                                                reg15 = 1;
                                                                                                reg16 = 0;
                                                                                                if ((reg11 ~= 1) and 1 or 0)==0 then goto if_1509_fin end 
                                                                                                    reg34 = (bit_band(reg11,-2));
                                                                                                    reg8 = reg31;
                                                                                                    reg1 = reg6;
                                                                                                    
                                                                                                    while true do ::loop_1518_start::
                                                                                                        reg10 = (bit_tobit(reg1 + -4));
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg10);
                                                                                                        reg37 = reg15;
                                                                                                        reg15 = reg35;
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                        reg38 = reg10;
                                                                                                        reg10 = (bit_tobit(reg15 + (bit_bxor(reg35,-1))));
                                                                                                        reg36 = (bit_tobit(reg37 + reg10));
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg38,reg36);
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                        reg37 = reg35;
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                        reg12 = (bit_tobit(reg37 + (bit_bxor(reg35,-1))));
                                                                                                        reg35 = bit_tobit(reg12 + (bit_bor(((__UNSIGNED__(reg10) < __UNSIGNED__(reg15)) and 1 or 0),((__UNSIGNED__(reg36) < __UNSIGNED__(reg10)) and 1 or 0))));
                                                                                                        reg10 = reg35;
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg1,reg10);
                                                                                                        reg15 = (bit_bor(((__UNSIGNED__(reg12) < __UNSIGNED__(reg37)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg12)) and 1 or 0)));
                                                                                                        reg35 = bit_tobit(reg8 + 8);
                                                                                                        reg8 = reg35;
                                                                                                        reg35 = bit_tobit(reg1 + 8);
                                                                                                        reg1 = reg35;
                                                                                                        reg35 = bit_tobit(reg16 + 2);
                                                                                                        reg16 = reg35;
                                                                                                        if ((reg34 ~= reg16) and 1 or 0)~=0 then goto loop_1518_start; end;
                                                                                                        break
                                                                                                    end
                                                                                                    
                                                                                                ::if_1509_fin::
                                                                                                if (bit_band(reg11,1))==0 then goto if_1586_else end 
                                                                                                    reg1 = (bit_lshift(reg16,2));
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 4));
                                                                                                    reg38 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg39 = reg8;
                                                                                                    reg8 = reg38;
                                                                                                    reg38 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg23)) + 4)));
                                                                                                    reg1 = (bit_tobit(reg8 + (bit_bxor(reg38,-1))));
                                                                                                    reg10 = (bit_tobit(reg1 + reg15));
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg39,reg10);
                                                                                                    reg35 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                                goto if_1586_fin
                                                                                                ::if_1586_else::
                                                                                                    reg35 = reg15
                                                                                                    -- BLOCK RET (if):
                                                                                                ::if_1586_fin::
                                                                                                if ((reg35 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                                                            ::if_1501_fin::
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4,reg11);
                                                                                            reg35 = bit_bor(reg33,4);
                                                                                            reg33 = reg35;
                                                                                            goto block_1432_fin;
                                                                                        ::if_1442_fin::
                                                                                        goto block_12_fin;
                                                                                    ::block_1432_fin::
                                                                                    
                                                                                        
                                                                                        reg10 = ((((__UNSIGNED__(reg11) > __UNSIGNED__(reg28)) and 1 or 0) == 0) and reg28 or reg11);
                                                                                        if ((__UNSIGNED__(reg10) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_1646_fin end 
                                                                                            reg1 = (bit_lshift(reg10,2));
                                                                                            
                                                                                            while true do ::loop_1651_start::
                                                                                                
                                                                                                    if ((reg1 == 0) and 1 or 0)==0 then goto if_1655_fin end 
                                                                                                        
                                                                                                        reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                        goto block_1652_fin;
                                                                                                    ::if_1655_fin::
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + 672)) + reg1));
                                                                                                    reg12 = (bit_tobit(reg1 + reg4));
                                                                                                    reg35 = bit_tobit(reg1 + -4);
                                                                                                    reg1 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg12);
                                                                                                    reg12 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg8 = reg35;
                                                                                                    
                                                                                                    reg35 = (((__UNSIGNED__(reg12) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg12 ~= reg8) and 1 or 0) or -1;
                                                                                                    reg8 = reg35;
                                                                                                    if ((reg8 == 0) and 1 or 0)~=0 then goto loop_1651_start; end;
                                                                                                ::block_1652_fin::
                                                                                                break
                                                                                            end
                                                                                            
                                                                                            if ((__UNSIGNED__((bit_band(reg8,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1699_fin end 
                                                                                                reg10 = reg11;
                                                                                                goto block_1636_fin;
                                                                                            ::if_1699_fin::
                                                                                            if reg10==0 then goto if_1705_fin end 
                                                                                                reg15 = 1;
                                                                                                reg16 = 0;
                                                                                                if ((reg10 ~= 1) and 1 or 0)==0 then goto if_1713_fin end 
                                                                                                    reg34 = (bit_band(reg10,-2));
                                                                                                    reg8 = reg30;
                                                                                                    reg1 = reg6;
                                                                                                    
                                                                                                    while true do ::loop_1722_start::
                                                                                                        reg11 = (bit_tobit(reg1 + -4));
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                                        reg38 = reg15;
                                                                                                        reg15 = reg35;
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                        reg39 = reg11;
                                                                                                        reg11 = (bit_tobit(reg15 + (bit_bxor(reg35,-1))));
                                                                                                        reg36 = (bit_tobit(reg38 + reg11));
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg39,reg36);
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                        reg37 = reg35;
                                                                                                        reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                        reg12 = (bit_tobit(reg37 + (bit_bxor(reg35,-1))));
                                                                                                        reg35 = bit_tobit(reg12 + (bit_bor(((__UNSIGNED__(reg11) < __UNSIGNED__(reg15)) and 1 or 0),((__UNSIGNED__(reg36) < __UNSIGNED__(reg11)) and 1 or 0))));
                                                                                                        reg11 = reg35;
                                                                                                        __MEMORY_WRITE_32__(mem_0,reg1,reg11);
                                                                                                        reg15 = (bit_bor(((__UNSIGNED__(reg12) < __UNSIGNED__(reg37)) and 1 or 0),((__UNSIGNED__(reg11) < __UNSIGNED__(reg12)) and 1 or 0)));
                                                                                                        reg35 = bit_tobit(reg8 + 8);
                                                                                                        reg8 = reg35;
                                                                                                        reg35 = bit_tobit(reg1 + 8);
                                                                                                        reg1 = reg35;
                                                                                                        reg35 = bit_tobit(reg16 + 2);
                                                                                                        reg16 = reg35;
                                                                                                        if ((reg34 ~= reg16) and 1 or 0)~=0 then goto loop_1722_start; end;
                                                                                                        break
                                                                                                    end
                                                                                                    
                                                                                                ::if_1713_fin::
                                                                                                if (bit_band(reg10,1))==0 then goto if_1790_else end 
                                                                                                    reg1 = (bit_lshift(reg16,2));
                                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 4));
                                                                                                    reg38 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg39 = reg8;
                                                                                                    reg8 = reg38;
                                                                                                    reg38 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg22)) + 4)));
                                                                                                    reg1 = (bit_tobit(reg8 + (bit_bxor(reg38,-1))));
                                                                                                    reg11 = (bit_tobit(reg1 + reg15));
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg39,reg11);
                                                                                                    reg35 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg11) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                                goto if_1790_fin
                                                                                                ::if_1790_else::
                                                                                                    reg35 = reg15
                                                                                                    -- BLOCK RET (if):
                                                                                                ::if_1790_fin::
                                                                                                if ((reg35 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                                                            ::if_1705_fin::
                                                                                            __MEMORY_WRITE_32__(mem_0,reg4,reg10);
                                                                                            reg35 = bit_tobit(reg33 + 2);
                                                                                            reg33 = reg35;
                                                                                            goto block_1636_fin;
                                                                                        ::if_1646_fin::
                                                                                        goto block_10_fin;
                                                                                    ::block_1636_fin::
                                                                                    
                                                                                    reg12 = ((((__UNSIGNED__(reg10) > __UNSIGNED__(reg27)) and 1 or 0) == 0) and reg27 or reg10);
                                                                                    if ((__UNSIGNED__(reg12) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_8_fin; end;
                                                                                    reg1 = (bit_lshift(reg12,2));
                                                                                    
                                                                                    while true do ::loop_1854_start::
                                                                                        
                                                                                            if ((reg1 == 0) and 1 or 0)==0 then goto if_1858_fin end 
                                                                                                
                                                                                                reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                goto block_1855_fin;
                                                                                            ::if_1858_fin::
                                                                                            reg8 = (bit_tobit((bit_tobit(reg4 + 504)) + reg1));
                                                                                            reg11 = (bit_tobit(reg1 + reg4));
                                                                                            reg35 = bit_tobit(reg1 + -4);
                                                                                            reg1 = reg35;
                                                                                            reg35 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                            reg11 = reg35;
                                                                                            reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                            reg8 = reg35;
                                                                                            
                                                                                            reg35 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg11 ~= reg8) and 1 or 0) or -1;
                                                                                            reg8 = reg35;
                                                                                            if ((reg8 == 0) and 1 or 0)~=0 then goto loop_1854_start; end;
                                                                                        ::block_1855_fin::
                                                                                        break
                                                                                    end
                                                                                    
                                                                                    
                                                                                        if ((__UNSIGNED__((bit_band(reg8,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1903_fin end 
                                                                                            reg12 = reg10;
                                                                                            goto block_1897_fin;
                                                                                        ::if_1903_fin::
                                                                                        if reg12==0 then goto if_1909_fin end 
                                                                                            reg15 = 1;
                                                                                            reg16 = 0;
                                                                                            if ((reg12 ~= 1) and 1 or 0)==0 then goto if_1917_fin end 
                                                                                                reg34 = (bit_band(reg12,-2));
                                                                                                reg8 = reg26;
                                                                                                reg1 = reg6;
                                                                                                
                                                                                                while true do ::loop_1926_start::
                                                                                                    reg10 = (bit_tobit(reg1 + -4));
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg10);
                                                                                                    reg38 = reg15;
                                                                                                    reg15 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                    reg39 = reg10;
                                                                                                    reg10 = (bit_tobit(reg15 + (bit_bxor(reg35,-1))));
                                                                                                    reg36 = (bit_tobit(reg38 + reg10));
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg39,reg36);
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                    reg37 = reg35;
                                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                    reg11 = (bit_tobit(reg37 + (bit_bxor(reg35,-1))));
                                                                                                    reg35 = bit_tobit(reg11 + (bit_bor(((__UNSIGNED__(reg10) < __UNSIGNED__(reg15)) and 1 or 0),((__UNSIGNED__(reg36) < __UNSIGNED__(reg10)) and 1 or 0))));
                                                                                                    reg10 = reg35;
                                                                                                    __MEMORY_WRITE_32__(mem_0,reg1,reg10);
                                                                                                    reg15 = (bit_bor(((__UNSIGNED__(reg11) < __UNSIGNED__(reg37)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg11)) and 1 or 0)));
                                                                                                    reg35 = bit_tobit(reg8 + 8);
                                                                                                    reg8 = reg35;
                                                                                                    reg35 = bit_tobit(reg1 + 8);
                                                                                                    reg1 = reg35;
                                                                                                    reg35 = bit_tobit(reg16 + 2);
                                                                                                    reg16 = reg35;
                                                                                                    if ((reg34 ~= reg16) and 1 or 0)~=0 then goto loop_1926_start; end;
                                                                                                    break
                                                                                                end
                                                                                                
                                                                                            ::if_1917_fin::
                                                                                            if (bit_band(reg12,1))==0 then goto if_1994_else end 
                                                                                                reg1 = (bit_lshift(reg16,2));
                                                                                                reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 4));
                                                                                                reg38 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                reg39 = reg8;
                                                                                                reg8 = reg38;
                                                                                                reg38 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg4)) + 508)));
                                                                                                reg1 = (bit_tobit(reg8 + (bit_bxor(reg38,-1))));
                                                                                                reg10 = (bit_tobit(reg1 + reg15));
                                                                                                __MEMORY_WRITE_32__(mem_0,reg39,reg10);
                                                                                                reg35 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                            goto if_1994_fin
                                                                                            ::if_1994_else::
                                                                                                reg35 = reg15
                                                                                                -- BLOCK RET (if):
                                                                                            ::if_1994_fin::
                                                                                            if ((reg35 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                                                        ::if_1909_fin::
                                                                                        __MEMORY_WRITE_32__(mem_0,reg4,reg12);
                                                                                        reg35 = bit_tobit(reg33 + 1);
                                                                                        reg33 = reg35;
                                                                                    ::block_1897_fin::
                                                                                    if ((reg18 == 17) and 1 or 0)~=0 then goto block_1173_fin; end;
                                                                                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg18)),(bit_tobit(reg33 + 48)));
                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg4+168);
                                                                                    reg34 = reg35;
                                                                                    
                                                                                    reg1 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg34)) and 1 or 0) == 0) and reg34 or reg12);
                                                                                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                                                                    reg10 = (bit_tobit(reg18 + 1));
                                                                                    reg35 = bit_lshift(reg1,2);
                                                                                    reg1 = reg35;
                                                                                    
                                                                                    while true do ::loop_2072_start::
                                                                                        
                                                                                            if ((reg1 == 0) and 1 or 0)==0 then goto if_2076_fin end 
                                                                                                
                                                                                                reg11 = ((reg1 == 0) and 0 or -1);
                                                                                                goto block_2073_fin;
                                                                                            ::if_2076_fin::
                                                                                            reg8 = (bit_tobit((bit_tobit(reg4 + 168)) + reg1));
                                                                                            reg11 = (bit_tobit(reg1 + reg4));
                                                                                            reg35 = bit_tobit(reg1 + -4);
                                                                                            reg1 = reg35;
                                                                                            reg35 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                            reg11 = reg35;
                                                                                            reg35 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                            reg8 = reg35;
                                                                                            
                                                                                            reg35 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg11 ~= reg8) and 1 or 0) or -1;
                                                                                            reg11 = reg35;
                                                                                            if ((reg11 == 0) and 1 or 0)~=0 then goto loop_2072_start; end;
                                                                                        ::block_2073_fin::
                                                                                        break
                                                                                    end
                                                                                    
                                                                                    reg35 = __FUNCS__.func_64(reg19,reg7,160);
                                                                                    __MEMORY_WRITE_32__(mem_0,reg4+1176,reg12);
                                                                                    reg35 = __MEMORY_READ_32__(mem_0,reg4+336);
                                                                                    reg36 = reg35;
                                                                                    
                                                                                    reg33 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg36)) and 1 or 0) == 0) and reg36 or reg12);
                                                                                    if ((__UNSIGNED__(reg33) > __UNSIGNED__(40)) and 1 or 0)~=0 then goto block_1175_fin; end;
                                                                                    
                                                                                        if ((reg33 == 0) and 1 or 0)==0 then goto if_2138_fin end 
                                                                                            reg33 = 0;
                                                                                            goto block_2135_fin;
                                                                                        ::if_2138_fin::
                                                                                        reg15 = 0;
                                                                                        reg16 = 0;
                                                                                        if ((reg33 ~= 1) and 1 or 0)==0 then goto if_2150_fin end 
                                                                                            reg35 = (bit_band(reg33,-2));
                                                                                            reg8 = reg17;
                                                                                            reg1 = reg20;
                                                                                            
                                                                                            while true do ::loop_2159_start::
                                                                                                reg37 = (bit_tobit(reg1 + -4));
                                                                                                reg38 = __MEMORY_READ_32__(mem_0,reg37);
                                                                                                reg39 = reg38;
                                                                                                reg38 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + -4)));
                                                                                                reg40 = reg37;
                                                                                                reg37 = (bit_tobit(reg39 + reg38));
                                                                                                reg38 = (bit_tobit(reg15 + reg37));
                                                                                                __MEMORY_WRITE_32__(mem_0,reg40,reg38);
                                                                                                reg40 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                                reg41 = reg40;
                                                                                                reg40 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                                reg15 = (bit_tobit(reg41 + reg40));
                                                                                                reg40 = bit_tobit(reg15 + (bit_bor(((__UNSIGNED__(reg37) < __UNSIGNED__(reg39)) and 1 or 0),((__UNSIGNED__(reg38) < __UNSIGNED__(reg37)) and 1 or 0))));
                                                                                                reg37 = reg40;
                                                                                                __MEMORY_WRITE_32__(mem_0,reg1,reg37);
                                                                                                reg38 = bit_bor(((__UNSIGNED__(reg15) < __UNSIGNED__(reg41)) and 1 or 0),((__UNSIGNED__(reg37) < __UNSIGNED__(reg15)) and 1 or 0));
                                                                                                reg15 = reg38;
                                                                                                reg37 = bit_tobit(reg8 + 8);
                                                                                                reg8 = reg37;
                                                                                                reg37 = bit_tobit(reg1 + 8);
                                                                                                reg1 = reg37;
                                                                                                reg37 = bit_tobit(reg16 + 2);
                                                                                                reg16 = reg37;
                                                                                                if ((reg35 ~= reg16) and 1 or 0)~=0 then goto loop_2159_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2150_fin::
                                                                                        if (bit_band(reg33,1))==0 then goto if_2223_else end 
                                                                                            reg1 = (bit_lshift(reg16,2));
                                                                                            reg8 = (bit_tobit((bit_tobit(reg4 + reg1)) + 1180));
                                                                                            reg38 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                            reg39 = reg8;
                                                                                            reg8 = reg38;
                                                                                            reg38 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg4)) + 340)));
                                                                                            reg1 = (bit_tobit(reg8 + reg38));
                                                                                            reg38 = bit_tobit(reg1 + reg15);
                                                                                            reg15 = reg38;
                                                                                            __MEMORY_WRITE_32__(mem_0,reg39,reg15);
                                                                                            reg37 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg8)) and 1 or 0),((__UNSIGNED__(reg15) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                                        goto if_2223_fin
                                                                                        ::if_2223_else::
                                                                                            reg37 = reg15
                                                                                            -- BLOCK RET (if):
                                                                                        ::if_2223_fin::
                                                                                        if ((reg37 == 0) and 1 or 0)~=0 then goto block_2135_fin; end;
                                                                                        if ((__UNSIGNED__(reg33) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_1174_fin; end;
                                                                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit((bit_lshift(reg33,2)) + reg4)) + 1180)),1);
                                                                                        reg37 = bit_tobit(reg33 + 1);
                                                                                        reg33 = reg37;
                                                                                    ::block_2135_fin::
                                                                                    __MEMORY_WRITE_32__(mem_0,reg4+1176,reg33);
                                                                                    
                                                                                    reg1 = ((((__UNSIGNED__(reg27) > __UNSIGNED__(reg33)) and 1 or 0) == 0) and reg33 or reg27);
                                                                                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                                                                    reg37 = bit_lshift(reg1,2);
                                                                                    reg1 = reg37;
                                                                                    
                                                                                    while true do ::loop_2294_start::
                                                                                        
                                                                                            if ((reg1 == 0) and 1 or 0)==0 then goto if_2298_fin end 
                                                                                                
                                                                                                reg8 = ((reg1 == 0) and 0 or -1);
                                                                                                goto block_2295_fin;
                                                                                            ::if_2298_fin::
                                                                                            reg8 = (bit_tobit((bit_tobit(reg4 + 1176)) + reg1));
                                                                                            reg15 = (bit_tobit((bit_tobit(reg4 + 504)) + reg1));
                                                                                            reg37 = bit_tobit(reg1 + -4);
                                                                                            reg1 = reg37;
                                                                                            reg37 = __MEMORY_READ_32__(mem_0,reg15);
                                                                                            reg15 = reg37;
                                                                                            reg37 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                            reg8 = reg37;
                                                                                            
                                                                                            reg37 = (((__UNSIGNED__(reg15) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg15 ~= reg8) and 1 or 0) or -1;
                                                                                            reg8 = reg37;
                                                                                            if ((reg8 == 0) and 1 or 0)~=0 then goto loop_2294_start; end;
                                                                                        ::block_2295_fin::
                                                                                        break
                                                                                    end
                                                                                    
                                                                                    if (bit_bor(((reg11 < reg9) and 1 or 0),((reg8 < reg9) and 1 or 0)))~=0 then goto block_1176_fin; end;
                                                                                    if ((__UNSIGNED__(reg12) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_8_fin; end;
                                                                                    
                                                                                        if ((reg12 == 0) and 1 or 0)==0 then goto if_2354_fin end 
                                                                                            reg12 = 0;
                                                                                            goto block_2351_fin;
                                                                                        ::if_2354_fin::
                                                                                        reg18 = (bit_lshift(reg12,2));
                                                                                        reg8 = (bit_tobit(reg18 + -4));
                                                                                        reg15 = (bit_tobit((bit_rshift(reg8,2)) + 1));
                                                                                        reg11 = (bit_band(reg15,3));
                                                                                        reg5 = __LONG_INT__(0,0);
                                                                                        reg1 = reg14;
                                                                                        if ((__UNSIGNED__(reg8) >= __UNSIGNED__(12)) and 1 or 0)==0 then goto if_2381_fin end 
                                                                                            reg8 = (bit_tobit(0 - (bit_band(reg15,2147483644))));
                                                                                            
                                                                                            while true do ::loop_2388_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg15 = (bit_tobit(reg1 + 4));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 8));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 12));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg37 = bit_tobit(reg1 + 16);
                                                                                                reg1 = reg37;
                                                                                                reg37 = bit_tobit(reg8 + 4);
                                                                                                reg8 = reg37;
                                                                                                if reg8~=0 then goto loop_2388_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2381_fin::
                                                                                        if reg11==0 then goto if_2456_fin end 
                                                                                            reg8 = (bit_tobit(0 - reg11));
                                                                                            
                                                                                            while true do ::loop_2461_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg37 = bit_tobit(reg1 + 4);
                                                                                                reg1 = reg37;
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg11 = (bit_tobit(reg8 + 1));
                                                                                                reg37 = (__UNSIGNED__(reg11) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                                                                reg8 = reg11;
                                                                                                if reg37~=0 then goto loop_2461_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2456_fin::
                                                                                        reg1 = ((reg5)[1]);
                                                                                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_2351_fin; end;
                                                                                        if ((__UNSIGNED__(reg12) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_1172_fin; end;
                                                                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg18)) + 4)),reg1);
                                                                                        reg37 = bit_tobit(reg12 + 1);
                                                                                        reg12 = reg37;
                                                                                    ::block_2351_fin::
                                                                                    __MEMORY_WRITE_32__(mem_0,reg4,reg12);
                                                                                    if ((__UNSIGNED__(reg34) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_1171_fin; end;
                                                                                    
                                                                                        if ((reg34 == 0) and 1 or 0)==0 then goto if_2521_fin end 
                                                                                            reg34 = 0;
                                                                                            goto block_2518_fin;
                                                                                        ::if_2521_fin::
                                                                                        reg18 = (bit_lshift(reg34,2));
                                                                                        reg8 = (bit_tobit(reg18 + -4));
                                                                                        reg15 = (bit_tobit((bit_rshift(reg8,2)) + 1));
                                                                                        reg11 = (bit_band(reg15,3));
                                                                                        reg5 = __LONG_INT__(0,0);
                                                                                        reg1 = reg13;
                                                                                        if ((__UNSIGNED__(reg8) >= __UNSIGNED__(12)) and 1 or 0)==0 then goto if_2548_fin end 
                                                                                            reg8 = (bit_tobit(0 - (bit_band(reg15,2147483644))));
                                                                                            
                                                                                            while true do ::loop_2555_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg15 = (bit_tobit(reg1 + 4));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 8));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 12));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg37 = bit_tobit(reg1 + 16);
                                                                                                reg1 = reg37;
                                                                                                reg37 = bit_tobit(reg8 + 4);
                                                                                                reg8 = reg37;
                                                                                                if reg8~=0 then goto loop_2555_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2548_fin::
                                                                                        if reg11==0 then goto if_2623_fin end 
                                                                                            reg8 = (bit_tobit(0 - reg11));
                                                                                            
                                                                                            while true do ::loop_2628_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg37 = bit_tobit(reg1 + 4);
                                                                                                reg1 = reg37;
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg11 = (bit_tobit(reg8 + 1));
                                                                                                reg37 = (__UNSIGNED__(reg11) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                                                                reg8 = reg11;
                                                                                                if reg37~=0 then goto loop_2628_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2623_fin::
                                                                                        reg1 = ((reg5)[1]);
                                                                                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_2518_fin; end;
                                                                                        if ((__UNSIGNED__(reg34) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_1170_fin; end;
                                                                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg18)) + 172)),reg1);
                                                                                        reg37 = bit_tobit(reg34 + 1);
                                                                                        reg34 = reg37;
                                                                                    ::block_2518_fin::
                                                                                    __MEMORY_WRITE_32__(mem_0,reg4+168,reg34);
                                                                                    if ((__UNSIGNED__(reg36) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_1169_fin; end;
                                                                                    
                                                                                        if ((reg36 == 0) and 1 or 0)==0 then goto if_2688_fin end 
                                                                                            reg36 = 0;
                                                                                            goto block_2685_fin;
                                                                                        ::if_2688_fin::
                                                                                        reg18 = (bit_lshift(reg36,2));
                                                                                        reg8 = (bit_tobit(reg18 + -4));
                                                                                        reg15 = (bit_tobit((bit_rshift(reg8,2)) + 1));
                                                                                        reg11 = (bit_band(reg15,3));
                                                                                        reg5 = __LONG_INT__(0,0);
                                                                                        reg1 = reg21;
                                                                                        if ((__UNSIGNED__(reg8) >= __UNSIGNED__(12)) and 1 or 0)==0 then goto if_2715_fin end 
                                                                                            reg8 = (bit_tobit(0 - (bit_band(reg15,2147483644))));
                                                                                            
                                                                                            while true do ::loop_2722_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg15 = (bit_tobit(reg1 + 4));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 8));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg15 = (bit_tobit(reg1 + 12));
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg15);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg15);
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg37 = bit_tobit(reg1 + 16);
                                                                                                reg1 = reg37;
                                                                                                reg37 = bit_tobit(reg8 + 4);
                                                                                                reg8 = reg37;
                                                                                                if reg8~=0 then goto loop_2722_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2715_fin::
                                                                                        if reg11==0 then goto if_2790_fin end 
                                                                                            reg8 = (bit_tobit(0 - reg11));
                                                                                            
                                                                                            while true do ::loop_2795_start::
                                                                                                reg37 = __MEMORY_READ_32__(mem_0,reg1);reg37=__LONG_INT__(reg37,0);
                                                                                                reg38 = (reg37 * __LONG_INT__(10,0)) + reg5;
                                                                                                reg5 = reg38;
                                                                                                (reg5):store32(mem_0,reg1);
                                                                                                reg37 = bit_tobit(reg1 + 4);
                                                                                                reg1 = reg37;
                                                                                                reg37 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                                                                reg5 = reg37;
                                                                                                reg11 = (bit_tobit(reg8 + 1));
                                                                                                reg37 = (__UNSIGNED__(reg11) >= __UNSIGNED__(reg8)) and 1 or 0;
                                                                                                reg8 = reg11;
                                                                                                if reg37~=0 then goto loop_2795_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                        ::if_2790_fin::
                                                                                        reg1 = ((reg5)[1]);
                                                                                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_2685_fin; end;
                                                                                        if ((__UNSIGNED__(reg36) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_1168_fin; end;
                                                                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg4 + reg18)) + 340)),reg1);
                                                                                        reg37 = bit_tobit(reg36 + 1);
                                                                                        reg36 = reg37;
                                                                                    ::block_2685_fin::
                                                                                    __MEMORY_WRITE_32__(mem_0,reg4+336,reg36);
                                                                                    
                                                                                    reg11 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg25)) and 1 or 0) == 0) and reg25 or reg12);
                                                                                    if ((__UNSIGNED__(reg11) <= __UNSIGNED__(40)) and 1 or 0)~=0 then goto loop_1236_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                            ::if_1190_fin::
                                                                            goto block_12_fin;
                                                                        ::block_1176_fin::
                                                                        if ((reg8 >= reg9) and 1 or 0)~=0 then goto block_13_fin; end;
                                                                        if ((reg11 < reg9) and 1 or 0)==0 then goto if_2869_fin end 
                                                                            reg9 = __FUNCS__.func_6(reg4,1);
                                                                            reg9 = __MEMORY_READ_32__(mem_0,reg4);
                                                                            reg1 = reg9;
                                                                            reg9 = __MEMORY_READ_32__(mem_0,reg4+504);
                                                                            reg8 = reg9;
                                                                            
                                                                            reg9 = (((__UNSIGNED__(reg1) > __UNSIGNED__(reg8)) and 1 or 0) == 0) and reg8 or reg1;
                                                                            reg1 = reg9;
                                                                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                                                            reg9 = bit_lshift(reg1,2);
                                                                            reg1 = reg9;
                                                                            
                                                                            while true do ::loop_2892_start::
                                                                                
                                                                                    if ((reg1 == 0) and 1 or 0)==0 then goto if_2896_fin end 
                                                                                        
                                                                                        reg8 = ((reg1 == 0) and 0 or -1);
                                                                                        goto block_2893_fin;
                                                                                    ::if_2896_fin::
                                                                                    reg8 = (bit_tobit((bit_tobit(reg4 + 504)) + reg1));
                                                                                    reg6 = (bit_tobit(reg1 + reg4));
                                                                                    reg9 = bit_tobit(reg1 + -4);
                                                                                    reg1 = reg9;
                                                                                    reg9 = __MEMORY_READ_32__(mem_0,reg6);
                                                                                    reg6 = reg9;
                                                                                    reg9 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                    reg8 = reg9;
                                                                                    
                                                                                    reg9 = (((__UNSIGNED__(reg6) < __UNSIGNED__(reg8)) and 1 or 0) == 0) and ((reg6 ~= reg8) and 1 or 0) or -1;
                                                                                    reg8 = reg9;
                                                                                    if ((reg8 == 0) and 1 or 0)~=0 then goto loop_2892_start; end;
                                                                                ::block_2893_fin::
                                                                                break
                                                                            end
                                                                            
                                                                            if ((__UNSIGNED__((bit_band(reg8,255))) >= __UNSIGNED__(2)) and 1 or 0)~=0 then goto block_13_fin; end;
                                                                        ::if_2869_fin::
                                                                        if ((__UNSIGNED__(reg18) >= __UNSIGNED__(17)) and 1 or 0)~=0 then goto block_1167_fin; end;
                                                                        reg11 = (bit_tobit(reg2 + reg10));
                                                                        reg8 = -1;
                                                                        reg1 = reg18;
                                                                        
                                                                            
                                                                            while true do ::loop_2955_start::
                                                                                if ((reg1 == -1) and 1 or 0)~=0 then goto block_2954_fin; end;
                                                                                reg9 = bit_tobit(reg8 + 1);
                                                                                reg8 = reg9;
                                                                                reg6 = (bit_tobit(reg1 + -1));
                                                                                reg9 = bit_tobit(reg1 + reg2);
                                                                                reg1 = reg6;
                                                                                reg37 = __MEMORY_READ_8__(mem_0,reg9);
                                                                                if ((reg37 == 57) and 1 or 0)~=0 then goto loop_2955_start; end;
                                                                                break
                                                                            end
                                                                            
                                                                            reg1 = (bit_tobit(reg2 + reg6));
                                                                            reg11 = (bit_tobit(reg1 + 1));
                                                                            reg9 = __MEMORY_READ_8__(mem_0,reg11);
                                                                            __MEMORY_WRITE_8__(mem_0,reg11,(bit_tobit(reg9 + 1)));
                                                                            if ((__UNSIGNED__(reg18) < __UNSIGNED__((bit_tobit(reg6 + 2)))) and 1 or 0)~=0 then goto block_13_fin; end;
                                                                            reg6 = __FUNCS__.func_65((bit_tobit(reg1 + 2)),48,reg8);
                                                                            goto block_13_fin;
                                                                        ::block_2954_fin::
                                                                        __MEMORY_WRITE_8__(mem_0,reg2,49);
                                                                        if reg18==0 then goto if_3008_fin end 
                                                                            reg6 = __FUNCS__.func_65((bit_tobit(reg2 + 1)),48,reg18);
                                                                        ::if_3008_fin::
                                                                        if ((__UNSIGNED__(reg10) < __UNSIGNED__(17)) and 1 or 0)==0 then goto if_3020_fin end 
                                                                            __MEMORY_WRITE_8__(mem_0,reg11,48);
                                                                            reg6 = bit_tobit(reg3 + 1);
                                                                            reg3 = reg6;
                                                                            reg10 = (bit_tobit(reg18 + 2));
                                                                            goto block_13_fin;
                                                                        ::if_3020_fin::
                                                                        __FUNCS__.func_82(reg10,17,1052708);
                                                                        error('unreachable');
                                                                    ::block_1175_fin::
                                                                    __FUNCS__.func_84(reg33,40,1058148);
                                                                    error('unreachable');
                                                                ::block_1174_fin::
                                                                __FUNCS__.func_82(reg33,40,1058148);
                                                                error('unreachable');
                                                            ::block_1173_fin::
                                                            __FUNCS__.func_82(17,17,1052676);
                                                            error('unreachable');
                                                        ::block_1172_fin::
                                                        __FUNCS__.func_82(reg12,40,1058148);
                                                        error('unreachable');
                                                    ::block_1171_fin::
                                                    __FUNCS__.func_84(reg34,40,1058148);
                                                    error('unreachable');
                                                ::block_1170_fin::
                                                __FUNCS__.func_82(reg34,40,1058148);
                                                error('unreachable');
                                            ::block_1169_fin::
                                            __FUNCS__.func_84(reg36,40,1058148);
                                            error('unreachable');
                                        ::block_1168_fin::
                                        __FUNCS__.func_82(reg36,40,1058148);
                                        error('unreachable');
                                    ::block_1167_fin::
                                    __FUNCS__.func_84(reg10,17,1052692);
                                    error('unreachable');
                                ::block_14_fin::
                                __FUNCS__.func_82(reg12,40,1058148);
                                error('unreachable');
                            ::block_13_fin::
                            if ((__UNSIGNED__(reg10) <= __UNSIGNED__(17)) and 1 or 0)==0 then goto if_3103_fin end 
                                __MEMORY_WRITE_16__(mem_0,reg0+8,reg3);
                                __MEMORY_WRITE_32__(mem_0,reg0+4,reg10);
                                __MEMORY_WRITE_32__(mem_0,reg0,reg2);
                                __GLOBALS__[0] = (bit_tobit(reg4 + 1344));
                                do return  end
                            ::if_3103_fin::
                            __FUNCS__.func_84(reg10,17,1052724);
                            error('unreachable');
                        ::block_12_fin::
                        __FUNCS__.func_84(reg11,40,1058148);
                        error('unreachable');
                    ::block_11_fin::
                    __FUNCS__.func_84(reg1,40,1058148);
                    error('unreachable');
                ::block_10_fin::
                __FUNCS__.func_84(reg10,40,1058148);
                error('unreachable');
            ::block_9_fin::
            __FUNCS__.func_110(1058164,26,1058148);
            error('unreachable');
        ::block_8_fin::
        __FUNCS__.func_84(reg12,40,1058148);
        error('unreachable');
    end
    function __FUNCS__.func_1(reg0, reg1, reg2, reg3, reg4)
        local reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19,reg20,reg21,reg22,reg23,reg24,reg25,reg26,reg27,reg28,reg29,reg30,reg31,reg32,reg33,reg34,reg35,reg36,reg37;
        reg5 = __GLOBALS__[0];
        reg6 = (bit_tobit(reg5 - 848));
        __GLOBALS__[0] = reg6;
        
            
                
                    
                        
                            
                                
                                    
                                        
                                            
                                                
                                                    
                                                        
                                                            
                                                                
                                                                    reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg1);
                                                                    reg7 = reg5;
                                                                    if (((((reg7)[1] == 0) and ((reg7)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_28_fin end 
                                                                        reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg1+8);
                                                                        reg8 = reg5;
                                                                        if (((reg8)[1] == 0) and ((reg8)[2] == 0) and 1 or 0)~=0 then goto block_22_fin; end;
                                                                        reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg1+16);
                                                                        reg9 = reg5;
                                                                        if (((reg9)[1] == 0) and ((reg9)[2] == 0) and 1 or 0)~=0 then goto block_21_fin; end;
                                                                        if (((reg7 + reg9)):_lt_u(reg7) and 1 or 0)~=0 then goto block_20_fin; end;
                                                                        if (((reg7 - reg8)):_gt_u(reg7) and 1 or 0)~=0 then goto block_19_fin; end;
                                                                        reg5 = __MEMORY_READ_16__(mem_0,reg1+24);
                                                                        reg1 = reg5;
                                                                        (reg7):store32(mem_0,reg6+12);
                                                                        reg5 = ((reg7):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                                                        
                                                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 16)),((reg5 == 0) and ((((reg7):_shr_u(__LONG_INT__(32,0))))[1]) or 0));
                                                                        
                                                                        __MEMORY_WRITE_32__(mem_0,reg6+8,((reg5 == 0) and 2 or 1));
                                                                        reg10 = __FUNCS__.func_65((bit_tobit(reg6 + 20)),0,152);
                                                                        reg10 = __FUNCS__.func_65((bit_tobit(reg6 + 184)),0,156);
                                                                        (__LONG_INT__(1,1)):store(mem_0,reg6+176);
                                                                        reg5 = ((((((((((((__LONG_INT__(reg1,0))):_shl(__LONG_INT__(48,0)))):_shr_s(__LONG_INT__(48,0))) - ((reg7 + __LONG_INT__(-1,-1)):_clz())) * __LONG_INT__(1292913986,0)) + __LONG_INT__(1142116480,19))):_shr_u(__LONG_INT__(32,0))))[1]);
                                                                        reg10 = (bit_arshift((bit_lshift(reg5,16)),16));
                                                                        
                                                                            reg11 = (bit_arshift((bit_lshift(reg1,16)),16));
                                                                            if ((reg11 >= 0) and 1 or 0)==0 then goto if_127_fin end 
                                                                                reg12 = __FUNCS__.func_6((bit_tobit(reg6 + 8)),reg1);
                                                                                goto block_118_fin;
                                                                            ::if_127_fin::
                                                                            reg12 = __FUNCS__.func_6((bit_tobit(reg6 + 176)),(bit_arshift((bit_lshift((bit_tobit(0 - reg11)),16)),16)));
                                                                        ::block_118_fin::
                                                                        
                                                                            if ((reg10 <= -1) and 1 or 0)==0 then goto if_153_fin end 
                                                                                __FUNCS__.func_15((bit_tobit(reg6 + 8)),(bit_arshift((bit_lshift((bit_tobit(0 - reg10)),16)),16)));
                                                                                goto block_149_fin;
                                                                            ::if_153_fin::
                                                                            __FUNCS__.func_15((bit_tobit(reg6 + 176)),(bit_band(reg5,65535)));
                                                                        ::block_149_fin::
                                                                        reg12 = __MEMORY_READ_32__(mem_0,reg6+176);
                                                                        reg13 = reg12;
                                                                        reg12 = (bit_bor((bit_tobit(reg6 + 176)),4));
                                                                        reg14 = __FUNCS__.func_64((bit_bor((bit_tobit(reg6 + 680)),4)),reg12,160);
                                                                        __MEMORY_WRITE_32__(mem_0,reg6+680,reg13);
                                                                        
                                                                            reg11 = reg3;
                                                                            if ((__UNSIGNED__(reg11) < __UNSIGNED__(10)) and 1 or 0)~=0 then goto block_195_fin; end;
                                                                            
                                                                                if ((__UNSIGNED__(reg13) > __UNSIGNED__(40)) and 1 or 0)==0 then goto if_205_fin end 
                                                                                    reg1 = reg13;
                                                                                    goto block_201_fin;
                                                                                ::if_205_fin::
                                                                                reg14 = (bit_tobit(reg6 + 676));
                                                                                reg1 = reg13;
                                                                                
                                                                                while true do ::loop_216_start::
                                                                                    
                                                                                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_217_fin; end;
                                                                                        reg15 = bit_lshift(reg1,2);
                                                                                        reg1 = reg15;
                                                                                        reg5 = (bit_tobit(reg1 + -4));
                                                                                        reg15 = (bit_tobit((bit_rshift(reg5,2)) + 1));
                                                                                        
                                                                                            if ((reg5 == 0) and 1 or 0)==0 then goto if_238_fin end 
                                                                                                reg7 = __LONG_INT__(0,0);
                                                                                                reg16 = (bit_tobit((bit_tobit(reg1 + reg6)) + 684)); goto block_235_fin;
                                                                                            ::if_238_fin::
                                                                                            reg17 = bit_tobit(reg1 + reg14);
                                                                                            reg1 = reg17;
                                                                                            reg5 = (bit_tobit(0 - (bit_band(reg15,2147483646))));
                                                                                            reg7 = __LONG_INT__(0,0);
                                                                                            
                                                                                            while true do ::loop_260_start::
                                                                                                reg17 = bit_band(reg15,1);
                                                                                                reg15 = (bit_tobit(reg1 + 4));
                                                                                                reg18 = __MEMORY_READ_32__(mem_0,reg15);reg18=__LONG_INT__(reg18,0);
                                                                                                reg19 = (reg18):_or(((reg7):_shl(__LONG_INT__(32,0))));
                                                                                                reg7 = reg19;
                                                                                                reg8 = ((reg7):_div_u(__LONG_INT__(1000000000,0)));
                                                                                                (reg8):store32(mem_0,reg15);
                                                                                                reg18 = __MEMORY_READ_32__(mem_0,reg1);reg18=__LONG_INT__(reg18,0);
                                                                                                reg19 = (reg18):_or((((reg7 - (reg8 * __LONG_INT__(1000000000,0)))):_shl(__LONG_INT__(32,0))));
                                                                                                reg7 = reg19;
                                                                                                reg8 = ((reg7):_div_u(__LONG_INT__(1000000000,0)));
                                                                                                (reg8):store32(mem_0,reg1);
                                                                                                reg18 = reg7 - (reg8 * __LONG_INT__(1000000000,0));
                                                                                                reg7 = reg18;
                                                                                                reg18 = bit_tobit(reg1 + -8);
                                                                                                reg1 = reg18;
                                                                                                reg18 = bit_tobit(reg5 + 2);
                                                                                                reg5 = reg18;
                                                                                                if reg5~=0 then goto loop_260_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                            reg16 = (bit_tobit(reg1 + 8))
                                                                                            -- BLOCK RET (block):
                                                                                        ::block_235_fin::
                                                                                        reg1 = reg16;
                                                                                        if ((reg17 == 0) and 1 or 0)~=0 then goto block_217_fin; end;
                                                                                        reg16 = bit_tobit(reg1 + -4);
                                                                                        reg1 = reg16;
                                                                                        reg16 = __MEMORY_READ_32__(mem_0,reg1);reg16=__LONG_INT__(reg16,0);
                                                                                        (((((reg16):_or(((reg7):_shl(__LONG_INT__(32,0)))))):_div_u(__LONG_INT__(1000000000,0)))):store32(mem_0,reg1);
                                                                                    ::block_217_fin::
                                                                                    reg16 = bit_tobit(reg11 + -9);
                                                                                    reg11 = reg16;
                                                                                    if ((__UNSIGNED__(reg11) <= __UNSIGNED__(9)) and 1 or 0)~=0 then goto block_195_fin; end;
                                                                                    reg16 = __MEMORY_READ_32__(mem_0,reg6+680);
                                                                                    reg1 = reg16;
                                                                                    if ((__UNSIGNED__(reg1) < __UNSIGNED__(41)) and 1 or 0)~=0 then goto loop_216_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                            ::block_201_fin::
                                                                            goto block_11_fin;
                                                                        ::block_195_fin::
                                                                        
                                                                            
                                                                                
                                                                                    
                                                                                        
                                                                                            
                                                                                                reg18 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift(reg11,2)) + 1052028)));
                                                                                                reg5 = reg18;
                                                                                                if reg5==0 then goto if_359_fin end 
                                                                                                    reg18 = __MEMORY_READ_32__(mem_0,reg6+680);
                                                                                                    reg1 = reg18;
                                                                                                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                                                                                    if ((reg1 == 0) and 1 or 0)~=0 then reg16 = 0; goto block_349_fin; end;
                                                                                                    reg7 = (__LONG_INT__(reg5,0));
                                                                                                    reg5 = (bit_lshift(reg1,2));
                                                                                                    reg1 = (bit_tobit(reg5 + -4));
                                                                                                    reg11 = (bit_tobit((bit_rshift(reg1,2)) + 1));
                                                                                                    reg14 = (bit_band(reg11,1));
                                                                                                    if reg1~=0 then goto block_351_fin; end;
                                                                                                    reg8 = __LONG_INT__(0,0);
                                                                                                    reg17 = (bit_tobit((bit_tobit(reg5 + reg6)) + 684)); goto block_350_fin;
                                                                                                ::if_359_fin::
                                                                                                __FUNCS__.func_110(1058219,27,1058148);
                                                                                                error('unreachable');
                                                                                            ::block_351_fin::
                                                                                            reg5 = (bit_tobit(0 - (bit_band(reg11,2147483646))));
                                                                                            reg18 = bit_tobit((bit_tobit(reg6 + 680)) + reg1);
                                                                                            reg1 = reg18;
                                                                                            reg8 = __LONG_INT__(0,0);
                                                                                            
                                                                                            while true do ::loop_420_start::
                                                                                                reg11 = (bit_tobit(reg1 + 4));
                                                                                                reg18 = __MEMORY_READ_32__(mem_0,reg11);reg18=__LONG_INT__(reg18,0);
                                                                                                reg19 = (reg18):_or(((reg8):_shl(__LONG_INT__(32,0))));
                                                                                                reg8 = reg19;
                                                                                                reg9 = ((reg8):_div_u(reg7));
                                                                                                (reg9):store32(mem_0,reg11);
                                                                                                reg18 = __MEMORY_READ_32__(mem_0,reg1);reg18=__LONG_INT__(reg18,0);
                                                                                                reg19 = (reg18):_or((((reg8 - (reg7 * reg9))):_shl(__LONG_INT__(32,0))));
                                                                                                reg8 = reg19;
                                                                                                reg9 = ((reg8):_div_u(reg7));
                                                                                                (reg9):store32(mem_0,reg1);
                                                                                                reg18 = reg8 - (reg7 * reg9);
                                                                                                reg8 = reg18;
                                                                                                reg9 = bit_tobit(reg1 + -8);
                                                                                                reg1 = reg9;
                                                                                                reg9 = bit_tobit(reg5 + 2);
                                                                                                reg5 = reg9;
                                                                                                if reg5~=0 then goto loop_420_start; end;
                                                                                                break
                                                                                            end
                                                                                            
                                                                                            reg17 = (bit_tobit(reg1 + 8))
                                                                                            -- BLOCK RET (block):
                                                                                        ::block_350_fin::
                                                                                        reg1 = reg17;
                                                                                        if reg14==0 then goto if_474_fin end 
                                                                                            reg9 = bit_tobit(reg1 + -4);
                                                                                            reg1 = reg9;
                                                                                            reg9 = __MEMORY_READ_32__(mem_0,reg1);reg9=__LONG_INT__(reg9,0);
                                                                                            (((((reg9):_or(((reg8):_shl(__LONG_INT__(32,0)))))):_div_u(reg7))):store32(mem_0,reg1);
                                                                                        ::if_474_fin::
                                                                                        reg8 = __MEMORY_READ_32__(mem_0,reg6+680);
                                                                                        reg16 = reg8
                                                                                        -- BLOCK RET (block):
                                                                                    ::block_349_fin::
                                                                                    reg1 = reg16;
                                                                                    reg8 = __MEMORY_READ_32__(mem_0,reg6+8);
                                                                                    reg9 = reg8;
                                                                                    
                                                                                    reg14 = ((((__UNSIGNED__(reg1) > __UNSIGNED__(reg9)) and 1 or 0) == 0) and reg9 or reg1);
                                                                                    if ((__UNSIGNED__(reg14) <= __UNSIGNED__(40)) and 1 or 0)==0 then goto if_503_fin end 
                                                                                        if ((reg14 == 0) and 1 or 0)==0 then goto if_506_fin end 
                                                                                            reg14 = 0;
                                                                                            goto block_346_fin;
                                                                                        ::if_506_fin::
                                                                                        reg8 = (bit_band(reg14,1));
                                                                                        if ((reg14 ~= 1) and 1 or 0)~=0 then goto block_348_fin; end;
                                                                                        reg11 = 0;
                                                                                        goto block_347_fin;
                                                                                    ::if_503_fin::
                                                                                    __FUNCS__.func_84(reg14,40,1058148);
                                                                                    error('unreachable');
                                                                                ::block_348_fin::
                                                                                reg16 = (bit_band(reg14,-2));
                                                                                reg5 = (bit_tobit(reg6 + 16));
                                                                                reg1 = (bit_tobit(reg6 + 688));
                                                                                reg11 = 0;
                                                                                -- FORCE INIT VAR | i32
                                                                                reg17 = 0;
                                                                                
                                                                                while true do ::loop_543_start::
                                                                                    reg15 = (bit_tobit(reg1 + -4));
                                                                                    reg18 = __MEMORY_READ_32__(mem_0,reg15);
                                                                                    reg19 = reg18;
                                                                                    reg18 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + -4)));
                                                                                    reg20 = reg15;
                                                                                    reg15 = (bit_tobit(reg19 + reg18));
                                                                                    reg18 = (bit_tobit(reg15 + (bit_band(reg11,1))));
                                                                                    __MEMORY_WRITE_32__(mem_0,reg20,reg18);
                                                                                    reg20 = __MEMORY_READ_32__(mem_0,reg1);
                                                                                    reg21 = reg20;
                                                                                    reg20 = __MEMORY_READ_32__(mem_0,reg5);
                                                                                    reg11 = (bit_tobit(reg21 + reg20));
                                                                                    reg20 = bit_tobit(reg11 + (bit_bor(((__UNSIGNED__(reg15) < __UNSIGNED__(reg19)) and 1 or 0),((__UNSIGNED__(reg18) < __UNSIGNED__(reg15)) and 1 or 0))));
                                                                                    reg15 = reg20;
                                                                                    __MEMORY_WRITE_32__(mem_0,reg1,reg15);
                                                                                    reg20 = bit_bor(((__UNSIGNED__(reg11) < __UNSIGNED__(reg21)) and 1 or 0),((__UNSIGNED__(reg15) < __UNSIGNED__(reg11)) and 1 or 0));
                                                                                    reg11 = reg20;
                                                                                    reg20 = bit_tobit(reg5 + 8);
                                                                                    reg5 = reg20;
                                                                                    reg20 = bit_tobit(reg1 + 8);
                                                                                    reg1 = reg20;
                                                                                    reg20 = bit_tobit(reg17 + 2);
                                                                                    reg17 = reg20;
                                                                                    if ((reg16 ~= reg17) and 1 or 0)~=0 then goto loop_543_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                            ::block_347_fin::
                                                                            if reg8==0 then goto if_607_else end 
                                                                                reg1 = (bit_lshift(reg17,2));
                                                                                reg5 = (bit_tobit((bit_tobit(reg6 + reg1)) + 684));
                                                                                reg22 = __MEMORY_READ_32__(mem_0,reg5);
                                                                                reg23 = reg5;
                                                                                reg5 = reg22;
                                                                                reg22 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg1 + reg6)) + 12)));
                                                                                reg1 = (bit_tobit(reg5 + reg22));
                                                                                reg22 = bit_tobit(reg1 + reg11);
                                                                                reg11 = reg22;
                                                                                __MEMORY_WRITE_32__(mem_0,reg23,reg11);
                                                                                reg20 = (bit_bor(((__UNSIGNED__(reg1) < __UNSIGNED__(reg5)) and 1 or 0),((__UNSIGNED__(reg11) < __UNSIGNED__(reg1)) and 1 or 0)))
                                                                            goto if_607_fin
                                                                            ::if_607_else::
                                                                                reg20 = reg11
                                                                                -- BLOCK RET (if):
                                                                            ::if_607_fin::
                                                                            if (((bit_band(reg20,1)) == 0) and 1 or 0)~=0 then goto block_346_fin; end;
                                                                            if ((__UNSIGNED__(reg14) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_18_fin; end;
                                                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit((bit_lshift(reg14,2)) + reg6)) + 684)),1);
                                                                            reg20 = bit_tobit(reg14 + 1);
                                                                            reg14 = reg20;
                                                                        ::block_346_fin::
                                                                        __MEMORY_WRITE_32__(mem_0,reg6+680,reg14);
                                                                        
                                                                        reg5 = ((((__UNSIGNED__(reg14) > __UNSIGNED__(reg13)) and 1 or 0) == 0) and reg13 or reg14);
                                                                        if ((__UNSIGNED__(reg5) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_17_fin; end;
                                                                        reg1 = (bit_bor((bit_tobit(reg6 + 176)),4));
                                                                        reg14 = (bit_bor((bit_tobit(reg6 + 8)),4));
                                                                        reg20 = bit_lshift(reg5,2);
                                                                        reg5 = reg20;
                                                                        
                                                                        while true do ::loop_692_start::
                                                                            
                                                                                if ((reg5 == 0) and 1 or 0)==0 then goto if_696_fin end 
                                                                                    
                                                                                    reg11 = ((reg5 == 0) and 0 or -1);
                                                                                    goto block_693_fin;
                                                                                ::if_696_fin::
                                                                                reg11 = (bit_tobit((bit_tobit(reg6 + 176)) + reg5));
                                                                                reg15 = (bit_tobit((bit_tobit(reg6 + 680)) + reg5));
                                                                                reg20 = bit_tobit(reg5 + -4);
                                                                                reg5 = reg20;
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg15);
                                                                                reg15 = reg20;
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                reg11 = reg20;
                                                                                
                                                                                reg20 = (((__UNSIGNED__(reg15) < __UNSIGNED__(reg11)) and 1 or 0) == 0) and ((reg15 ~= reg11) and 1 or 0) or -1;
                                                                                reg11 = reg20;
                                                                                if ((reg11 == 0) and 1 or 0)~=0 then goto loop_692_start; end;
                                                                            ::block_693_fin::
                                                                            break
                                                                        end
                                                                        
                                                                        if ((__UNSIGNED__((bit_band(reg11,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_742_fin end 
                                                                            if ((__UNSIGNED__(reg9) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_10_fin; end;
                                                                            if ((reg9 == 0) and 1 or 0)==0 then goto if_749_fin end 
                                                                                __MEMORY_WRITE_32__(mem_0,reg6+8,0);
                                                                                goto block_15_fin;
                                                                            ::if_749_fin::
                                                                            reg8 = (bit_lshift(reg9,2));
                                                                            reg5 = (bit_tobit(reg8 + -4));
                                                                            reg11 = (bit_tobit((bit_rshift(reg5,2)) + 1));
                                                                            reg15 = (bit_band(reg11,3));
                                                                            if ((__UNSIGNED__(reg5) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_773_fin end 
                                                                                reg7 = __LONG_INT__(0,0);
                                                                                reg5 = reg14;
                                                                                goto block_16_fin;
                                                                            ::if_773_fin::
                                                                            reg20 = bit_tobit(0 - (bit_band(reg11,2147483644)));
                                                                            reg11 = reg20;
                                                                            reg7 = __LONG_INT__(0,0);
                                                                            reg5 = reg14;
                                                                            
                                                                            while true do ::loop_790_start::
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg5);reg20=__LONG_INT__(reg20,0);
                                                                                reg22 = (reg20 * __LONG_INT__(10,0)) + reg7;
                                                                                reg7 = reg22;
                                                                                (reg7):store32(mem_0,reg5);
                                                                                reg16 = (bit_tobit(reg5 + 4));
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg16);reg20=__LONG_INT__(reg20,0);
                                                                                reg22 = (reg20 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                                                reg7 = reg22;
                                                                                (reg7):store32(mem_0,reg16);
                                                                                reg16 = (bit_tobit(reg5 + 8));
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg16);reg20=__LONG_INT__(reg20,0);
                                                                                reg22 = (reg20 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                                                reg7 = reg22;
                                                                                (reg7):store32(mem_0,reg16);
                                                                                reg16 = (bit_tobit(reg5 + 12));
                                                                                reg20 = __MEMORY_READ_32__(mem_0,reg16);reg20=__LONG_INT__(reg20,0);
                                                                                reg22 = (reg20 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                                                reg7 = reg22;
                                                                                (reg7):store32(mem_0,reg16);
                                                                                reg20 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                                                reg7 = reg20;
                                                                                reg20 = bit_tobit(reg5 + 16);
                                                                                reg5 = reg20;
                                                                                reg20 = bit_tobit(reg11 + 4);
                                                                                reg11 = reg20;
                                                                                if reg11~=0 then goto loop_790_start; end;
                                                                                break
                                                                            end
                                                                            
                                                                            goto block_16_fin;
                                                                        ::if_742_fin::
                                                                        reg20 = bit_tobit(reg10 + 1);
                                                                        reg10 = reg20;
                                                                        goto block_15_fin;
                                                                    ::if_28_fin::
                                                                    __FUNCS__.func_110(1052331,28,1052740);
                                                                    error('unreachable');
                                                                ::block_22_fin::
                                                                __FUNCS__.func_110(1052376,29,1052756);
                                                                error('unreachable');
                                                            ::block_21_fin::
                                                            __FUNCS__.func_110(1052424,28,1052772);
                                                            error('unreachable');
                                                        ::block_20_fin::
                                                        __FUNCS__.func_110(1052468,54,1052788);
                                                        error('unreachable');
                                                    ::block_19_fin::
                                                    __FUNCS__.func_110(1052540,55,1052804);
                                                    error('unreachable');
                                                ::block_18_fin::
                                                __FUNCS__.func_82(reg14,40,1058148);
                                                error('unreachable');
                                            ::block_17_fin::
                                            __FUNCS__.func_84(reg5,40,1058148);
                                            error('unreachable');
                                        ::block_16_fin::
                                        if reg15==0 then goto if_907_fin end 
                                            reg11 = (bit_tobit(0 - reg15));
                                            
                                            while true do ::loop_912_start::
                                                reg20 = __MEMORY_READ_32__(mem_0,reg5);reg20=__LONG_INT__(reg20,0);
                                                reg22 = (reg20 * __LONG_INT__(10,0)) + reg7;
                                                reg7 = reg22;
                                                (reg7):store32(mem_0,reg5);
                                                reg20 = bit_tobit(reg5 + 4);
                                                reg5 = reg20;
                                                reg20 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                reg7 = reg20;
                                                reg15 = (bit_tobit(reg11 + 1));
                                                reg20 = (__UNSIGNED__(reg15) >= __UNSIGNED__(reg11)) and 1 or 0;
                                                reg11 = reg15;
                                                if reg20~=0 then goto loop_912_start; end;
                                                break
                                            end
                                            
                                        ::if_907_fin::
                                        reg5 = ((reg7)[1]);
                                        if reg5==0 then goto if_945_else end 
                                            if ((__UNSIGNED__(reg9) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_14_fin; end;
                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg6 + reg8)) + 12)),reg5);
                                            reg20 = (bit_tobit(reg9 + 1))
                                        goto if_945_fin
                                        ::if_945_else::
                                            reg20 = reg9
                                            -- BLOCK RET (if):
                                        ::if_945_fin::
                                        __MEMORY_WRITE_32__(mem_0,reg6+8,reg20);
                                    ::block_15_fin::
                                    reg20 = 1;
                                    
                                        reg5 = (bit_arshift((bit_lshift(reg10,16)),16));
                                        reg11 = (bit_arshift((bit_lshift(reg4,16)),16));
                                        if ((reg5 >= reg11) and 1 or 0)==0 then goto if_980_fin end 
                                            
                                            reg17 = ((((__UNSIGNED__((bit_tobit(reg5 - reg11))) < __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg3 or (bit_arshift((bit_lshift((bit_tobit(reg10 - reg4)),16)),16)));
                                            if reg17~=0 then goto block_966_fin; end;
                                        ::if_980_fin::
                                        reg17 = 0;
                                        goto block_13_fin;
                                    ::block_966_fin::
                                    reg22 = __FUNCS__.func_64((bit_bor((bit_tobit(reg6 + 344)),4)),reg12,160);
                                    __MEMORY_WRITE_32__(mem_0,reg6+344,reg13);
                                    reg22 = __FUNCS__.func_6((bit_tobit(reg6 + 344)),1);
                                    reg23 = reg22;
                                    reg22 = __MEMORY_READ_32__(mem_0,reg6+176);
                                    reg5 = reg22;
                                    reg22 = __FUNCS__.func_64((bit_bor((bit_tobit(reg6 + 512)),4)),reg12,160);
                                    __MEMORY_WRITE_32__(mem_0,reg6+512,reg5);
                                    reg22 = __FUNCS__.func_6((bit_tobit(reg6 + 512)),2);
                                    reg24 = reg22;
                                    reg22 = __MEMORY_READ_32__(mem_0,reg6+176);
                                    reg5 = reg22;
                                    reg22 = __FUNCS__.func_64((bit_bor((bit_tobit(reg6 + 680)),4)),reg12,160);
                                    __MEMORY_WRITE_32__(mem_0,reg6+680,reg5);
                                    reg18 = (bit_tobit(reg6 + 184));
                                    reg21 = (bit_tobit(reg6 + 352));
                                    reg22 = (bit_tobit(reg6 + 520));
                                    reg25 = (bit_tobit(reg6 + 688));
                                    reg15 = (bit_tobit(reg6 + 16));
                                    reg26 = __FUNCS__.func_6((bit_tobit(reg6 + 680)),3);
                                    reg27 = reg26;
                                    reg26 = __MEMORY_READ_32__(mem_0,reg6+8);
                                    reg12 = reg26;
                                    reg26 = __MEMORY_READ_32__(mem_0,reg6+176);
                                    reg13 = reg26;
                                    reg26 = __MEMORY_READ_32__(mem_0,reg6+344);
                                    reg28 = reg26;
                                    reg26 = __MEMORY_READ_32__(mem_0,reg6+512);
                                    reg29 = reg26;
                                    reg26 = __MEMORY_READ_32__(mem_0,reg6+680);
                                    reg30 = reg26;
                                    reg19 = 0;
                                    
                                        
                                            
                                            while true do ::loop_1101_start::
                                                reg16 = reg19;
                                                
                                                    
                                                        
                                                            if ((__UNSIGNED__(reg12) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_1110_fin end 
                                                                reg19 = (bit_tobit(reg16 + 1));
                                                                reg5 = (bit_lshift(reg12,2));
                                                                reg11 = reg14;
                                                                
                                                                    
                                                                        
                                                                            
                                                                            while true do ::loop_1124_start::
                                                                                if ((reg5 == 0) and 1 or 0)~=0 then goto block_1123_fin; end;
                                                                                reg31 = bit_tobit(reg5 + -4);
                                                                                reg5 = reg31;
                                                                                reg31 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                reg32 = bit_tobit(reg11 + 4);
                                                                                reg11 = reg32;
                                                                                if ((reg31 == 0) and 1 or 0)~=0 then goto loop_1124_start; end;
                                                                                break
                                                                            end
                                                                            
                                                                            
                                                                            reg9 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg30)) and 1 or 0) == 0) and reg30 or reg12);
                                                                            if ((__UNSIGNED__(reg9) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_10_fin; end;
                                                                            reg5 = (bit_lshift(reg9,2));
                                                                            
                                                                            while true do ::loop_1155_start::
                                                                                
                                                                                    if ((reg5 == 0) and 1 or 0)==0 then goto if_1159_fin end 
                                                                                        
                                                                                        reg11 = ((reg5 == 0) and 0 or -1);
                                                                                        goto block_1156_fin;
                                                                                    ::if_1159_fin::
                                                                                    reg11 = (bit_tobit((bit_tobit(reg6 + 680)) + reg5));
                                                                                    reg8 = (bit_tobit((bit_tobit(reg6 + 8)) + reg5));
                                                                                    reg31 = bit_tobit(reg5 + -4);
                                                                                    reg5 = reg31;
                                                                                    reg31 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                    reg8 = reg31;
                                                                                    reg31 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                    reg11 = reg31;
                                                                                    
                                                                                    reg31 = (((__UNSIGNED__(reg8) < __UNSIGNED__(reg11)) and 1 or 0) == 0) and ((reg8 ~= reg11) and 1 or 0) or -1;
                                                                                    reg11 = reg31;
                                                                                    if ((reg11 == 0) and 1 or 0)~=0 then goto loop_1155_start; end;
                                                                                ::block_1156_fin::
                                                                                break
                                                                            end
                                                                            
                                                                            if ((__UNSIGNED__((bit_band(reg11,255))) >= __UNSIGNED__(2)) and 1 or 0)~=0 then reg26 = 0; goto block_1121_fin; end;
                                                                            if ((reg9 == 0) and 1 or 0)~=0 then goto block_1122_fin; end;
                                                                            reg20 = 1;
                                                                            reg12 = 0;
                                                                            if ((reg9 ~= 1) and 1 or 0)==0 then goto if_1218_fin end 
                                                                                reg31 = (bit_band(reg9,-2));
                                                                                reg11 = reg25;
                                                                                reg5 = reg15;
                                                                                
                                                                                while true do ::loop_1227_start::
                                                                                    reg8 = (bit_tobit(reg5 + -4));
                                                                                    reg32 = __MEMORY_READ_32__(mem_0,reg8);
                                                                                    reg33 = reg32;
                                                                                    reg32 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + -4)));
                                                                                    reg34 = reg8;
                                                                                    reg8 = (bit_tobit(reg33 + (bit_bxor(reg32,-1))));
                                                                                    reg32 = (bit_tobit(reg8 + reg20));
                                                                                    __MEMORY_WRITE_32__(mem_0,reg34,reg32);
                                                                                    reg34 = __MEMORY_READ_32__(mem_0,reg5);
                                                                                    reg35 = reg34;
                                                                                    reg34 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                    reg20 = (bit_tobit(reg35 + (bit_bxor(reg34,-1))));
                                                                                    reg34 = bit_tobit(reg20 + (bit_bor(((__UNSIGNED__(reg8) < __UNSIGNED__(reg33)) and 1 or 0),((__UNSIGNED__(reg32) < __UNSIGNED__(reg8)) and 1 or 0))));
                                                                                    reg8 = reg34;
                                                                                    __MEMORY_WRITE_32__(mem_0,reg5,reg8);
                                                                                    reg34 = bit_bor(((__UNSIGNED__(reg20) < __UNSIGNED__(reg35)) and 1 or 0),((__UNSIGNED__(reg8) < __UNSIGNED__(reg20)) and 1 or 0));
                                                                                    reg20 = reg34;
                                                                                    reg34 = bit_tobit(reg11 + 8);
                                                                                    reg11 = reg34;
                                                                                    reg34 = bit_tobit(reg5 + 8);
                                                                                    reg5 = reg34;
                                                                                    reg34 = bit_tobit(reg12 + 2);
                                                                                    reg12 = reg34;
                                                                                    if ((reg31 ~= reg12) and 1 or 0)~=0 then goto loop_1227_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                            ::if_1218_fin::
                                                                            if (bit_band(reg9,1))==0 then goto if_1295_else end 
                                                                                reg5 = (bit_lshift(reg12,2));
                                                                                reg11 = (bit_tobit((bit_tobit(reg6 + reg5)) + 12));
                                                                                reg36 = __MEMORY_READ_32__(mem_0,reg11);
                                                                                reg37 = reg11;
                                                                                reg11 = reg36;
                                                                                reg36 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg5 + reg27)) + 4)));
                                                                                reg5 = (bit_tobit(reg11 + (bit_bxor(reg36,-1))));
                                                                                reg12 = (bit_tobit(reg5 + reg20));
                                                                                __MEMORY_WRITE_32__(mem_0,reg37,reg12);
                                                                                reg34 = (bit_bor(((__UNSIGNED__(reg5) < __UNSIGNED__(reg11)) and 1 or 0),((__UNSIGNED__(reg12) < __UNSIGNED__(reg5)) and 1 or 0)))
                                                                            goto if_1295_fin
                                                                            ::if_1295_else::
                                                                                reg34 = reg20
                                                                                -- BLOCK RET (if):
                                                                            ::if_1295_fin::
                                                                            if reg34~=0 then goto block_1122_fin; end;
                                                                            goto block_9_fin;
                                                                        ::block_1123_fin::
                                                                        if ((__UNSIGNED__(reg17) < __UNSIGNED__(reg16)) and 1 or 0)~=0 then goto block_1106_fin; end;
                                                                        if ((__UNSIGNED__(reg17) > __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_1105_fin; end;
                                                                        if ((reg17 == reg16) and 1 or 0)~=0 then goto block_12_fin; end;
                                                                        reg34 = __FUNCS__.func_65((bit_tobit(reg2 + reg16)),48,(bit_tobit(reg17 - reg16)));
                                                                        goto block_12_fin;
                                                                    ::block_1122_fin::
                                                                    __MEMORY_WRITE_32__(mem_0,reg6+8,reg9);
                                                                    reg12 = reg9;
                                                                    reg26 = 8
                                                                    -- BLOCK RET (block):
                                                                ::block_1121_fin::
                                                                reg31 = reg26;
                                                                
                                                                reg9 = ((((__UNSIGNED__(reg12) > __UNSIGNED__(reg29)) and 1 or 0) == 0) and reg29 or reg12);
                                                                if ((__UNSIGNED__(reg9) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_10_fin; end;
                                                                reg5 = (bit_lshift(reg9,2));
                                                                
                                                                while true do ::loop_1379_start::
                                                                    
                                                                        if ((reg5 == 0) and 1 or 0)==0 then goto if_1383_fin end 
                                                                            
                                                                            reg11 = ((reg5 == 0) and 0 or -1);
                                                                            goto block_1380_fin;
                                                                        ::if_1383_fin::
                                                                        reg11 = (bit_tobit((bit_tobit(reg6 + 512)) + reg5));
                                                                        reg8 = (bit_tobit((bit_tobit(reg6 + 8)) + reg5));
                                                                        reg26 = bit_tobit(reg5 + -4);
                                                                        reg5 = reg26;
                                                                        reg26 = __MEMORY_READ_32__(mem_0,reg8);
                                                                        reg8 = reg26;
                                                                        reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                                        reg11 = reg26;
                                                                        
                                                                        reg26 = (((__UNSIGNED__(reg8) < __UNSIGNED__(reg11)) and 1 or 0) == 0) and ((reg8 ~= reg11) and 1 or 0) or -1;
                                                                        reg11 = reg26;
                                                                        if ((reg11 == 0) and 1 or 0)~=0 then goto loop_1379_start; end;
                                                                    ::block_1380_fin::
                                                                    break
                                                                end
                                                                
                                                                if ((__UNSIGNED__((bit_band(reg11,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1429_fin end 
                                                                    reg9 = reg12;
                                                                    goto block_1104_fin;
                                                                ::if_1429_fin::
                                                                if reg9==0 then goto if_1435_fin end 
                                                                    reg20 = 1;
                                                                    reg12 = 0;
                                                                    if ((reg9 ~= 1) and 1 or 0)==0 then goto if_1443_fin end 
                                                                        reg33 = (bit_band(reg9,-2));
                                                                        reg11 = reg22;
                                                                        reg5 = reg15;
                                                                        
                                                                        while true do ::loop_1452_start::
                                                                            reg8 = (bit_tobit(reg5 + -4));
                                                                            reg26 = __MEMORY_READ_32__(mem_0,reg8);
                                                                            reg32 = reg26;
                                                                            reg26 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + -4)));
                                                                            reg34 = reg8;
                                                                            reg8 = (bit_tobit(reg32 + (bit_bxor(reg26,-1))));
                                                                            reg35 = (bit_tobit(reg8 + reg20));
                                                                            __MEMORY_WRITE_32__(mem_0,reg34,reg35);
                                                                            reg26 = __MEMORY_READ_32__(mem_0,reg5);
                                                                            reg34 = reg26;
                                                                            reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                                            reg20 = (bit_tobit(reg34 + (bit_bxor(reg26,-1))));
                                                                            reg26 = bit_tobit(reg20 + (bit_bor(((__UNSIGNED__(reg8) < __UNSIGNED__(reg32)) and 1 or 0),((__UNSIGNED__(reg35) < __UNSIGNED__(reg8)) and 1 or 0))));
                                                                            reg8 = reg26;
                                                                            __MEMORY_WRITE_32__(mem_0,reg5,reg8);
                                                                            reg26 = bit_bor(((__UNSIGNED__(reg20) < __UNSIGNED__(reg34)) and 1 or 0),((__UNSIGNED__(reg8) < __UNSIGNED__(reg20)) and 1 or 0));
                                                                            reg20 = reg26;
                                                                            reg26 = bit_tobit(reg11 + 8);
                                                                            reg11 = reg26;
                                                                            reg26 = bit_tobit(reg5 + 8);
                                                                            reg5 = reg26;
                                                                            reg26 = bit_tobit(reg12 + 2);
                                                                            reg12 = reg26;
                                                                            if ((reg33 ~= reg12) and 1 or 0)~=0 then goto loop_1452_start; end;
                                                                            break
                                                                        end
                                                                        
                                                                    ::if_1443_fin::
                                                                    if (bit_band(reg9,1))==0 then goto if_1520_else end 
                                                                        reg5 = (bit_lshift(reg12,2));
                                                                        reg11 = (bit_tobit((bit_tobit(reg6 + reg5)) + 12));
                                                                        reg36 = __MEMORY_READ_32__(mem_0,reg11);
                                                                        reg37 = reg11;
                                                                        reg11 = reg36;
                                                                        reg36 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg5 + reg24)) + 4)));
                                                                        reg5 = (bit_tobit(reg11 + (bit_bxor(reg36,-1))));
                                                                        reg12 = (bit_tobit(reg5 + reg20));
                                                                        __MEMORY_WRITE_32__(mem_0,reg37,reg12);
                                                                        reg26 = (bit_bor(((__UNSIGNED__(reg5) < __UNSIGNED__(reg11)) and 1 or 0),((__UNSIGNED__(reg12) < __UNSIGNED__(reg5)) and 1 or 0)))
                                                                    goto if_1520_fin
                                                                    ::if_1520_else::
                                                                        reg26 = reg20
                                                                        -- BLOCK RET (if):
                                                                    ::if_1520_fin::
                                                                    if ((reg26 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                                ::if_1435_fin::
                                                                __MEMORY_WRITE_32__(mem_0,reg6+8,reg9);
                                                                reg26 = bit_bor(reg31,4);
                                                                reg31 = reg26;
                                                                goto block_1104_fin;
                                                            ::if_1110_fin::
                                                            goto block_8_fin;
                                                        ::block_1106_fin::
                                                        __FUNCS__.func_85(reg16,reg17,1052820);
                                                        error('unreachable');
                                                    ::block_1105_fin::
                                                    __FUNCS__.func_84(reg17,reg3,1052820);
                                                    error('unreachable');
                                                ::block_1104_fin::
                                                
                                                    
                                                    reg8 = ((((__UNSIGNED__(reg9) > __UNSIGNED__(reg28)) and 1 or 0) == 0) and reg28 or reg9);
                                                    if ((__UNSIGNED__(reg8) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_1592_fin end 
                                                        reg5 = (bit_lshift(reg8,2));
                                                        
                                                        while true do ::loop_1597_start::
                                                            
                                                                if ((reg5 == 0) and 1 or 0)==0 then goto if_1601_fin end 
                                                                    
                                                                    reg11 = ((reg5 == 0) and 0 or -1);
                                                                    goto block_1598_fin;
                                                                ::if_1601_fin::
                                                                reg11 = (bit_tobit((bit_tobit(reg6 + 344)) + reg5));
                                                                reg12 = (bit_tobit((bit_tobit(reg6 + 8)) + reg5));
                                                                reg26 = bit_tobit(reg5 + -4);
                                                                reg5 = reg26;
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg12);
                                                                reg12 = reg26;
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                                reg11 = reg26;
                                                                
                                                                reg26 = (((__UNSIGNED__(reg12) < __UNSIGNED__(reg11)) and 1 or 0) == 0) and ((reg12 ~= reg11) and 1 or 0) or -1;
                                                                reg11 = reg26;
                                                                if ((reg11 == 0) and 1 or 0)~=0 then goto loop_1597_start; end;
                                                            ::block_1598_fin::
                                                            break
                                                        end
                                                        
                                                        if ((__UNSIGNED__((bit_band(reg11,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1647_fin end 
                                                            reg8 = reg9;
                                                            goto block_1582_fin;
                                                        ::if_1647_fin::
                                                        if reg8==0 then goto if_1653_fin end 
                                                            reg20 = 1;
                                                            reg12 = 0;
                                                            if ((reg8 ~= 1) and 1 or 0)==0 then goto if_1661_fin end 
                                                                reg33 = (bit_band(reg8,-2));
                                                                reg11 = reg21;
                                                                reg5 = reg15;
                                                                
                                                                while true do ::loop_1670_start::
                                                                    reg9 = (bit_tobit(reg5 + -4));
                                                                    reg26 = __MEMORY_READ_32__(mem_0,reg9);
                                                                    reg32 = reg26;
                                                                    reg26 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + -4)));
                                                                    reg36 = reg9;
                                                                    reg9 = (bit_tobit(reg32 + (bit_bxor(reg26,-1))));
                                                                    reg35 = (bit_tobit(reg9 + reg20));
                                                                    __MEMORY_WRITE_32__(mem_0,reg36,reg35);
                                                                    reg26 = __MEMORY_READ_32__(mem_0,reg5);
                                                                    reg34 = reg26;
                                                                    reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                                    reg20 = (bit_tobit(reg34 + (bit_bxor(reg26,-1))));
                                                                    reg26 = bit_tobit(reg20 + (bit_bor(((__UNSIGNED__(reg9) < __UNSIGNED__(reg32)) and 1 or 0),((__UNSIGNED__(reg35) < __UNSIGNED__(reg9)) and 1 or 0))));
                                                                    reg9 = reg26;
                                                                    __MEMORY_WRITE_32__(mem_0,reg5,reg9);
                                                                    reg26 = bit_bor(((__UNSIGNED__(reg20) < __UNSIGNED__(reg34)) and 1 or 0),((__UNSIGNED__(reg9) < __UNSIGNED__(reg20)) and 1 or 0));
                                                                    reg20 = reg26;
                                                                    reg26 = bit_tobit(reg11 + 8);
                                                                    reg11 = reg26;
                                                                    reg26 = bit_tobit(reg5 + 8);
                                                                    reg5 = reg26;
                                                                    reg26 = bit_tobit(reg12 + 2);
                                                                    reg12 = reg26;
                                                                    if ((reg33 ~= reg12) and 1 or 0)~=0 then goto loop_1670_start; end;
                                                                    break
                                                                end
                                                                
                                                            ::if_1661_fin::
                                                            if (bit_band(reg8,1))==0 then goto if_1738_else end 
                                                                reg5 = (bit_lshift(reg12,2));
                                                                reg11 = (bit_tobit((bit_tobit(reg6 + reg5)) + 12));
                                                                reg36 = __MEMORY_READ_32__(mem_0,reg11);
                                                                reg37 = reg11;
                                                                reg11 = reg36;
                                                                reg36 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg5 + reg23)) + 4)));
                                                                reg5 = (bit_tobit(reg11 + (bit_bxor(reg36,-1))));
                                                                reg12 = (bit_tobit(reg5 + reg20));
                                                                __MEMORY_WRITE_32__(mem_0,reg37,reg12);
                                                                reg26 = (bit_bor(((__UNSIGNED__(reg5) < __UNSIGNED__(reg11)) and 1 or 0),((__UNSIGNED__(reg12) < __UNSIGNED__(reg5)) and 1 or 0)))
                                                            goto if_1738_fin
                                                            ::if_1738_else::
                                                                reg26 = reg20
                                                                -- BLOCK RET (if):
                                                            ::if_1738_fin::
                                                            if ((reg26 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                        ::if_1653_fin::
                                                        __MEMORY_WRITE_32__(mem_0,reg6+8,reg8);
                                                        reg26 = bit_tobit(reg31 + 2);
                                                        reg31 = reg26;
                                                        goto block_1582_fin;
                                                    ::if_1592_fin::
                                                    __FUNCS__.func_84(reg8,40,1058148);
                                                    error('unreachable');
                                                ::block_1582_fin::
                                                
                                                reg12 = ((((__UNSIGNED__(reg8) > __UNSIGNED__(reg13)) and 1 or 0) == 0) and reg13 or reg8);
                                                if ((__UNSIGNED__(reg12) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_8_fin; end;
                                                reg5 = (bit_lshift(reg12,2));
                                                
                                                while true do ::loop_1806_start::
                                                    
                                                        if ((reg5 == 0) and 1 or 0)==0 then goto if_1810_fin end 
                                                            
                                                            reg11 = ((reg5 == 0) and 0 or -1);
                                                            goto block_1807_fin;
                                                        ::if_1810_fin::
                                                        reg11 = (bit_tobit((bit_tobit(reg6 + 176)) + reg5));
                                                        reg9 = (bit_tobit((bit_tobit(reg6 + 8)) + reg5));
                                                        reg26 = bit_tobit(reg5 + -4);
                                                        reg5 = reg26;
                                                        reg26 = __MEMORY_READ_32__(mem_0,reg9);
                                                        reg9 = reg26;
                                                        reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                        reg11 = reg26;
                                                        
                                                        reg26 = (((__UNSIGNED__(reg9) < __UNSIGNED__(reg11)) and 1 or 0) == 0) and ((reg9 ~= reg11) and 1 or 0) or -1;
                                                        reg11 = reg26;
                                                        if ((reg11 == 0) and 1 or 0)~=0 then goto loop_1806_start; end;
                                                    ::block_1807_fin::
                                                    break
                                                end
                                                
                                                
                                                    if ((__UNSIGNED__((bit_band(reg11,255))) >= __UNSIGNED__(2)) and 1 or 0)==0 then goto if_1857_fin end 
                                                        reg12 = reg8;
                                                        goto block_1851_fin;
                                                    ::if_1857_fin::
                                                    if reg12==0 then goto if_1863_fin end 
                                                        reg20 = 1;
                                                        reg9 = 0;
                                                        if ((reg12 ~= 1) and 1 or 0)==0 then goto if_1871_fin end 
                                                            reg33 = (bit_band(reg12,-2));
                                                            reg11 = reg18;
                                                            reg5 = reg15;
                                                            
                                                            while true do ::loop_1880_start::
                                                                reg8 = (bit_tobit(reg5 + -4));
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg8);
                                                                reg32 = reg26;
                                                                reg26 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + -4)));
                                                                reg36 = reg8;
                                                                reg8 = (bit_tobit(reg32 + (bit_bxor(reg26,-1))));
                                                                reg35 = (bit_tobit(reg8 + reg20));
                                                                __MEMORY_WRITE_32__(mem_0,reg36,reg35);
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg5);
                                                                reg34 = reg26;
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg11);
                                                                reg20 = (bit_tobit(reg34 + (bit_bxor(reg26,-1))));
                                                                reg26 = bit_tobit(reg20 + (bit_bor(((__UNSIGNED__(reg8) < __UNSIGNED__(reg32)) and 1 or 0),((__UNSIGNED__(reg35) < __UNSIGNED__(reg8)) and 1 or 0))));
                                                                reg8 = reg26;
                                                                __MEMORY_WRITE_32__(mem_0,reg5,reg8);
                                                                reg26 = bit_bor(((__UNSIGNED__(reg20) < __UNSIGNED__(reg34)) and 1 or 0),((__UNSIGNED__(reg8) < __UNSIGNED__(reg20)) and 1 or 0));
                                                                reg20 = reg26;
                                                                reg26 = bit_tobit(reg11 + 8);
                                                                reg11 = reg26;
                                                                reg26 = bit_tobit(reg5 + 8);
                                                                reg5 = reg26;
                                                                reg26 = bit_tobit(reg9 + 2);
                                                                reg9 = reg26;
                                                                if ((reg33 ~= reg9) and 1 or 0)~=0 then goto loop_1880_start; end;
                                                                break
                                                            end
                                                            
                                                        ::if_1871_fin::
                                                        if (bit_band(reg12,1))==0 then goto if_1948_else end 
                                                            reg5 = (bit_lshift(reg9,2));
                                                            reg11 = (bit_tobit((bit_tobit(reg6 + reg5)) + 12));
                                                            reg32 = __MEMORY_READ_32__(mem_0,reg11);
                                                            reg34 = reg11;
                                                            reg11 = reg32;
                                                            reg32 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg5 + reg6)) + 180)));
                                                            reg5 = (bit_tobit(reg11 + (bit_bxor(reg32,-1))));
                                                            reg9 = (bit_tobit(reg5 + reg20));
                                                            __MEMORY_WRITE_32__(mem_0,reg34,reg9);
                                                            reg26 = (bit_bor(((__UNSIGNED__(reg5) < __UNSIGNED__(reg11)) and 1 or 0),((__UNSIGNED__(reg9) < __UNSIGNED__(reg5)) and 1 or 0)))
                                                        goto if_1948_fin
                                                        ::if_1948_else::
                                                            reg26 = reg20
                                                            -- BLOCK RET (if):
                                                        ::if_1948_fin::
                                                        if ((reg26 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                                    ::if_1863_fin::
                                                    __MEMORY_WRITE_32__(mem_0,reg6+8,reg12);
                                                    reg26 = bit_tobit(reg31 + 1);
                                                    reg31 = reg26;
                                                ::block_1851_fin::
                                                if ((reg3 == reg16) and 1 or 0)~=0 then goto block_1100_fin; end;
                                                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg16)),(bit_tobit(reg31 + 48)));
                                                if ((__UNSIGNED__(reg12) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_8_fin; end;
                                                
                                                    if ((reg12 == 0) and 1 or 0)==0 then goto if_2013_fin end 
                                                        reg12 = 0;
                                                        goto block_2010_fin;
                                                    ::if_2013_fin::
                                                    reg8 = (bit_lshift(reg12,2));
                                                    reg11 = (bit_tobit(reg8 + -4));
                                                    reg16 = (bit_tobit((bit_rshift(reg11,2)) + 1));
                                                    reg9 = (bit_band(reg16,3));
                                                    reg7 = __LONG_INT__(0,0);
                                                    reg5 = reg14;
                                                    if ((__UNSIGNED__(reg11) >= __UNSIGNED__(12)) and 1 or 0)==0 then goto if_2040_fin end 
                                                        reg11 = (bit_tobit(0 - (bit_band(reg16,2147483644))));
                                                        
                                                        while true do ::loop_2047_start::
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg5);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(10,0)) + reg7;
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg5);
                                                            reg16 = (bit_tobit(reg5 + 4));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg16);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg16);
                                                            reg16 = (bit_tobit(reg5 + 8));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg16);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg16);
                                                            reg16 = (bit_tobit(reg5 + 12));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg16);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(10,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg16);
                                                            reg26 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                            reg7 = reg26;
                                                            reg26 = bit_tobit(reg5 + 16);
                                                            reg5 = reg26;
                                                            reg26 = bit_tobit(reg11 + 4);
                                                            reg11 = reg26;
                                                            if reg11~=0 then goto loop_2047_start; end;
                                                            break
                                                        end
                                                        
                                                    ::if_2040_fin::
                                                    if reg9==0 then goto if_2115_fin end 
                                                        reg11 = (bit_tobit(0 - reg9));
                                                        
                                                        while true do ::loop_2120_start::
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg5);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(10,0)) + reg7;
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg5);
                                                            reg26 = bit_tobit(reg5 + 4);
                                                            reg5 = reg26;
                                                            reg26 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                            reg7 = reg26;
                                                            reg9 = (bit_tobit(reg11 + 1));
                                                            reg26 = (__UNSIGNED__(reg9) >= __UNSIGNED__(reg11)) and 1 or 0;
                                                            reg11 = reg9;
                                                            if reg26~=0 then goto loop_2120_start; end;
                                                            break
                                                        end
                                                        
                                                    ::if_2115_fin::
                                                    reg5 = ((reg7)[1]);
                                                    if ((reg5 == 0) and 1 or 0)~=0 then goto block_2010_fin; end;
                                                    if ((__UNSIGNED__(reg12) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_1099_fin; end;
                                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg6 + reg8)) + 12)),reg5);
                                                    reg26 = bit_tobit(reg12 + 1);
                                                    reg12 = reg26;
                                                ::block_2010_fin::
                                                __MEMORY_WRITE_32__(mem_0,reg6+8,reg12);
                                                if ((reg17 ~= reg19) and 1 or 0)~=0 then goto loop_1101_start; end;
                                                break
                                            end
                                            
                                            reg20 = 0;
                                            goto block_13_fin;
                                        ::block_1100_fin::
                                        __FUNCS__.func_82(reg3,reg3,1052836);
                                        error('unreachable');
                                    ::block_1099_fin::
                                    __FUNCS__.func_82(reg12,40,1058148);
                                    error('unreachable');
                                ::block_14_fin::
                                __FUNCS__.func_82(reg9,40,1058148);
                                error('unreachable');
                            ::block_13_fin::
                            
                                
                                    
                                        
                                            
                                                
                                                    if ((__UNSIGNED__(reg13) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_2209_fin end 
                                                        if ((reg13 == 0) and 1 or 0)==0 then goto if_2212_fin end 
                                                            reg13 = 0;
                                                            goto block_2204_fin;
                                                        ::if_2212_fin::
                                                        reg14 = (bit_lshift(reg13,2));
                                                        reg5 = (bit_tobit(reg14 + -4));
                                                        reg15 = (bit_tobit((bit_rshift(reg5,2)) + 1));
                                                        reg11 = (bit_band(reg15,3));
                                                        if ((__UNSIGNED__(reg5) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_2235_fin end 
                                                            reg7 = __LONG_INT__(0,0);
                                                            goto block_2205_fin;
                                                        ::if_2235_fin::
                                                        reg5 = (bit_tobit(0 - (bit_band(reg15,2147483644))));
                                                        reg7 = __LONG_INT__(0,0);
                                                        
                                                        while true do ::loop_2248_start::
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg1);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(5,0)) + reg7;
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg1);
                                                            reg15 = (bit_tobit(reg1 + 4));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg15);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(5,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg15);
                                                            reg15 = (bit_tobit(reg1 + 8));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg15);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(5,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg15);
                                                            reg15 = (bit_tobit(reg1 + 12));
                                                            reg26 = __MEMORY_READ_32__(mem_0,reg15);reg26=__LONG_INT__(reg26,0);
                                                            reg32 = (reg26 * __LONG_INT__(5,0)) + ((reg7):_shr_u(__LONG_INT__(32,0)));
                                                            reg7 = reg32;
                                                            (reg7):store32(mem_0,reg15);
                                                            reg26 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                            reg7 = reg26;
                                                            reg26 = bit_tobit(reg1 + 16);
                                                            reg1 = reg26;
                                                            reg26 = bit_tobit(reg5 + 4);
                                                            reg5 = reg26;
                                                            if reg5~=0 then goto loop_2248_start; end;
                                                            break
                                                        end
                                                        
                                                        goto block_2205_fin;
                                                    ::if_2209_fin::
                                                    __FUNCS__.func_84(reg13,40,1058148);
                                                    error('unreachable');
                                                ::block_2205_fin::
                                                if reg11==0 then goto if_2323_fin end 
                                                    reg5 = (bit_tobit(0 - reg11));
                                                    
                                                    while true do ::loop_2328_start::
                                                        reg26 = __MEMORY_READ_32__(mem_0,reg1);reg26=__LONG_INT__(reg26,0);
                                                        reg32 = (reg26 * __LONG_INT__(5,0)) + reg7;
                                                        reg7 = reg32;
                                                        (reg7):store32(mem_0,reg1);
                                                        reg26 = bit_tobit(reg1 + 4);
                                                        reg1 = reg26;
                                                        reg26 = (reg7):_shr_u(__LONG_INT__(32,0));
                                                        reg7 = reg26;
                                                        reg11 = (bit_tobit(reg5 + 1));
                                                        reg26 = (__UNSIGNED__(reg11) >= __UNSIGNED__(reg5)) and 1 or 0;
                                                        reg5 = reg11;
                                                        if reg26~=0 then goto loop_2328_start; end;
                                                        break
                                                    end
                                                    
                                                ::if_2323_fin::
                                                reg1 = ((reg7)[1]);
                                                if ((reg1 == 0) and 1 or 0)~=0 then goto block_2204_fin; end;
                                                if ((__UNSIGNED__(reg13) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_2203_fin; end;
                                                __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg6 + reg14)) + 180)),reg1);
                                                reg7 = bit_tobit(reg13 + 1);
                                                reg13 = reg7;
                                            ::block_2204_fin::
                                            __MEMORY_WRITE_32__(mem_0,reg6+176,reg13);
                                            reg7 = __MEMORY_READ_32__(mem_0,reg6+8);
                                            reg1 = reg7;
                                            
                                            reg7 = (((__UNSIGNED__(reg1) > __UNSIGNED__(reg13)) and 1 or 0) == 0) and reg13 or reg1;
                                            reg1 = reg7;
                                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_11_fin; end;
                                            reg7 = bit_lshift(reg1,2);
                                            reg1 = reg7;
                                            
                                                
                                                while true do ::loop_2398_start::
                                                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_2397_fin; end;
                                                    reg5 = (bit_tobit((bit_tobit(reg6 + 176)) + reg1));
                                                    reg11 = (bit_tobit((bit_tobit(reg6 + 8)) + reg1));
                                                    reg7 = bit_tobit(reg1 + -4);
                                                    reg1 = reg7;
                                                    reg7 = __MEMORY_READ_32__(mem_0,reg11);
                                                    reg11 = reg7;
                                                    reg7 = __MEMORY_READ_32__(mem_0,reg5);
                                                    reg5 = reg7;
                                                    
                                                    reg7 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg5)) and 1 or 0) == 0) and ((reg11 ~= reg5) and 1 or 0) or -1;
                                                    reg5 = reg7;
                                                    if ((reg5 == 0) and 1 or 0)~=0 then goto loop_2398_start; end;
                                                    break
                                                end
                                                
                                                if (((bit_band(reg5,255)) ~= 1) and 1 or 0)~=0 then goto block_2200_fin; end;
                                                goto block_2201_fin;
                                            ::block_2397_fin::
                                            if reg1~=0 then goto block_2200_fin; end;
                                            if reg20~=0 then goto block_2201_fin; end;
                                            reg1 = (bit_tobit(reg17 + -1));
                                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_2202_fin; end;
                                            reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + reg2)));
                                            if (bit_band(reg7,1))~=0 then goto block_2201_fin; end;
                                            goto block_2200_fin;
                                        ::block_2203_fin::
                                        __FUNCS__.func_82(reg13,40,1058148);
                                        error('unreachable');
                                    ::block_2202_fin::
                                    __FUNCS__.func_82(reg1,reg3,1052852);
                                    error('unreachable');
                                ::block_2201_fin::
                                if ((__UNSIGNED__(reg17) <= __UNSIGNED__(reg3)) and 1 or 0)==0 then goto if_2477_fin end 
                                    reg1 = 0;
                                    reg5 = reg2;
                                    
                                        
                                        while true do ::loop_2486_start::
                                            if ((reg1 == reg17) and 1 or 0)~=0 then goto block_2485_fin; end;
                                            reg7 = bit_tobit(reg1 + 1);
                                            reg1 = reg7;
                                            reg15 = (bit_tobit(reg5 + -1));
                                            reg7 = bit_tobit(reg5 + reg17);
                                            reg5 = reg15;
                                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg7 + -1)));
                                            if ((reg11 == 57) and 1 or 0)~=0 then goto loop_2486_start; end;
                                            break
                                        end
                                        
                                        reg4 = (bit_tobit(reg15 + reg17));
                                        reg7 = __MEMORY_READ_8__(mem_0,reg4);
                                        __MEMORY_WRITE_8__(mem_0,reg4,(bit_tobit(reg7 + 1)));
                                        if ((__UNSIGNED__(reg17) <= __UNSIGNED__((bit_tobit((bit_tobit(reg17 - reg1)) + 1)))) and 1 or 0)~=0 then goto block_2200_fin; end;
                                        reg7 = __FUNCS__.func_65((bit_tobit(reg4 + 1)),48,(bit_tobit(reg1 + -1)));
                                        goto block_2200_fin;
                                    ::block_2485_fin::
                                    
                                        if reg20~=0 then reg7 = 49; goto block_2538_fin; end;
                                        __MEMORY_WRITE_8__(mem_0,reg2,49);
                                        if ((reg17 == 1) and 1 or 0)~=0 then reg7 = 48; goto block_2538_fin; end;
                                        reg11 = __FUNCS__.func_65((bit_tobit(reg2 + 1)),48,(bit_tobit(reg17 + -1)));
                                        reg7 = 48
                                        -- BLOCK RET (block):
                                    ::block_2538_fin::
                                    reg11 = bit_arshift((bit_tobit((bit_lshift(reg10,16)) + 65536)),16);
                                    reg10 = reg11;
                                    if (bit_bor(((reg10 <= (bit_arshift((bit_lshift(reg4,16)),16))) and 1 or 0),((__UNSIGNED__(reg17) >= __UNSIGNED__(reg3)) and 1 or 0)))~=0 then goto block_2200_fin; end;
                                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg17)),reg7);
                                    reg4 = bit_tobit(reg17 + 1);
                                    reg17 = reg4;
                                    goto block_2200_fin;
                                ::if_2477_fin::
                                __FUNCS__.func_84(reg17,reg3,1052868);
                                error('unreachable');
                            ::block_2200_fin::
                            if ((__UNSIGNED__(reg17) <= __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_12_fin; end;
                            __FUNCS__.func_84(reg17,reg3,1052884);
                            error('unreachable');
                        ::block_12_fin::
                        __MEMORY_WRITE_16__(mem_0,reg0+8,reg10);
                        __MEMORY_WRITE_32__(mem_0,reg0+4,reg17);
                        __MEMORY_WRITE_32__(mem_0,reg0,reg2);
                        __GLOBALS__[0] = (bit_tobit(reg6 + 848));
                        do return  end
                    ::block_11_fin::
                    __FUNCS__.func_84(reg1,40,1058148);
                    error('unreachable');
                ::block_10_fin::
                __FUNCS__.func_84(reg9,40,1058148);
                error('unreachable');
            ::block_9_fin::
            __FUNCS__.func_110(1058164,26,1058148);
            error('unreachable');
        ::block_8_fin::
        __FUNCS__.func_84(reg12,40,1058148);
        error('unreachable');
    end
    function __FUNCS__.func_2(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 16));
        __GLOBALS__[0] = reg2;
        
            
                if ((__UNSIGNED__(reg0) >= __UNSIGNED__(245)) and 1 or 0)==0 then goto if_13_fin end 
                    reg1 = __FUNCS__.func_174(0);
                    reg3 = reg1;
                    reg1 = __FUNCS__.func_143(reg3,8);
                    reg4 = __FUNCS__.func_143(20,8);
                    reg5 = __FUNCS__.func_143(16,8);
                    reg6 = (bit_tobit((bit_band((bit_tobit((bit_tobit(reg3 - (bit_tobit((bit_tobit(reg1 + reg4)) + reg5)))) + -65544)),-9)) + -3));
                    reg1 = __FUNCS__.func_143(16,8);
                    reg3 = (bit_tobit(0 - (bit_lshift(reg1,2))));
                    
                    if ((__UNSIGNED__(((((__UNSIGNED__(reg3) > __UNSIGNED__(reg6)) and 1 or 0) == 0) and reg3 or reg6)) <= __UNSIGNED__(reg0)) and 1 or 0)~=0 then goto block_8_fin; end;
                    reg1 = __FUNCS__.func_143((bit_tobit(reg0 + 4)),8);
                    reg4 = reg1;
                    reg1 = __MEMORY_READ_32__(mem_0,1059200);
                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                    reg1 = (bit_tobit(0 - reg4));
                    
                        
                            
                                if ((__UNSIGNED__(reg4) < __UNSIGNED__(256)) and 1 or 0)~=0 then reg5 = 0; goto block_67_fin; end;
                                if ((__UNSIGNED__(reg4) > __UNSIGNED__(16777215)) and 1 or 0)~=0 then reg5 = 31; goto block_67_fin; end;
                                reg0 = (__CLZ__((bit_rshift(reg4,8))));
                                reg5 = (bit_tobit((bit_tobit((bit_band((bit_rshift(reg4,(bit_tobit(6 - reg0)))),1)) - (bit_lshift(reg0,1)))) + 62))
                                -- BLOCK RET (block):
                            ::block_67_fin::
                            reg7 = reg5;
                            reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift(reg7,2)) + 1059468)));
                            reg0 = reg5;
                            if reg0==0 then goto if_105_fin end 
                                reg5 = __FUNCS__.func_139(reg7);
                                reg8 = (bit_lshift(reg4,reg5));
                                reg3 = 0;
                                -- FORCE INIT VAR | i32
                                reg5 = 0;
                                -- FORCE INIT VAR | i32
                                reg5 = 0;
                                
                                while true do ::loop_113_start::
                                    
                                        reg9 = __FUNCS__.func_166(reg0);
                                        reg6 = reg9;
                                        if ((__UNSIGNED__(reg6) < __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_114_fin; end;
                                        reg9 = bit_tobit(reg6 - reg4);
                                        reg6 = reg9;
                                        if ((__UNSIGNED__(reg6) >= __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_114_fin; end;
                                        reg3 = reg0;
                                        reg1 = reg6;
                                        if reg1~=0 then goto block_114_fin; end;
                                        reg1 = 0;
                                        goto block_66_fin;
                                    ::block_114_fin::
                                    reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
                                    reg6 = reg9;
                                    reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg0 + (bit_band((bit_rshift(reg8,29)),4)))) + 16)));
                                    reg0 = reg9;
                                    
                                    
                                    reg9 = (reg6 == 0) and reg5 or ((((reg6 ~= reg0) and 1 or 0) == 0) and reg5 or reg6);
                                    reg5 = reg9;
                                    reg9 = bit_lshift(reg8,1);
                                    reg8 = reg9;
                                    if reg0~=0 then goto loop_113_start; end;
                                    break
                                end
                                
                                if reg5==0 then goto if_169_fin end 
                                    reg0 = reg5;
                                    goto block_66_fin;
                                ::if_169_fin::
                                if reg3~=0 then goto block_65_fin; end;
                            ::if_105_fin::
                            reg3 = 0;
                            reg9 = __FUNCS__.func_146((bit_lshift(1,reg7)));
                            reg10 = __MEMORY_READ_32__(mem_0,1059200);
                            reg0 = (bit_band(reg9,reg10));
                            if ((reg0 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                            reg9 = __FUNCS__.func_155(reg0);
                            reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift((__CTZ__(reg9)),2)) + 1059468)));
                            reg0 = reg10;
                            if ((reg0 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                        ::block_66_fin::
                        
                        while true do ::loop_201_start::
                            reg9 = __FUNCS__.func_166(reg0);
                            reg10 = reg3;
                            reg3 = reg9;
                            reg5 = (bit_tobit(reg3 - reg4));
                            reg6 = (bit_band(((__UNSIGNED__(reg3) >= __UNSIGNED__(reg4)) and 1 or 0),((__UNSIGNED__(reg5) < __UNSIGNED__(reg1)) and 1 or 0)));
                            
                            reg3 = ((reg6 == 0) and reg10 or reg0);
                            
                            reg9 = (reg6 == 0) and reg1 or reg5;
                            reg1 = reg9;
                            reg9 = __FUNCS__.func_138(reg0);
                            reg0 = reg9;
                            if reg0~=0 then goto loop_201_start; end;
                            break
                        end
                        
                        if ((reg3 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                    ::block_65_fin::
                    reg9 = __MEMORY_READ_32__(mem_0,1059596);
                    reg0 = reg9;
                    
                    if ((((__UNSIGNED__(reg1) >= __UNSIGNED__((bit_tobit(reg0 - reg4)))) and 1 or 0) == 0) and 0 or ((__UNSIGNED__(reg0) >= __UNSIGNED__(reg4)) and 1 or 0))~=0 then goto block_9_fin; end;
                    reg0 = reg3;
                    reg9 = __FUNCS__.func_172(reg0,reg4);
                    reg7 = reg9;
                    __FUNCS__.func_54(reg0);
                    
                        reg9 = __FUNCS__.func_143(16,8);
                        if ((__UNSIGNED__(reg1) >= __UNSIGNED__(reg9)) and 1 or 0)==0 then goto if_259_fin end 
                            __FUNCS__.func_157(reg0,reg4);
                            __FUNCS__.func_140(reg7,reg1);
                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_269_fin end 
                                __FUNCS__.func_52(reg7,reg1);
                                goto block_253_fin;
                            ::if_269_fin::
                            reg3 = (bit_rshift(reg1,3));
                            reg5 = (bit_tobit((bit_lshift(reg3,3)) + 1059204));
                            
                                reg10 = __MEMORY_READ_32__(mem_0,1059196);
                                reg6 = reg10;
                                reg10 = bit_lshift(1,reg3);
                                reg3 = reg10;
                                if (bit_band(reg6,reg3))==0 then goto if_293_fin end 
                                    reg10 = __MEMORY_READ_32__(mem_0,reg5+8);
                                    reg9 = reg10; goto block_284_fin;
                                ::if_293_fin::
                                __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg3,reg6)));
                                reg9 = reg5
                                -- BLOCK RET (block):
                            ::block_284_fin::
                            reg3 = reg9;
                            __MEMORY_WRITE_32__(mem_0,reg5+8,reg7);
                            __MEMORY_WRITE_32__(mem_0,reg3+12,reg7);
                            __MEMORY_WRITE_32__(mem_0,reg7+12,reg5);
                            __MEMORY_WRITE_32__(mem_0,reg7+8,reg3);
                            goto block_253_fin;
                        ::if_259_fin::
                        __FUNCS__.func_130(reg0,(bit_tobit(reg1 + reg4)));
                    ::block_253_fin::
                    reg9 = __FUNCS__.func_174(reg0);
                    reg1 = reg9;
                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                    goto block_8_fin;
                ::if_13_fin::
                reg9 = __FUNCS__.func_143(16,8);
                
                reg10 = __FUNCS__.func_143(((((__UNSIGNED__((bit_tobit(reg9 + -5))) > __UNSIGNED__(reg0)) and 1 or 0) == 0) and (bit_tobit(reg0 + 4)) or 16),8);
                reg4 = reg10;
                
                    
                        
                            
                                
                                    
                                        reg10 = __MEMORY_READ_32__(mem_0,1059196);
                                        reg3 = reg10;
                                        reg0 = (bit_rshift(reg4,3));
                                        reg6 = (bit_rshift(reg3,reg0));
                                        if (((bit_band(reg6,3)) == 0) and 1 or 0)==0 then goto if_366_fin end 
                                            reg10 = __MEMORY_READ_32__(mem_0,1059596);
                                            if ((__UNSIGNED__(reg4) <= __UNSIGNED__(reg10)) and 1 or 0)~=0 then goto block_9_fin; end;
                                            if reg6~=0 then goto block_353_fin; end;
                                            reg10 = __MEMORY_READ_32__(mem_0,1059200);
                                            reg0 = reg10;
                                            if ((reg0 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                            reg10 = __FUNCS__.func_155(reg0);
                                            reg11 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift((__CTZ__(reg10)),2)) + 1059468)));
                                            reg3 = reg11;
                                            reg10 = __FUNCS__.func_166(reg3);
                                            reg1 = (bit_tobit(reg10 - reg4));
                                            reg10 = __FUNCS__.func_138(reg3);
                                            reg0 = reg10;
                                            if reg0==0 then goto if_395_fin end 
                                                
                                                while true do ::loop_396_start::
                                                    reg10 = __FUNCS__.func_166(reg0);
                                                    reg6 = (bit_tobit(reg10 - reg4));
                                                    reg10 = (__UNSIGNED__(reg6) < __UNSIGNED__(reg1)) and 1 or 0;
                                                    reg11 = reg6;
                                                    reg6 = reg10;
                                                    
                                                    reg10 = (reg6 == 0) and reg1 or reg11;
                                                    reg1 = reg10;
                                                    
                                                    reg10 = (reg6 == 0) and reg3 or reg0;
                                                    reg3 = reg10;
                                                    reg10 = __FUNCS__.func_138(reg0);
                                                    reg0 = reg10;
                                                    if reg0~=0 then goto loop_396_start; end;
                                                    break
                                                end
                                                
                                            ::if_395_fin::
                                            reg0 = reg3;
                                            reg10 = __FUNCS__.func_172(reg0,reg4);
                                            reg5 = reg10;
                                            __FUNCS__.func_54(reg0);
                                            reg10 = __FUNCS__.func_143(16,8);
                                            if ((__UNSIGNED__(reg1) < __UNSIGNED__(reg10)) and 1 or 0)~=0 then goto block_349_fin; end;
                                            __FUNCS__.func_157(reg0,reg4);
                                            __FUNCS__.func_140(reg5,reg1);
                                            reg10 = __MEMORY_READ_32__(mem_0,1059596);
                                            reg3 = reg10;
                                            if ((reg3 == 0) and 1 or 0)~=0 then goto block_350_fin; end;
                                            reg10 = bit_rshift(reg3,3);
                                            reg3 = reg10;
                                            reg8 = (bit_tobit((bit_lshift(reg3,3)) + 1059204));
                                            reg10 = __MEMORY_READ_32__(mem_0,1059604);
                                            reg7 = reg10;
                                            reg10 = __MEMORY_READ_32__(mem_0,1059196);
                                            reg6 = reg10;
                                            reg10 = bit_lshift(1,reg3);
                                            reg3 = reg10;
                                            if (((bit_band(reg6,reg3)) == 0) and 1 or 0)~=0 then goto block_352_fin; end;
                                            reg10 = __MEMORY_READ_32__(mem_0,reg8+8);
                                            reg9 = reg10; goto block_351_fin;
                                        ::if_366_fin::
                                        
                                            reg1 = (bit_tobit((bit_band((bit_bxor(reg6,-1)),1)) + reg0));
                                            reg0 = (bit_lshift(reg1,3));
                                            reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 1059212)));
                                            reg5 = reg10;
                                            reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + 8)));
                                            reg6 = reg10;
                                            reg10 = bit_tobit(reg0 + 1059204);
                                            reg0 = reg10;
                                            if ((reg6 ~= reg0) and 1 or 0)==0 then goto if_495_fin end 
                                                __MEMORY_WRITE_32__(mem_0,reg6+12,reg0);
                                                __MEMORY_WRITE_32__(mem_0,reg0+8,reg6);
                                                goto block_470_fin;
                                            ::if_495_fin::
                                            __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg3,(bit_rol(-2,reg1)))));
                                        ::block_470_fin::
                                        __FUNCS__.func_130(reg5,(bit_lshift(reg1,3)));
                                        reg10 = __FUNCS__.func_174(reg5);
                                        reg1 = reg10;
                                        goto block_8_fin;
                                    ::block_353_fin::
                                    
                                        reg10 = bit_band(reg0,31);
                                        reg0 = reg10;
                                        reg10 = __FUNCS__.func_146((bit_lshift(1,reg0)));
                                        reg11 = __FUNCS__.func_155((bit_band(reg10,(bit_lshift(reg6,reg0)))));
                                        reg6 = (__CTZ__(reg11));
                                        reg0 = (bit_lshift(reg6,3));
                                        reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 1059212)));
                                        reg1 = reg10;
                                        reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 8)));
                                        reg3 = reg10;
                                        reg10 = bit_tobit(reg0 + 1059204);
                                        reg0 = reg10;
                                        if ((reg3 ~= reg0) and 1 or 0)==0 then goto if_553_fin end 
                                            __MEMORY_WRITE_32__(mem_0,reg3+12,reg0);
                                            __MEMORY_WRITE_32__(mem_0,reg0+8,reg3);
                                            goto block_522_fin;
                                        ::if_553_fin::
                                        reg10 = __MEMORY_READ_32__(mem_0,1059196);
                                        __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg10,(bit_rol(-2,reg6)))));
                                    ::block_522_fin::
                                    __FUNCS__.func_157(reg1,reg4);
                                    reg10 = __FUNCS__.func_172(reg1,reg4);
                                    reg5 = reg10;
                                    reg10 = bit_tobit((bit_lshift(reg6,3)) - reg4);
                                    reg6 = reg10;
                                    __FUNCS__.func_140(reg5,reg6);
                                    reg10 = __MEMORY_READ_32__(mem_0,1059596);
                                    reg0 = reg10;
                                    if reg0==0 then goto if_588_fin end 
                                        reg10 = bit_rshift(reg0,3);
                                        reg0 = reg10;
                                        reg8 = (bit_tobit((bit_lshift(reg0,3)) + 1059204));
                                        reg10 = __MEMORY_READ_32__(mem_0,1059604);
                                        reg7 = reg10;
                                        
                                            reg11 = __MEMORY_READ_32__(mem_0,1059196);
                                            reg3 = reg11;
                                            reg11 = bit_lshift(1,reg0);
                                            reg0 = reg11;
                                            if (bit_band(reg3,reg0))==0 then goto if_610_fin end 
                                                reg11 = __MEMORY_READ_32__(mem_0,reg8+8);
                                                reg10 = reg11; goto block_601_fin;
                                            ::if_610_fin::
                                            __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg0,reg3)));
                                            reg10 = reg8
                                            -- BLOCK RET (block):
                                        ::block_601_fin::
                                        reg0 = reg10;
                                        __MEMORY_WRITE_32__(mem_0,reg8+8,reg7);
                                        __MEMORY_WRITE_32__(mem_0,reg0+12,reg7);
                                        __MEMORY_WRITE_32__(mem_0,reg7+12,reg8);
                                        __MEMORY_WRITE_32__(mem_0,reg7+8,reg0);
                                    ::if_588_fin::
                                    __MEMORY_WRITE_32__(mem_0,1059604,reg5);
                                    __MEMORY_WRITE_32__(mem_0,1059596,reg6);
                                    reg10 = __FUNCS__.func_174(reg1);
                                    reg1 = reg10;
                                    goto block_8_fin;
                                ::block_352_fin::
                                __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg3,reg6)));
                                reg9 = reg8
                                -- BLOCK RET (block):
                            ::block_351_fin::
                            reg3 = reg9;
                            __MEMORY_WRITE_32__(mem_0,reg8+8,reg7);
                            __MEMORY_WRITE_32__(mem_0,reg3+12,reg7);
                            __MEMORY_WRITE_32__(mem_0,reg7+12,reg8);
                            __MEMORY_WRITE_32__(mem_0,reg7+8,reg3);
                        ::block_350_fin::
                        __MEMORY_WRITE_32__(mem_0,1059604,reg5);
                        __MEMORY_WRITE_32__(mem_0,1059596,reg1);
                        goto block_348_fin;
                    ::block_349_fin::
                    __FUNCS__.func_130(reg0,(bit_tobit(reg1 + reg4)));
                ::block_348_fin::
                reg9 = __FUNCS__.func_174(reg0);
                reg1 = reg9;
                if reg1~=0 then goto block_8_fin; end;
            ::block_9_fin::
            
                
                    
                        
                            
                                
                                    
                                        
                                            
                                                
                                                    reg9 = __MEMORY_READ_32__(mem_0,1059596);
                                                    reg0 = reg9;
                                                    if ((__UNSIGNED__(reg0) < __UNSIGNED__(reg4)) and 1 or 0)==0 then goto if_702_fin end 
                                                        reg9 = __MEMORY_READ_32__(mem_0,1059600);
                                                        reg0 = reg9;
                                                        if ((__UNSIGNED__(reg0) > __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_693_fin; end;
                                                        reg1 = 0;
                                                        reg9 = __FUNCS__.func_174(0);
                                                        reg0 = reg9;
                                                        reg9 = __FUNCS__.func_143(reg0,8);
                                                        reg10 = __FUNCS__.func_143(20,8);
                                                        reg11 = __FUNCS__.func_143(16,8);
                                                        reg12 = __FUNCS__.func_143((bit_tobit((bit_tobit((bit_tobit((bit_tobit((bit_tobit(reg4 - reg0)) + reg9)) + reg10)) + reg11)) + 8)),65536);
                                                        __FUNCS__.func_113(reg2,reg12);
                                                        reg9 = __MEMORY_READ_32__(mem_0,reg2);
                                                        reg10 = reg9;
                                                        if ((reg10 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                                                        reg9 = __MEMORY_READ_32__(mem_0,reg2+8);
                                                        reg11 = reg9;
                                                        reg9 = __MEMORY_READ_32__(mem_0,reg2+4);
                                                        reg12 = reg9;
                                                        reg9 = __MEMORY_READ_32__(mem_0,1059612);
                                                        reg3 = (bit_tobit(reg12 + reg9));
                                                        __MEMORY_WRITE_32__(mem_0,1059612,reg3);
                                                        reg9 = __MEMORY_READ_32__(mem_0,1059616);
                                                        reg0 = reg9;
                                                        
                                                        __MEMORY_WRITE_32__(mem_0,1059616,((((__UNSIGNED__(reg0) > __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg3 or reg0));
                                                        reg9 = __MEMORY_READ_32__(mem_0,1059608);
                                                        if ((reg9 == 0) and 1 or 0)~=0 then goto block_696_fin; end;
                                                        reg0 = 1059620;
                                                        
                                                        while true do ::loop_767_start::
                                                            reg9 = __FUNCS__.func_158(reg0);
                                                            if ((reg9 == reg10) and 1 or 0)~=0 then goto block_695_fin; end;
                                                            reg9 = __MEMORY_READ_32__(mem_0,reg0+8);
                                                            reg0 = reg9;
                                                            if reg0~=0 then goto loop_767_start; end;
                                                            break
                                                        end
                                                        
                                                        goto block_694_fin;
                                                    ::if_702_fin::
                                                    reg9 = __MEMORY_READ_32__(mem_0,1059604);
                                                    reg6 = reg9;
                                                    reg3 = (bit_tobit(reg0 - reg4));
                                                    reg9 = __FUNCS__.func_143(16,8);
                                                    if ((__UNSIGNED__(reg3) < __UNSIGNED__(reg9)) and 1 or 0)==0 then goto if_791_fin end 
                                                        __MEMORY_WRITE_32__(mem_0,1059604,0);
                                                        reg9 = __MEMORY_READ_32__(mem_0,1059596);
                                                        reg0 = reg9;
                                                        __MEMORY_WRITE_32__(mem_0,1059596,0);
                                                        __FUNCS__.func_130(reg6,reg0);
                                                        reg9 = __FUNCS__.func_174(reg6);
                                                        reg1 = reg9;
                                                        goto block_8_fin;
                                                    ::if_791_fin::
                                                    reg9 = __FUNCS__.func_172(reg6,reg4);
                                                    reg0 = reg9;
                                                    __MEMORY_WRITE_32__(mem_0,1059596,reg3);
                                                    __MEMORY_WRITE_32__(mem_0,1059604,reg0);
                                                    __FUNCS__.func_140(reg0,reg3);
                                                    __FUNCS__.func_157(reg6,reg4);
                                                    reg9 = __FUNCS__.func_174(reg6);
                                                    reg1 = reg9;
                                                    goto block_8_fin;
                                                ::block_696_fin::
                                                reg9 = __MEMORY_READ_32__(mem_0,1059640);
                                                reg0 = reg9;
                                                if (bit_bor(((reg0 == 0) and 1 or 0),((__UNSIGNED__(reg10) < __UNSIGNED__(reg0)) and 1 or 0)))~=0 then goto block_692_fin; end;
                                                goto block_688_fin;
                                            ::block_695_fin::
                                            reg9 = __FUNCS__.func_168(reg0);
                                            if reg9~=0 then goto block_694_fin; end;
                                            reg9 = __FUNCS__.func_169(reg0);
                                            if ((reg9 ~= reg11) and 1 or 0)~=0 then goto block_694_fin; end;
                                            reg3 = reg0;
                                            reg9 = __MEMORY_READ_32__(mem_0,reg3);
                                            reg5 = reg9;
                                            reg9 = __MEMORY_READ_32__(mem_0,1059608);
                                            reg6 = reg9;
                                            if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg6)) and 1 or 0)==0 then goto if_857_else end 
                                                reg13 = __MEMORY_READ_32__(mem_0,reg3+4);
                                                reg9 = ((__UNSIGNED__((bit_tobit(reg5 + reg13))) > __UNSIGNED__(reg6)) and 1 or 0)
                                            goto if_857_fin
                                            ::if_857_else::
                                                reg9 = 0
                                                -- BLOCK RET (if):
                                            ::if_857_fin::
                                            if reg9~=0 then goto block_691_fin; end;
                                        ::block_694_fin::
                                        reg9 = __MEMORY_READ_32__(mem_0,1059640);
                                        reg0 = reg9;
                                        
                                        __MEMORY_WRITE_32__(mem_0,1059640,((((__UNSIGNED__(reg10) > __UNSIGNED__(reg0)) and 1 or 0) == 0) and reg10 or reg0));
                                        reg3 = (bit_tobit(reg10 + reg12));
                                        reg0 = 1059620;
                                        
                                            
                                                
                                                while true do ::loop_886_start::
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg0);
                                                    if ((reg3 ~= reg9) and 1 or 0)==0 then goto if_891_fin end 
                                                        reg9 = __MEMORY_READ_32__(mem_0,reg0+8);
                                                        reg0 = reg9;
                                                        if reg0~=0 then goto loop_886_start; end;
                                                        goto block_885_fin;
                                                    ::if_891_fin::
                                                    break
                                                end
                                                
                                                reg9 = __FUNCS__.func_168(reg0);
                                                if reg9~=0 then goto block_885_fin; end;
                                                reg9 = __FUNCS__.func_169(reg0);
                                                if ((reg9 == reg11) and 1 or 0)~=0 then goto block_884_fin; end;
                                            ::block_885_fin::
                                            reg9 = __MEMORY_READ_32__(mem_0,1059608);
                                            reg13 = reg9;
                                            reg0 = 1059620;
                                            
                                                
                                                while true do ::loop_914_start::
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg0);
                                                    if ((__UNSIGNED__(reg9) <= __UNSIGNED__(reg13)) and 1 or 0)==0 then goto if_919_fin end 
                                                        reg9 = __FUNCS__.func_158(reg0);
                                                        if ((__UNSIGNED__(reg9) > __UNSIGNED__(reg13)) and 1 or 0)~=0 then goto block_913_fin; end;
                                                    ::if_919_fin::
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg0+8);
                                                    reg0 = reg9;
                                                    if reg0~=0 then goto loop_914_start; end;
                                                    break
                                                end
                                                
                                                reg0 = 0;
                                            ::block_913_fin::
                                            reg9 = __FUNCS__.func_158(reg0);
                                            reg8 = reg9;
                                            reg9 = __FUNCS__.func_143(20,8);
                                            reg14 = reg9;
                                            reg3 = (bit_tobit((bit_tobit(reg8 - reg14)) + -23));
                                            reg9 = __FUNCS__.func_174(reg3);
                                            reg0 = reg9;
                                            reg9 = __FUNCS__.func_143(reg0,8);
                                            reg15 = bit_tobit((bit_tobit(reg9 - reg0)) + reg3);
                                            reg0 = reg15;
                                            reg9 = __FUNCS__.func_143(16,8);
                                            
                                            reg15 = ((((__UNSIGNED__(reg0) < __UNSIGNED__((bit_tobit(reg9 + reg13)))) and 1 or 0) == 0) and reg0 or reg13);
                                            reg9 = __FUNCS__.func_174(reg15);
                                            reg16 = reg9;
                                            reg9 = __FUNCS__.func_172(reg15,reg14);
                                            reg0 = reg9;
                                            reg9 = __FUNCS__.func_174(0);
                                            reg7 = reg9;
                                            reg9 = __FUNCS__.func_143(reg7,8);
                                            reg1 = reg9;
                                            reg9 = __FUNCS__.func_143(20,8);
                                            reg5 = reg9;
                                            reg9 = __FUNCS__.func_143(16,8);
                                            reg6 = reg9;
                                            reg9 = __FUNCS__.func_174(reg10);
                                            reg3 = reg9;
                                            reg9 = __FUNCS__.func_143(reg3,8);
                                            reg17 = bit_tobit(reg9 - reg3);
                                            reg3 = reg17;
                                            reg9 = __FUNCS__.func_172(reg10,reg3);
                                            reg17 = reg9;
                                            __MEMORY_WRITE_32__(mem_0,1059608,reg17);
                                            reg9 = bit_tobit((bit_tobit(reg7 + reg12)) - (bit_tobit((bit_tobit(reg6 + (bit_tobit(reg1 + reg5)))) + reg3)));
                                            reg7 = reg9;
                                            __MEMORY_WRITE_32__(mem_0,1059600,reg7);
                                            __MEMORY_WRITE_32__(mem_0,reg17+4,(bit_bor(reg7,1)));
                                            reg9 = __FUNCS__.func_174(0);
                                            reg1 = reg9;
                                            reg9 = __FUNCS__.func_143(reg1,8);
                                            reg5 = reg9;
                                            reg9 = __FUNCS__.func_143(20,8);
                                            reg6 = reg9;
                                            reg9 = __FUNCS__.func_143(16,8);
                                            reg3 = reg9;
                                            reg9 = __FUNCS__.func_172(reg17,reg7);
                                            __MEMORY_WRITE_32__(mem_0,reg9+4,(bit_tobit(reg3 + (bit_tobit(reg6 + (bit_tobit(reg5 - reg1)))))));
                                            __MEMORY_WRITE_32__(mem_0,1059636,2097152);
                                            __FUNCS__.func_157(reg15,reg14);
                                            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,1059620);
                                            reg14 = reg9;
                                            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,1059628);
                                            (reg9):store(mem_0,(bit_tobit(reg16 + 8)));
                                            (reg14):store(mem_0,reg16);
                                            __MEMORY_WRITE_32__(mem_0,1059632,reg11);
                                            __MEMORY_WRITE_32__(mem_0,1059624,reg12);
                                            __MEMORY_WRITE_32__(mem_0,1059620,reg10);
                                            __MEMORY_WRITE_32__(mem_0,1059628,reg16);
                                            
                                            while true do ::loop_1071_start::
                                                reg9 = __FUNCS__.func_172(reg0,4);
                                                reg3 = reg9;
                                                __MEMORY_WRITE_32__(mem_0,reg0+4,7);
                                                reg0 = reg3;
                                                if ((__UNSIGNED__(reg8) > __UNSIGNED__((bit_tobit(reg0 + 4)))) and 1 or 0)~=0 then goto loop_1071_start; end;
                                                break
                                            end
                                            
                                            if ((reg13 == reg15) and 1 or 0)~=0 then goto block_687_fin; end;
                                            reg0 = (bit_tobit(reg15 - reg13));
                                            reg9 = __FUNCS__.func_172(reg13,reg0);
                                            __FUNCS__.func_131(reg13,reg0,reg9);
                                            if ((__UNSIGNED__(reg0) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_1103_fin end 
                                                __FUNCS__.func_52(reg13,reg0);
                                                goto block_687_fin;
                                            ::if_1103_fin::
                                            reg9 = bit_rshift(reg0,3);
                                            reg0 = reg9;
                                            reg6 = (bit_tobit((bit_lshift(reg0,3)) + 1059204));
                                            
                                                reg14 = __MEMORY_READ_32__(mem_0,1059196);
                                                reg3 = reg14;
                                                reg14 = bit_lshift(1,reg0);
                                                reg0 = reg14;
                                                if (bit_band(reg3,reg0))==0 then goto if_1127_fin end 
                                                    reg14 = __MEMORY_READ_32__(mem_0,reg6+8);
                                                    reg9 = reg14; goto block_1118_fin;
                                                ::if_1127_fin::
                                                __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg0,reg3)));
                                                reg9 = reg6
                                                -- BLOCK RET (block):
                                            ::block_1118_fin::
                                            reg0 = reg9;
                                            __MEMORY_WRITE_32__(mem_0,reg6+8,reg13);
                                            __MEMORY_WRITE_32__(mem_0,reg0+12,reg13);
                                            __MEMORY_WRITE_32__(mem_0,reg13+12,reg6);
                                            __MEMORY_WRITE_32__(mem_0,reg13+8,reg0);
                                            goto block_687_fin;
                                        ::block_884_fin::
                                        reg9 = __MEMORY_READ_32__(mem_0,reg0);
                                        reg1 = reg9;
                                        __MEMORY_WRITE_32__(mem_0,reg0,reg10);
                                        reg9 = __MEMORY_READ_32__(mem_0,reg0+4);
                                        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_tobit(reg9 + reg12)));
                                        reg9 = __FUNCS__.func_174(reg10);
                                        reg5 = reg9;
                                        reg9 = __FUNCS__.func_143(reg5,8);
                                        reg6 = reg9;
                                        reg9 = __FUNCS__.func_174(reg1);
                                        reg3 = reg9;
                                        reg9 = __FUNCS__.func_143(reg3,8);
                                        reg0 = reg9;
                                        reg7 = (bit_tobit(reg10 + (bit_tobit(reg6 - reg5))));
                                        reg9 = __FUNCS__.func_172(reg7,reg4);
                                        reg8 = reg9;
                                        __FUNCS__.func_157(reg7,reg4);
                                        reg9 = bit_tobit(reg1 + (bit_tobit(reg0 - reg3)));
                                        reg0 = reg9;
                                        reg9 = bit_tobit(reg0 - (bit_tobit(reg4 + reg7)));
                                        reg4 = reg9;
                                        reg9 = __MEMORY_READ_32__(mem_0,1059608);
                                        if ((reg0 ~= reg9) and 1 or 0)==0 then goto if_1205_fin end 
                                            reg9 = __MEMORY_READ_32__(mem_0,1059604);
                                            if ((reg9 == reg0) and 1 or 0)~=0 then goto block_690_fin; end;
                                            reg9 = __MEMORY_READ_32__(mem_0,reg0+4);
                                            if (((bit_band(reg9,3)) ~= 1) and 1 or 0)~=0 then goto block_689_fin; end;
                                            
                                                reg9 = __FUNCS__.func_166(reg0);
                                                reg5 = reg9;
                                                if ((__UNSIGNED__(reg5) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_1224_fin end 
                                                    __FUNCS__.func_54(reg0);
                                                    goto block_1218_fin;
                                                ::if_1224_fin::
                                                reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                                                reg6 = reg9;
                                                reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                                                reg3 = reg9;
                                                if ((reg6 ~= reg3) and 1 or 0)==0 then goto if_1240_fin end 
                                                    __MEMORY_WRITE_32__(mem_0,reg3+12,reg6);
                                                    __MEMORY_WRITE_32__(mem_0,reg6+8,reg3);
                                                    goto block_1218_fin;
                                                ::if_1240_fin::
                                                reg9 = __MEMORY_READ_32__(mem_0,1059196);
                                                __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg9,(bit_rol(-2,(bit_rshift(reg5,3)))))));
                                            ::block_1218_fin::
                                            reg9 = bit_tobit(reg4 + reg5);
                                            reg4 = reg9;
                                            reg9 = __FUNCS__.func_172(reg0,reg5);
                                            reg0 = reg9;
                                            goto block_689_fin;
                                        ::if_1205_fin::
                                        __MEMORY_WRITE_32__(mem_0,1059608,reg8);
                                        reg9 = __MEMORY_READ_32__(mem_0,1059600);
                                        reg0 = (bit_tobit(reg9 + reg4));
                                        __MEMORY_WRITE_32__(mem_0,1059600,reg0);
                                        __MEMORY_WRITE_32__(mem_0,reg8+4,(bit_bor(reg0,1)));
                                        reg9 = __FUNCS__.func_174(reg7);
                                        reg1 = reg9;
                                        goto block_8_fin;
                                    ::block_693_fin::
                                    reg3 = (bit_tobit(reg0 - reg4));
                                    __MEMORY_WRITE_32__(mem_0,1059600,reg3);
                                    reg9 = __MEMORY_READ_32__(mem_0,1059608);
                                    reg6 = reg9;
                                    reg9 = __FUNCS__.func_172(reg6,reg4);
                                    reg0 = reg9;
                                    __MEMORY_WRITE_32__(mem_0,1059608,reg0);
                                    __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg3,1)));
                                    __FUNCS__.func_157(reg6,reg4);
                                    reg9 = __FUNCS__.func_174(reg6);
                                    reg1 = reg9;
                                    goto block_8_fin;
                                ::block_692_fin::
                                __MEMORY_WRITE_32__(mem_0,1059640,reg10);
                                goto block_688_fin;
                            ::block_691_fin::
                            reg9 = __MEMORY_READ_32__(mem_0,reg0+4);
                            __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_tobit(reg9 + reg12)));
                            reg9 = __MEMORY_READ_32__(mem_0,1059600);
                            reg3 = reg9;
                            reg9 = __MEMORY_READ_32__(mem_0,1059608);
                            reg0 = reg9;
                            reg9 = __FUNCS__.func_174(reg0);
                            reg13 = reg0;
                            reg0 = reg9;
                            reg9 = __FUNCS__.func_143(reg0,8);
                            reg14 = bit_tobit(reg9 - reg0);
                            reg0 = reg14;
                            reg9 = __FUNCS__.func_172(reg13,reg0);
                            reg7 = reg9;
                            reg1 = (bit_tobit((bit_tobit(reg3 + reg12)) - reg0));
                            __MEMORY_WRITE_32__(mem_0,1059600,reg1);
                            __MEMORY_WRITE_32__(mem_0,1059608,reg7);
                            __MEMORY_WRITE_32__(mem_0,reg7+4,(bit_bor(reg1,1)));
                            reg9 = __FUNCS__.func_174(0);
                            reg5 = reg9;
                            reg9 = __FUNCS__.func_143(reg5,8);
                            reg6 = reg9;
                            reg9 = __FUNCS__.func_143(20,8);
                            reg3 = reg9;
                            reg9 = __FUNCS__.func_143(16,8);
                            reg0 = reg9;
                            reg9 = __FUNCS__.func_172(reg7,reg1);
                            __MEMORY_WRITE_32__(mem_0,reg9+4,(bit_tobit(reg0 + (bit_tobit(reg3 + (bit_tobit(reg6 - reg5)))))));
                            __MEMORY_WRITE_32__(mem_0,1059636,2097152);
                            goto block_687_fin;
                        ::block_690_fin::
                        __MEMORY_WRITE_32__(mem_0,1059604,reg8);
                        reg9 = __MEMORY_READ_32__(mem_0,1059596);
                        reg0 = (bit_tobit(reg9 + reg4));
                        __MEMORY_WRITE_32__(mem_0,1059596,reg0);
                        __FUNCS__.func_140(reg8,reg0);
                        reg9 = __FUNCS__.func_174(reg7);
                        reg1 = reg9;
                        goto block_8_fin;
                    ::block_689_fin::
                    __FUNCS__.func_131(reg8,reg4,reg0);
                    if ((__UNSIGNED__(reg4) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_1415_fin end 
                        __FUNCS__.func_52(reg8,reg4);
                        reg9 = __FUNCS__.func_174(reg7);
                        reg1 = reg9;
                        goto block_8_fin;
                    ::if_1415_fin::
                    reg0 = (bit_rshift(reg4,3));
                    reg6 = (bit_tobit((bit_lshift(reg0,3)) + 1059204));
                    
                        reg13 = __MEMORY_READ_32__(mem_0,1059196);
                        reg3 = reg13;
                        reg13 = bit_lshift(1,reg0);
                        reg0 = reg13;
                        if (bit_band(reg3,reg0))==0 then goto if_1442_fin end 
                            reg13 = __MEMORY_READ_32__(mem_0,reg6+8);
                            reg9 = reg13; goto block_1433_fin;
                        ::if_1442_fin::
                        __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg0,reg3)));
                        reg9 = reg6
                        -- BLOCK RET (block):
                    ::block_1433_fin::
                    reg0 = reg9;
                    __MEMORY_WRITE_32__(mem_0,reg6+8,reg8);
                    __MEMORY_WRITE_32__(mem_0,reg0+12,reg8);
                    __MEMORY_WRITE_32__(mem_0,reg8+12,reg6);
                    __MEMORY_WRITE_32__(mem_0,reg8+8,reg0);
                    reg8 = __FUNCS__.func_174(reg7);
                    reg1 = reg8;
                    goto block_8_fin;
                ::block_688_fin::
                __MEMORY_WRITE_32__(mem_0,1059644,4095);
                __MEMORY_WRITE_32__(mem_0,1059632,reg11);
                __MEMORY_WRITE_32__(mem_0,1059624,reg12);
                __MEMORY_WRITE_32__(mem_0,1059620,reg10);
                __MEMORY_WRITE_32__(mem_0,1059216,1059204);
                __MEMORY_WRITE_32__(mem_0,1059224,1059212);
                __MEMORY_WRITE_32__(mem_0,1059212,1059204);
                __MEMORY_WRITE_32__(mem_0,1059232,1059220);
                __MEMORY_WRITE_32__(mem_0,1059220,1059212);
                __MEMORY_WRITE_32__(mem_0,1059240,1059228);
                __MEMORY_WRITE_32__(mem_0,1059228,1059220);
                __MEMORY_WRITE_32__(mem_0,1059248,1059236);
                __MEMORY_WRITE_32__(mem_0,1059236,1059228);
                __MEMORY_WRITE_32__(mem_0,1059256,1059244);
                __MEMORY_WRITE_32__(mem_0,1059244,1059236);
                __MEMORY_WRITE_32__(mem_0,1059264,1059252);
                __MEMORY_WRITE_32__(mem_0,1059252,1059244);
                __MEMORY_WRITE_32__(mem_0,1059272,1059260);
                __MEMORY_WRITE_32__(mem_0,1059260,1059252);
                __MEMORY_WRITE_32__(mem_0,1059280,1059268);
                __MEMORY_WRITE_32__(mem_0,1059268,1059260);
                __MEMORY_WRITE_32__(mem_0,1059276,1059268);
                __MEMORY_WRITE_32__(mem_0,1059288,1059276);
                __MEMORY_WRITE_32__(mem_0,1059284,1059276);
                __MEMORY_WRITE_32__(mem_0,1059296,1059284);
                __MEMORY_WRITE_32__(mem_0,1059292,1059284);
                __MEMORY_WRITE_32__(mem_0,1059304,1059292);
                __MEMORY_WRITE_32__(mem_0,1059300,1059292);
                __MEMORY_WRITE_32__(mem_0,1059312,1059300);
                __MEMORY_WRITE_32__(mem_0,1059308,1059300);
                __MEMORY_WRITE_32__(mem_0,1059320,1059308);
                __MEMORY_WRITE_32__(mem_0,1059316,1059308);
                __MEMORY_WRITE_32__(mem_0,1059328,1059316);
                __MEMORY_WRITE_32__(mem_0,1059324,1059316);
                __MEMORY_WRITE_32__(mem_0,1059336,1059324);
                __MEMORY_WRITE_32__(mem_0,1059332,1059324);
                __MEMORY_WRITE_32__(mem_0,1059344,1059332);
                __MEMORY_WRITE_32__(mem_0,1059352,1059340);
                __MEMORY_WRITE_32__(mem_0,1059340,1059332);
                __MEMORY_WRITE_32__(mem_0,1059360,1059348);
                __MEMORY_WRITE_32__(mem_0,1059348,1059340);
                __MEMORY_WRITE_32__(mem_0,1059368,1059356);
                __MEMORY_WRITE_32__(mem_0,1059356,1059348);
                __MEMORY_WRITE_32__(mem_0,1059376,1059364);
                __MEMORY_WRITE_32__(mem_0,1059364,1059356);
                __MEMORY_WRITE_32__(mem_0,1059384,1059372);
                __MEMORY_WRITE_32__(mem_0,1059372,1059364);
                __MEMORY_WRITE_32__(mem_0,1059392,1059380);
                __MEMORY_WRITE_32__(mem_0,1059380,1059372);
                __MEMORY_WRITE_32__(mem_0,1059400,1059388);
                __MEMORY_WRITE_32__(mem_0,1059388,1059380);
                __MEMORY_WRITE_32__(mem_0,1059408,1059396);
                __MEMORY_WRITE_32__(mem_0,1059396,1059388);
                __MEMORY_WRITE_32__(mem_0,1059416,1059404);
                __MEMORY_WRITE_32__(mem_0,1059404,1059396);
                __MEMORY_WRITE_32__(mem_0,1059424,1059412);
                __MEMORY_WRITE_32__(mem_0,1059412,1059404);
                __MEMORY_WRITE_32__(mem_0,1059432,1059420);
                __MEMORY_WRITE_32__(mem_0,1059420,1059412);
                __MEMORY_WRITE_32__(mem_0,1059440,1059428);
                __MEMORY_WRITE_32__(mem_0,1059428,1059420);
                __MEMORY_WRITE_32__(mem_0,1059448,1059436);
                __MEMORY_WRITE_32__(mem_0,1059436,1059428);
                __MEMORY_WRITE_32__(mem_0,1059456,1059444);
                __MEMORY_WRITE_32__(mem_0,1059444,1059436);
                __MEMORY_WRITE_32__(mem_0,1059464,1059452);
                __MEMORY_WRITE_32__(mem_0,1059452,1059444);
                __MEMORY_WRITE_32__(mem_0,1059460,1059452);
                reg8 = __FUNCS__.func_174(0);
                reg1 = reg8;
                reg8 = __FUNCS__.func_143(reg1,8);
                reg5 = reg8;
                reg8 = __FUNCS__.func_143(20,8);
                reg6 = reg8;
                reg8 = __FUNCS__.func_143(16,8);
                reg3 = reg8;
                reg8 = __FUNCS__.func_174(reg10);
                reg0 = reg8;
                reg8 = __FUNCS__.func_143(reg0,8);
                reg9 = bit_tobit(reg8 - reg0);
                reg0 = reg9;
                reg8 = __FUNCS__.func_172(reg10,reg0);
                reg7 = reg8;
                __MEMORY_WRITE_32__(mem_0,1059608,reg7);
                reg8 = bit_tobit((bit_tobit(reg1 + reg12)) - (bit_tobit((bit_tobit(reg3 + (bit_tobit(reg6 + reg5)))) + reg0)));
                reg1 = reg8;
                __MEMORY_WRITE_32__(mem_0,1059600,reg1);
                __MEMORY_WRITE_32__(mem_0,reg7+4,(bit_bor(reg1,1)));
                reg8 = __FUNCS__.func_174(0);
                reg5 = reg8;
                reg8 = __FUNCS__.func_143(reg5,8);
                reg6 = reg8;
                reg8 = __FUNCS__.func_143(20,8);
                reg3 = reg8;
                reg8 = __FUNCS__.func_143(16,8);
                reg0 = reg8;
                reg8 = __FUNCS__.func_172(reg7,reg1);
                __MEMORY_WRITE_32__(mem_0,reg8+4,(bit_tobit(reg0 + (bit_tobit(reg3 + (bit_tobit(reg6 - reg5)))))));
                __MEMORY_WRITE_32__(mem_0,1059636,2097152);
            ::block_687_fin::
            reg1 = 0;
            reg5 = __MEMORY_READ_32__(mem_0,1059600);
            reg0 = reg5;
            if ((__UNSIGNED__(reg0) <= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_8_fin; end;
            reg3 = (bit_tobit(reg0 - reg4));
            __MEMORY_WRITE_32__(mem_0,1059600,reg3);
            reg5 = __MEMORY_READ_32__(mem_0,1059608);
            reg6 = reg5;
            reg5 = __FUNCS__.func_172(reg6,reg4);
            reg0 = reg5;
            __MEMORY_WRITE_32__(mem_0,1059608,reg0);
            __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg3,1)));
            __FUNCS__.func_157(reg6,reg4);
            reg0 = __FUNCS__.func_174(reg6);
            reg1 = reg0;
        ::block_8_fin::
        __GLOBALS__[0] = (bit_tobit(reg2 + 16));
        do return reg1; end;
    end
    function __FUNCS__.func_3(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19,reg20,reg21,reg22,reg23,reg24,reg25,reg26,reg27,reg28,reg29;
        reg4 = __GLOBALS__[0];
        reg5 = (bit_tobit(reg4 - 96));
        __GLOBALS__[0] = reg5;
        
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 12)));
            reg6 = reg4;
            reg4 = bit_tobit(reg6 + reg2);
            reg2 = reg4;
            if ((__UNSIGNED__(reg2) < __UNSIGNED__(reg6)) and 1 or 0)==0 then goto if_19_fin end 
                __FUNCS__.func_136();
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5);
                reg7 = reg4;
                __MEMORY_WRITE_32__(mem_0,reg0,1);
                (reg7):store(mem_0,reg0+4);
                goto block_8_fin;
            ::if_19_fin::
            
                
                    
                        
                            
                                reg9 = __MEMORY_READ_32__(mem_0,reg1);
                                reg10 = reg9;
                                reg9 = (bit_tobit(reg10 + 1));
                                
                                reg11 = ((((__UNSIGNED__(reg10) < __UNSIGNED__(8)) and 1 or 0) == 0) and (__IMUL__((bit_rshift(reg9,3)),7)) or reg10);
                                if ((__UNSIGNED__(reg2) > __UNSIGNED__((bit_rshift(reg11,1)))) and 1 or 0)==0 then goto if_57_fin end 
                                    reg12 = (bit_tobit(reg11 + 1));
                                    
                                    reg13 = (((__UNSIGNED__(reg2) > __UNSIGNED__(reg12)) and 1 or 0) == 0) and reg12 or reg2;
                                    reg2 = reg13;
                                    if ((__UNSIGNED__(reg2) < __UNSIGNED__(8)) and 1 or 0)~=0 then goto block_36_fin; end;
                                    if ((reg2 == (bit_band(reg2,536870911))) and 1 or 0)==0 then goto if_76_fin end 
                                        reg8 = (bit_tobit((bit_rshift(-1,(__CLZ__((bit_tobit((__IDIV_U__((bit_lshift(reg2,3)),7)) + -1)))))) + 1)); goto block_35_fin;
                                    ::if_76_fin::
                                    __FUNCS__.func_136();
                                    reg13 = __MEMORY_READ_32__(mem_0,reg5+24);
                                    reg12 = reg13;
                                    reg13 = __MEMORY_READ_32__(mem_0,reg5+28);
                                    reg4 = reg13; goto block_33_fin;
                                ::if_57_fin::
                                reg13 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                                reg14 = reg13;
                                reg2 = 0;
                                
                                while true do ::loop_106_start::
                                    
                                        
                                            if (((bit_band(reg12,1)) == 0) and 1 or 0)==0 then goto if_113_fin end 
                                                if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg9)) and 1 or 0)~=0 then goto block_108_fin; end;
                                                goto block_107_fin;
                                            ::if_113_fin::
                                            reg12 = (bit_tobit(reg2 + 3));
                                            if ((__UNSIGNED__(reg12) < __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_108_fin; end;
                                            reg2 = reg12;
                                            if ((__UNSIGNED__(reg2) < __UNSIGNED__(reg9)) and 1 or 0)~=0 then goto block_107_fin; end;
                                        ::block_108_fin::
                                        
                                            
                                                if ((__UNSIGNED__(reg9) >= __UNSIGNED__(4)) and 1 or 0)==0 then goto if_138_fin end 
                                                    reg13 = __MEMORY_READ_32__(mem_0,reg14);
                                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg14 + reg9)),reg13);
                                                    goto block_134_fin;
                                                ::if_138_fin::
                                                __FUNCS__.func_39((bit_tobit(reg14 + 4)),reg14,reg9);
                                                if ((reg9 == 0) and 1 or 0)~=0 then goto block_133_fin; end;
                                            ::block_134_fin::
                                            reg13 = __LONG_INT__(0,0); reg13:load(mem_0,reg3);
                                            reg7 = reg13;
                                            reg13 = ((reg7):_xor(__LONG_INT__(1852142177,1819895653)));
                                            reg15 = ((reg7):_xor(__LONG_INT__(1886610805,1936682341)));
                                            reg16 = __LONG_INT__(0,0); reg16:load(mem_0,(bit_tobit(reg3 + 8)));
                                            reg17 = reg16;
                                            reg16 = ((reg17):_xor(__LONG_INT__(2037671283,1952801890)));
                                            reg18 = ((reg17):_xor(__LONG_INT__(1852075885,1685025377)));
                                            reg9 = (bit_tobit(reg5 + 80));
                                            reg2 = 0;
                                            
                                            while true do ::loop_185_start::
                                                
                                                    reg3 = reg2;
                                                    reg19 = (bit_tobit(reg14 + reg3));
                                                    reg20 = __MEMORY_READ_8__(mem_0,reg19);
                                                    if ((reg20 ~= 128) and 1 or 0)~=0 then goto block_186_fin; end;
                                                    reg2 = (bit_tobit(reg14 - (bit_lshift(reg3,3))));
                                                    reg20 = (bit_tobit(reg2 + -4));
                                                    reg21 = (bit_tobit(reg2 + -8));
                                                    reg22 = __MEMORY_READ_32__(mem_0,reg21);
                                                    reg2 = reg22;
                                                    
                                                        
                                                        while true do ::loop_212_start::
                                                            (__LONG_INT__(0,0)):store(mem_0,reg9);
                                                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg9 + 8)),0);
                                                            __MEMORY_WRITE_32__(mem_0,reg5+92,0);
                                                            (reg16):store(mem_0,reg5+72);
                                                            (reg18):store(mem_0,reg5+64);
                                                            (reg13):store(mem_0,reg5+56);
                                                            (reg15):store(mem_0,reg5+48);
                                                            (reg17):store(mem_0,reg5+40);
                                                            (reg7):store(mem_0,reg5+32);
                                                            __FUNCS__.func_24(reg2,(bit_tobit(reg5 + 32)));
                                                            reg22 = __LONG_INT__(0,0); reg22:load(mem_0,reg5+80);
                                                            reg23 = __MEMORY_READ_32__(mem_0,reg5+88);reg23=__LONG_INT__(reg23,0);
                                                            reg24 = ((reg22):_or(((reg23):_shl(__LONG_INT__(56,0)))));
                                                            reg22 = __LONG_INT__(0,0); reg22:load(mem_0,reg5+72);
                                                            reg23 = ((reg24):_xor(reg22));
                                                            reg22 = __LONG_INT__(0,0); reg22:load(mem_0,reg5+56);
                                                            reg25 = reg23 + reg22;
                                                            reg22 = (reg23):_rotl(__LONG_INT__(16,0));
                                                            reg23 = reg25;
                                                            reg25 = ((reg22):_xor(reg23));
                                                            reg22 = __LONG_INT__(0,0); reg22:load(mem_0,reg5+64);
                                                            reg26 = reg22;
                                                            reg22 = __LONG_INT__(0,0); reg22:load(mem_0,reg5+48);
                                                            reg27 = (reg26 + reg22);
                                                            reg22 = (reg25 + ((reg27):_rotl(__LONG_INT__(32,0))));
                                                            reg28 = (reg22):_xor(reg24);
                                                            reg24 = ((((reg26):_rotl(__LONG_INT__(13,0)))):_xor(reg27));
                                                            reg29 = reg23 + reg24;
                                                            reg23 = reg29;
                                                            reg29 = (reg23):_xor(((reg24):_rotl(__LONG_INT__(17,0))));
                                                            reg24 = reg29;
                                                            reg26 = (reg28 + reg24);
                                                            reg28 = (reg26):_xor(((reg24):_rotl(__LONG_INT__(13,0))));
                                                            reg24 = reg28;
                                                            reg28 = (((reg25):_rotl(__LONG_INT__(21,0)))):_xor(reg22);
                                                            reg25 = reg28;
                                                            reg22 = reg25 + ((((reg23):_rotl(__LONG_INT__(32,0)))):_xor(__LONG_INT__(255,0)));
                                                            reg23 = reg22;
                                                            reg27 = (reg24 + reg23);
                                                            reg22 = (reg27):_xor(((reg24):_rotl(__LONG_INT__(17,0))));
                                                            reg24 = reg22;
                                                            reg22 = (((reg25):_rotl(__LONG_INT__(16,0)))):_xor(reg23);
                                                            reg23 = reg22;
                                                            reg25 = (reg23 + ((reg26):_rotl(__LONG_INT__(32,0))));
                                                            reg22 = reg24 + reg25;
                                                            reg28 = (reg24):_rotl(__LONG_INT__(13,0));
                                                            reg24 = reg22;
                                                            reg26 = ((reg28):_xor(reg24));
                                                            reg22 = (((reg23):_rotl(__LONG_INT__(21,0)))):_xor(reg25);
                                                            reg23 = reg22;
                                                            reg25 = (reg23 + ((reg27):_rotl(__LONG_INT__(32,0))));
                                                            reg22 = reg26 + reg25;
                                                            reg28 = (reg26):_rotl(__LONG_INT__(17,0));
                                                            reg26 = reg22;
                                                            reg27 = ((reg28):_xor(reg26));
                                                            reg22 = (((reg23):_rotl(__LONG_INT__(16,0)))):_xor(reg25);
                                                            reg23 = reg22;
                                                            reg22 = reg23 + ((reg24):_rotl(__LONG_INT__(32,0)));
                                                            reg24 = reg22;
                                                            reg25 = ((((reg27):_rotl(__LONG_INT__(13,0)))):_xor((reg27 + reg24)));
                                                            reg22 = (((reg23):_rotl(__LONG_INT__(21,0)))):_xor(reg24);
                                                            reg24 = reg22;
                                                            reg23 = (reg24 + ((reg26):_rotl(__LONG_INT__(32,0))));
                                                            reg26 = (reg25 + reg23);
                                                            reg22 = ((((((((reg26):_xor(((((((reg24):_rotl(__LONG_INT__(16,0)))):_xor(reg23))):_rotl(__LONG_INT__(21,0)))))):_xor(((reg25):_rotl(__LONG_INT__(17,0)))))):_xor(((reg26):_shr_u(__LONG_INT__(32,0))))))[1]);
                                                            reg25 = (bit_band(reg10,reg22));
                                                            reg12 = reg25;
                                                            reg26 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg14 + reg25)));
                                                            reg27 = (bit_band(reg26,-2139062144));
                                                            if ((reg27 == 0) and 1 or 0)==0 then goto if_418_fin end 
                                                                reg2 = 4;
                                                                reg12 = reg25;
                                                                
                                                                while true do ::loop_423_start::
                                                                    reg26 = bit_tobit(reg2 + reg12);
                                                                    reg12 = reg26;
                                                                    reg26 = bit_tobit(reg2 + 4);
                                                                    reg2 = reg26;
                                                                    reg26 = bit_band(reg12,reg10);
                                                                    reg12 = reg26;
                                                                    reg26 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg14 + reg12)));
                                                                    reg27 = (bit_band(reg26,-2139062144));
                                                                    if ((reg27 == 0) and 1 or 0)~=0 then goto loop_423_start; end;
                                                                    break
                                                                end
                                                                
                                                            ::if_418_fin::
                                                            reg2 = (bit_band((bit_tobit((bit_rshift((__CTZ__(reg27)),3)) + reg12)),reg10));
                                                            reg26 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg14 + reg2)));reg26=bit_arshift(bit_lshift(reg26,24),24);
                                                            if ((reg26 > -1) and 1 or 0)==0 then goto if_460_fin end 
                                                                reg26 = __MEMORY_READ_32__(mem_0,reg14);
                                                                reg2 = (bit_rshift((__CTZ__((bit_band(reg26,-2139062144)))),3));
                                                            ::if_460_fin::
                                                            if ((__UNSIGNED__((bit_band((bit_bxor((bit_tobit(reg2 - reg25)),(bit_tobit(reg3 - reg25)))),reg10))) < __UNSIGNED__(4)) and 1 or 0)~=0 then goto block_211_fin; end;
                                                            reg12 = (bit_tobit(reg2 + reg14));
                                                            reg26 = __MEMORY_READ_8__(mem_0,reg12);
                                                            reg28 = reg12;
                                                            reg12 = (bit_rshift(reg22,25));
                                                            __MEMORY_WRITE_8__(mem_0,reg28,reg12);
                                                            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit((bit_band((bit_tobit(reg2 + -4)),reg10)) + reg14)) + 4)),reg12);
                                                            if ((reg26 ~= 255) and 1 or 0)==0 then goto if_506_fin end 
                                                                reg26 = bit_tobit((bit_tobit(reg14 - (bit_lshift(reg2,3)))) + -8);
                                                                reg2 = reg26;
                                                                reg26 = __LONG_INT__(0,0); reg26:load(mem_0,reg2);
                                                                reg24 = reg26;
                                                                reg26 = __LONG_INT__(0,0); reg26:load(mem_0,reg21);
                                                                (reg26):store(mem_0,reg2);
                                                                reg2 = ((reg24)[1]);
                                                                __MEMORY_WRITE_32__(mem_0,reg21,reg2);
                                                                (((reg24):_shr_u(__LONG_INT__(32,0)))):store32(mem_0,reg20);
                                                                goto loop_212_start;
                                                            ::if_506_fin::
                                                            break
                                                        end
                                                        
                                                        __MEMORY_WRITE_8__(mem_0,reg19,255);
                                                        __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit((bit_band((bit_tobit(reg3 + -4)),reg10)) + reg14)) + 4)),255);
                                                        reg26 = __LONG_INT__(0,0); reg26:load(mem_0,reg21);
                                                        (reg26):store(mem_0,(bit_tobit((bit_tobit(reg14 - (bit_lshift(reg2,3)))) + -8)));
                                                        goto block_186_fin;
                                                    ::block_211_fin::
                                                    reg2 = (bit_rshift(reg22,25));
                                                    __MEMORY_WRITE_8__(mem_0,reg19,reg2);
                                                    __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit((bit_band((bit_tobit(reg3 + -4)),reg10)) + reg14)) + 4)),reg2);
                                                ::block_186_fin::
                                                reg2 = (bit_tobit(reg3 + 1));
                                                if ((reg3 ~= reg10) and 1 or 0)~=0 then goto loop_185_start; end;
                                                break
                                            end
                                            
                                        ::block_133_fin::
                                        __MEMORY_WRITE_32__(mem_0,reg0,0);
                                        __MEMORY_WRITE_32__(mem_0,reg1+8,(bit_tobit(reg11 - reg6)));
                                        goto block_8_fin;
                                    ::block_107_fin::
                                    reg12 = (bit_tobit(reg2 + reg14));
                                    reg26 = __MEMORY_READ_32__(mem_0,reg12);
                                    reg28 = reg12;
                                    reg12 = reg26;
                                    __MEMORY_WRITE_32__(mem_0,reg28,(bit_tobit((bit_band((bit_bxor((bit_rshift(reg12,7)),-1)),16843009)) + (bit_bor(reg12,2139062143)))));
                                    reg12 = 1;
                                    reg26 = bit_tobit(reg2 + 1);
                                    reg2 = reg26;
                                    goto loop_106_start;
                                    break
                                end
                                
                                error('unreachable');
                            ::block_36_fin::
                            
                            reg8 = ((((__UNSIGNED__(reg2) < __UNSIGNED__(4)) and 1 or 0) == 0) and 8 or 4)
                            -- BLOCK RET (block):
                        ::block_35_fin::
                        reg2 = reg8;
                        if (((bit_band(reg2,536870911)) == reg2) and 1 or 0)==0 then goto if_638_fin end 
                            reg25 = 4;
                            reg14 = (bit_lshift(reg2,3));
                            reg21 = (bit_tobit(reg2 + 4));
                            reg12 = (bit_tobit(reg14 + reg21));
                            if ((__UNSIGNED__(reg12) >= __UNSIGNED__(reg14)) and 1 or 0)~=0 then goto block_34_fin; end;
                        ::if_638_fin::
                        __FUNCS__.func_136();
                        reg8 = __MEMORY_READ_32__(mem_0,reg5+8);
                        reg12 = reg8;
                        reg8 = __MEMORY_READ_32__(mem_0,reg5+12);
                        reg4 = reg8; goto block_33_fin;
                    ::block_34_fin::
                    if ((reg12 == 0) and 1 or 0)~=0 then goto block_32_fin; end;
                    reg8 = __FUNCS__.func_148(reg12,4);
                    reg25 = reg8;
                    if reg25~=0 then goto block_32_fin; end;
                    __FUNCS__.func_170(reg12,4);
                    error('unreachable');
                    reg4 = error('unreachable')
                    -- BLOCK RET (block):
                ::block_33_fin::
                reg1 = reg4;
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg12);
                __MEMORY_WRITE_32__(mem_0,reg0,1);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),reg1);
                goto block_8_fin;
            ::block_32_fin::
            reg4 = __FUNCS__.func_65((bit_tobit(reg14 + reg25)),255,reg21);
            reg11 = reg4;
            reg19 = (bit_tobit(reg2 + -1));
            
            reg22 = (bit_tobit(((((__UNSIGNED__(reg19) < __UNSIGNED__(8)) and 1 or 0) == 0) and (__IMUL__((bit_rshift(reg2,3)),7)) or reg19) - reg6));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg3 + 8)));
            reg7 = reg4;
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg3);
            reg17 = reg4;
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
            reg14 = reg4;
            reg25 = (bit_tobit(reg14 + 4));
            reg27 = (bit_tobit(reg14 + reg9));
            reg6 = reg14;
            
                reg8 = __MEMORY_READ_32__(mem_0,reg14);
                reg2 = (bit_band((bit_bxor(reg8,-1)),-2139062144));
                if reg2~=0 then reg4 = 1; goto block_735_fin; end;
                reg4 = 0
                -- BLOCK RET (block):
            ::block_735_fin::
            reg12 = reg4;
            
            while true do ::loop_749_start::
                
                    
                        
                            
                                if ((reg12 == 0) and 1 or 0)==0 then goto if_756_fin end 
                                    if ((__UNSIGNED__(reg25) >= __UNSIGNED__(reg27)) and 1 or 0)~=0 then goto block_752_fin; end;
                                    reg8 = bit_tobit(reg6 + -32);
                                    reg6 = reg8;
                                    reg8 = __MEMORY_READ_32__(mem_0,reg25);
                                    reg3 = (bit_tobit(reg25 + 4));
                                    reg25 = reg3;
                                    reg12 = (bit_band(reg8,-2139062144));
                                    if ((reg12 == -2139062144) and 1 or 0)~=0 then goto block_751_fin; end;
                                    reg25 = reg3;
                                    reg2 = (bit_bxor(reg12,-2139062144));
                                    reg4 = (bit_band((bit_tobit(reg2 + -1)),reg2)); goto block_753_fin;
                                ::if_756_fin::
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_752_fin; end;
                                reg4 = (bit_band((bit_tobit(reg2 + -1)),reg2))
                                -- BLOCK RET (block):
                            ::block_753_fin::
                            reg3 = (bit_tobit(reg5 + 80));
                            (__LONG_INT__(0,0)):store(mem_0,reg3);
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 8)),0);
                            __MEMORY_WRITE_32__(mem_0,reg5+92,0);
                            (((reg7):_xor(__LONG_INT__(2037671283,1952801890)))):store(mem_0,reg5+72);
                            (((reg7):_xor(__LONG_INT__(1852075885,1685025377)))):store(mem_0,reg5+64);
                            (((reg17):_xor(__LONG_INT__(1852142177,1819895653)))):store(mem_0,reg5+56);
                            (((reg17):_xor(__LONG_INT__(1886610805,1936682341)))):store(mem_0,reg5+48);
                            (reg7):store(mem_0,reg5+40);
                            (reg17):store(mem_0,reg5+32);
                            reg20 = (bit_tobit((bit_tobit(reg6 - (bit_band((__CTZ__(reg2)),56)))) + -8));
                            reg8 = __MEMORY_READ_32__(mem_0,reg20);
                            __FUNCS__.func_24(reg8,(bit_tobit(reg5 + 32)));
                            reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+80);
                            reg21 = __MEMORY_READ_32__(mem_0,reg5+88);reg21=__LONG_INT__(reg21,0);
                            reg24 = ((reg8):_or(((reg21):_shl(__LONG_INT__(56,0)))));
                            reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+72);
                            reg13 = ((reg24):_xor(reg8));
                            reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+56);
                            reg21 = reg13 + reg8;
                            reg8 = (reg13):_rotl(__LONG_INT__(16,0));
                            reg13 = reg21;
                            reg15 = ((reg8):_xor(reg13));
                            reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+64);
                            reg16 = reg8;
                            reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+48);
                            reg18 = (reg16 + reg8);
                            reg23 = (reg15 + ((reg18):_rotl(__LONG_INT__(32,0))));
                            reg8 = (reg23):_xor(reg24);
                            reg24 = ((((reg16):_rotl(__LONG_INT__(13,0)))):_xor(reg18));
                            reg21 = reg13 + reg24;
                            reg13 = reg21;
                            reg21 = (reg13):_xor(((reg24):_rotl(__LONG_INT__(17,0))));
                            reg24 = reg21;
                            reg16 = (reg8 + reg24);
                            reg8 = (reg16):_xor(((reg24):_rotl(__LONG_INT__(13,0))));
                            reg24 = reg8;
                            reg8 = (((reg15):_rotl(__LONG_INT__(21,0)))):_xor(reg23);
                            reg15 = reg8;
                            reg8 = reg15 + ((((reg13):_rotl(__LONG_INT__(32,0)))):_xor(__LONG_INT__(255,0)));
                            reg13 = reg8;
                            reg18 = (reg24 + reg13);
                            reg8 = (reg18):_xor(((reg24):_rotl(__LONG_INT__(17,0))));
                            reg24 = reg8;
                            reg8 = (((reg15):_rotl(__LONG_INT__(16,0)))):_xor(reg13);
                            reg13 = reg8;
                            reg15 = (reg13 + ((reg16):_rotl(__LONG_INT__(32,0))));
                            reg8 = reg24 + reg15;
                            reg21 = (reg24):_rotl(__LONG_INT__(13,0));
                            reg24 = reg8;
                            reg16 = ((reg21):_xor(reg24));
                            reg8 = (((reg13):_rotl(__LONG_INT__(21,0)))):_xor(reg15);
                            reg13 = reg8;
                            reg15 = (reg13 + ((reg18):_rotl(__LONG_INT__(32,0))));
                            reg8 = reg16 + reg15;
                            reg21 = (reg16):_rotl(__LONG_INT__(17,0));
                            reg16 = reg8;
                            reg18 = ((reg21):_xor(reg16));
                            reg8 = (((reg13):_rotl(__LONG_INT__(16,0)))):_xor(reg15);
                            reg13 = reg8;
                            reg8 = reg13 + ((reg24):_rotl(__LONG_INT__(32,0)));
                            reg24 = reg8;
                            reg15 = ((((reg18):_rotl(__LONG_INT__(13,0)))):_xor((reg18 + reg24)));
                            reg8 = (((reg13):_rotl(__LONG_INT__(21,0)))):_xor(reg24);
                            reg24 = reg8;
                            reg13 = (reg24 + ((reg16):_rotl(__LONG_INT__(32,0))));
                            reg16 = (reg15 + reg13);
                            reg8 = ((((((((reg16):_xor(((((((reg24):_rotl(__LONG_INT__(16,0)))):_xor(reg13))):_rotl(__LONG_INT__(21,0)))))):_xor(((reg15):_rotl(__LONG_INT__(17,0)))))):_xor(((reg16):_shr_u(__LONG_INT__(32,0))))))[1]);
                            reg12 = (bit_band(reg19,reg8));
                            reg21 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + reg12)));
                            reg3 = (bit_band(reg21,-2139062144));
                            if ((reg3 == 0) and 1 or 0)==0 then goto if_1022_fin end 
                                reg2 = 4;
                                
                                while true do ::loop_1025_start::
                                    reg3 = (bit_tobit(reg2 + reg12));
                                    reg21 = bit_tobit(reg2 + 4);
                                    reg2 = reg21;
                                    reg12 = (bit_band(reg3,reg19));
                                    reg21 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg11 + reg12)));
                                    reg3 = (bit_band(reg21,-2139062144));
                                    if ((reg3 == 0) and 1 or 0)~=0 then goto loop_1025_start; end;
                                    break
                                end
                                
                            ::if_1022_fin::
                            reg2 = (bit_band((bit_tobit((bit_rshift((__CTZ__(reg3)),3)) + reg12)),reg19));
                            reg21 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg11 + reg2)));reg21=bit_arshift(bit_lshift(reg21,24),24);
                            if ((reg21 > -1) and 1 or 0)==0 then goto if_1062_fin end 
                                reg21 = __MEMORY_READ_32__(mem_0,reg11);
                                reg2 = (bit_rshift((__CTZ__((bit_band(reg21,-2139062144)))),3));
                            ::if_1062_fin::
                            reg3 = (bit_rshift(reg8,25));
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg11)),reg3);
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit((bit_band((bit_tobit(reg2 + -4)),reg19)) + reg11)) + 4)),reg3);
                            reg21 = __LONG_INT__(0,0); reg21:load(mem_0,reg20);
                            (reg21):store(mem_0,(bit_tobit((bit_tobit(reg11 - (bit_lshift(reg2,3)))) + -8)));
                            reg2 = reg4;
                            if ((reg2 == 0) and 1 or 0)~=0 then goto block_751_fin; end;
                            goto block_750_fin;
                        ::block_752_fin::
                        __MEMORY_WRITE_32__(mem_0,reg1+8,reg22);
                        __MEMORY_WRITE_32__(mem_0,reg1,reg19);
                        __MEMORY_WRITE_32__(mem_0,reg0,0);
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 4)),reg11);
                        if ((reg10 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                        reg0 = (bit_lshift(reg9,3));
                        if (((bit_tobit((bit_tobit(reg10 + reg0)) + 5)) == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                        __FUNCS__.func_10((bit_tobit(reg14 - reg0)));
                        goto block_8_fin;
                    ::block_751_fin::
                    reg12 = 0;
                    goto loop_749_start;
                ::block_750_fin::
                reg12 = 1;
                goto loop_749_start;
                break
            end
            
            error('unreachable');
        ::block_8_fin::
        __GLOBALS__[0] = (bit_tobit(reg5 + 96));
    end
    function __FUNCS__.func_4(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19,reg20,reg21,reg22,reg23,reg24,reg25,reg26,reg27,reg28,reg29,reg30,reg31,reg32,reg33;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        
            
                
                    
                        
                            reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1);
                            reg5 = reg3;
                            if (((((reg5)[1] == 0) and ((reg5)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_18_fin end 
                                reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1+8);
                                reg6 = reg3;
                                if (((((reg6)[1] == 0) and ((reg6)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_24_fin end 
                                    reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg1+16);
                                    reg7 = reg3;
                                    if (((((reg7)[1] == 0) and ((reg7)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_30_fin end 
                                        reg3 = reg7 + reg5;
                                        reg7 = reg3;
                                        if ((reg7):_ge_u(reg5) and 1 or 0)==0 then goto if_37_fin end 
                                            reg3 = reg5 - reg6;
                                            reg6 = reg3;
                                            if ((reg6):_le_u(reg5) and 1 or 0)==0 then goto if_44_fin end 
                                                
                                                    
                                                        if ((reg7):_le_u(__LONG_INT__(-1,536870911)) and 1 or 0)==0 then goto if_50_fin end 
                                                            reg3 = __MEMORY_READ_16__(mem_0,reg1+24);
                                                            reg1 = reg3;
                                                            __MEMORY_WRITE_16__(mem_0,reg4+8,reg1);
                                                            (reg6):store(mem_0,reg4);
                                                            reg3 = ((reg7):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                                            
                                                            reg8 = ((reg3 == 0) and reg1 or (bit_tobit(reg1 + -32)));
                                                            
                                                            reg9 = (reg3 == 0) and reg7 or ((reg7):_shl(__LONG_INT__(32,0)));
                                                            reg7 = reg9;
                                                            reg3 = ((reg7):_lt_u(__LONG_INT__(0,65536)) and 1 or 0);
                                                            
                                                            reg9 = (reg3 == 0) and reg8 or (bit_tobit(reg8 + -16));
                                                            reg8 = reg9;
                                                            
                                                            reg9 = (reg3 == 0) and reg7 or ((reg7):_shl(__LONG_INT__(16,0)));
                                                            reg7 = reg9;
                                                            reg3 = ((reg7):_lt_u(__LONG_INT__(0,16777216)) and 1 or 0);
                                                            
                                                            reg9 = (reg3 == 0) and reg8 or (bit_tobit(reg8 + -8));
                                                            reg8 = reg9;
                                                            
                                                            reg9 = (reg3 == 0) and reg7 or ((reg7):_shl(__LONG_INT__(8,0)));
                                                            reg7 = reg9;
                                                            reg3 = ((reg7):_lt_u(__LONG_INT__(0,268435456)) and 1 or 0);
                                                            
                                                            reg9 = (reg3 == 0) and reg8 or (bit_tobit(reg8 + -4));
                                                            reg8 = reg9;
                                                            
                                                            reg9 = (reg3 == 0) and reg7 or ((reg7):_shl(__LONG_INT__(4,0)));
                                                            reg7 = reg9;
                                                            reg3 = ((reg7):_lt_u(__LONG_INT__(0,1073741824)) and 1 or 0);
                                                            
                                                            
                                                            reg9 = ((reg3 == 0) and reg7 or ((reg7):_shl(__LONG_INT__(2,0))));
                                                            reg10 = bit_tobit(((reg3 == 0) and reg8 or (bit_tobit(reg8 + -2))) + (bit_bxor(((((reg9):_shr_s(__LONG_INT__(63,0))))[1]),-1)));
                                                            reg3 = reg10;
                                                            reg8 = (bit_arshift((bit_lshift((bit_tobit(reg1 - reg3)),16)),16));
                                                            if ((reg8 < 0) and 1 or 0)~=0 then goto block_45_fin; end;
                                                            reg10 = (__LONG_INT__(reg8,0));
                                                            reg7 = ((__LONG_INT__(-1,-1)):_shr_u(reg10));
                                                            (((reg7):_and(reg6))):store(mem_0,reg4+16);
                                                            if ((reg6):_gt_u(reg7) and 1 or 0)~=0 then goto block_8_fin; end;
                                                            __MEMORY_WRITE_16__(mem_0,reg4+8,reg1);
                                                            (reg5):store(mem_0,reg4);
                                                            (((reg7):_and(reg5))):store(mem_0,reg4+16);
                                                            if ((reg5):_gt_u(reg7) and 1 or 0)~=0 then goto block_8_fin; end;
                                                            reg1 = (__IDIV_S__((bit_tobit((__IMUL__((bit_arshift((bit_lshift((bit_tobit(-96 - reg3)),16)),16)),80)) + 86960)),2126));
                                                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(81)) and 1 or 0)~=0 then goto block_46_fin; end;
                                                            reg11 = bit_lshift(reg1,4);
                                                            reg1 = reg11;
                                                            reg11 = __LONG_INT__(0,0); reg11:load(mem_0,(bit_tobit(reg1 + 1052904)));
                                                            reg12 = reg11;
                                                            reg7 = ((reg12):_and(__LONG_INT__(-1,0)));
                                                            reg11 = reg5;
                                                            reg5 = ((reg10):_and(__LONG_INT__(63,0)));
                                                            reg13 = ((reg11):_shl(reg5));
                                                            reg11 = ((reg13):_shr_u(__LONG_INT__(32,0)));
                                                            reg14 = (reg7 * reg11);
                                                            reg15 = ((reg14):_shr_u(__LONG_INT__(32,0)));
                                                            reg10 = ((reg12):_shr_u(__LONG_INT__(32,0)));
                                                            reg12 = ((reg13):_and(__LONG_INT__(-1,0)));
                                                            reg13 = (reg10 * reg12);
                                                            reg16 = ((reg13):_shr_u(__LONG_INT__(32,0)));
                                                            reg17 = (((((((reg14):_and(__LONG_INT__(-1,0))) + (((reg7 * reg12)):_shr_u(__LONG_INT__(32,0)))) + ((reg13):_and(__LONG_INT__(-1,0)))) + __LONG_INT__(-2147483648,0))):_shr_u(__LONG_INT__(32,0)));
                                                            reg18 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg1 + 1052912)));
                                                            reg14 = (__LONG_INT__((bit_band((bit_tobit(0 - (bit_tobit(reg3 + reg18)))),63)),0));
                                                            reg12 = ((__LONG_INT__(1,0)):_shl(reg14));
                                                            reg18 = (reg12 + __LONG_INT__(-1,-1));
                                                            reg19 = (reg6):_shl(reg5);
                                                            reg5 = reg19;
                                                            reg6 = ((reg5):_shr_u(__LONG_INT__(32,0)));
                                                            reg13 = (reg7 * reg6);
                                                            reg19 = (reg5):_and(__LONG_INT__(-1,0));
                                                            reg5 = reg19;
                                                            reg19 = reg5 * reg10;
                                                            reg20 = ((reg13):_and(__LONG_INT__(-1,0))) + (((reg7 * reg5)):_shr_u(__LONG_INT__(32,0)));
                                                            reg5 = reg19;
                                                            reg19 = ((((reg20 + ((reg5):_and(__LONG_INT__(-1,0)))) + __LONG_INT__(-2147483648,0))):_shr_u(__LONG_INT__(32,0)));
                                                            reg20 = reg6 * reg10;
                                                            reg6 = reg20;
                                                            reg20 = (reg5):_shr_u(__LONG_INT__(32,0));
                                                            reg5 = reg20;
                                                            reg20 = (reg13):_shr_u(__LONG_INT__(32,0));
                                                            reg13 = reg20;
                                                            reg20 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg1 + 1052914)));
                                                            reg1 = reg20;
                                                            
                                                                
                                                                    
                                                                        reg21 = (reg9):_shl(((((reg9):_xor(__LONG_INT__(-1,-1)))):_shr_u(__LONG_INT__(63,0))));
                                                                        reg9 = reg21;
                                                                        reg21 = ((reg9):_shr_u(__LONG_INT__(32,0)));
                                                                        reg22 = (reg10 * reg21);
                                                                        reg23 = (reg7 * reg21);
                                                                        reg24 = ((reg23):_shr_u(__LONG_INT__(32,0)));
                                                                        reg25 = (reg9):_and(__LONG_INT__(-1,0));
                                                                        reg9 = reg25;
                                                                        reg25 = (reg10 * reg9);
                                                                        reg26 = ((reg25):_shr_u(__LONG_INT__(32,0)));
                                                                        reg27 = ((((((reg23):_and(__LONG_INT__(-1,0))) + (((reg7 * reg9)):_shr_u(__LONG_INT__(32,0)))) + ((reg25):_and(__LONG_INT__(-1,0)))) + __LONG_INT__(-2147483648,0))):_shr_u(__LONG_INT__(32,0));
                                                                        reg25 = reg27;
                                                                        reg23 = ((((reg22 + reg24) + reg26) + reg25) + __LONG_INT__(1,0));
                                                                        reg3 = ((((reg23):_shr_u(reg14)))[1]);
                                                                        if ((__UNSIGNED__(reg3) >= __UNSIGNED__(10000)) and 1 or 0)==0 then goto if_392_fin end 
                                                                            if ((__UNSIGNED__(reg3) < __UNSIGNED__(1000000)) and 1 or 0)~=0 then goto block_330_fin; end;
                                                                            if ((__UNSIGNED__(reg3) < __UNSIGNED__(100000000)) and 1 or 0)~=0 then goto block_329_fin; end;
                                                                            reg8 = ((__UNSIGNED__(reg3) < __UNSIGNED__(1000000000)) and 1 or 0);
                                                                            
                                                                            reg27 = ((reg8 == 0) and 9 or 8);
                                                                            
                                                                            reg20 = ((reg8 == 0) and 1000000000 or 100000000); goto block_328_fin;
                                                                        ::if_392_fin::
                                                                        if ((__UNSIGNED__(reg3) >= __UNSIGNED__(100)) and 1 or 0)==0 then goto if_418_fin end 
                                                                            reg8 = ((__UNSIGNED__(reg3) < __UNSIGNED__(1000)) and 1 or 0);
                                                                            
                                                                            reg27 = ((reg8 == 0) and 3 or 2);
                                                                            
                                                                            reg20 = ((reg8 == 0) and 1000 or 100); goto block_328_fin;
                                                                        ::if_418_fin::
                                                                        reg27 = ((__UNSIGNED__(reg3) > __UNSIGNED__(9)) and 1 or 0);
                                                                        
                                                                        reg20 = ((((__UNSIGNED__(reg3) < __UNSIGNED__(10)) and 1 or 0) == 0) and 10 or 1); goto block_328_fin;
                                                                    ::block_330_fin::
                                                                    reg8 = ((__UNSIGNED__(reg3) < __UNSIGNED__(100000)) and 1 or 0);
                                                                    
                                                                    reg27 = ((reg8 == 0) and 5 or 4);
                                                                    
                                                                    reg20 = ((reg8 == 0) and 100000 or 10000); goto block_328_fin;
                                                                ::block_329_fin::
                                                                reg8 = ((__UNSIGNED__(reg3) < __UNSIGNED__(10000000)) and 1 or 0);
                                                                
                                                                reg27 = ((reg8 == 0) and 7 or 6);
                                                                
                                                                reg20 = ((reg8 == 0) and 10000000 or 1000000)
                                                                -- BLOCK RET (block):
                                                            ::block_328_fin::
                                                            reg8 = reg20;
                                                            reg20 = (((reg15 + (reg10 * reg11)) + reg16) + reg17);
                                                            reg7 = ((reg23):_and(reg18));
                                                            reg28 = (bit_tobit((bit_tobit(reg27 - reg1)) + 1));
                                                            reg29 = (((reg6 + reg13) + reg5) + reg19);
                                                            reg19 = ((reg23 - reg29) + __LONG_INT__(1,0));
                                                            reg6 = ((reg19):_and(reg18));
                                                            reg1 = 0;
                                                            
                                                            while true do ::loop_504_start::
                                                                reg30 = (__IDIV_U__(reg3,reg8));
                                                                
                                                                    
                                                                        
                                                                            if ((reg1 ~= 17) and 1 or 0)==0 then goto if_515_fin end 
                                                                                reg31 = (bit_tobit(reg1 + reg2));
                                                                                reg32 = (bit_tobit(reg30 + 48));
                                                                                __MEMORY_WRITE_8__(mem_0,reg31,reg32);
                                                                                reg33 = bit_tobit(reg3 - (__IMUL__(reg8,reg30)));
                                                                                reg3 = reg33;
                                                                                reg13 = (((__LONG_INT__(reg3,0))):_shl(reg14));
                                                                                reg5 = (reg13 + reg7);
                                                                                if ((reg19):_gt_u(reg5) and 1 or 0)~=0 then goto block_12_fin; end;
                                                                                if ((reg1 ~= reg27) and 1 or 0)~=0 then goto block_509_fin; end;
                                                                                reg30 = bit_tobit(reg1 + 1);
                                                                                reg1 = reg30;
                                                                                
                                                                                reg3 = ((((__UNSIGNED__(reg1) > __UNSIGNED__(17)) and 1 or 0) == 0) and 17 or reg1);
                                                                                reg5 = __LONG_INT__(1,0);
                                                                                
                                                                                while true do ::loop_557_start::
                                                                                    reg9 = reg5;
                                                                                    reg10 = reg6;
                                                                                    if ((reg1 == reg3) and 1 or 0)~=0 then goto block_511_fin; end;
                                                                                    reg5 = (reg9 * __LONG_INT__(10,0));
                                                                                    reg30 = reg7 * __LONG_INT__(10,0);
                                                                                    reg7 = reg30;
                                                                                    reg8 = (bit_tobit(((((reg7):_shr_u(reg14)))[1]) + 48));
                                                                                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + reg2)),reg8);
                                                                                    reg30 = bit_tobit(reg1 + 1);
                                                                                    reg1 = reg30;
                                                                                    reg6 = (reg10 * __LONG_INT__(10,0));
                                                                                    reg30 = (reg7):_and(reg18);
                                                                                    reg7 = reg30;
                                                                                    if ((reg6):_le_u(reg7) and 1 or 0)~=0 then goto loop_557_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                                if ((__UNSIGNED__((bit_tobit(reg1 + -1))) >= __UNSIGNED__(17)) and 1 or 0)~=0 then goto block_510_fin; end;
                                                                                reg14 = (reg6 - reg7);
                                                                                reg3 = ((reg14):_ge_u(reg12) and 1 or 0);
                                                                                reg30 = reg5 * (reg23 - reg20);
                                                                                reg23 = reg30;
                                                                                reg13 = (reg23 + reg5);
                                                                                reg30 = (reg14):_lt_u(reg12) and 1 or 0;
                                                                                reg14 = (reg23 - reg5);
                                                                                if (bit_bor(reg30,((reg14):_le_u(reg7) and 1 or 0)))~=0 then goto block_11_fin; end;
                                                                                reg27 = (bit_tobit((bit_tobit(reg1 + reg2)) + -1));
                                                                                reg23 = ((reg10 * __LONG_INT__(10,0)) - (reg7 + reg12));
                                                                                reg18 = (reg12 - reg14);
                                                                                reg20 = (reg14 - reg7);
                                                                                reg10 = __LONG_INT__(0,0);
                                                                                
                                                                                while true do ::loop_656_start::
                                                                                    reg5 = (reg7 + reg12);
                                                                                    if (((bit_bor(((reg5):_lt_u(reg14) and 1 or 0),(((reg10 + reg20)):_ge_u((reg7 + reg18)) and 1 or 0))) == 0) and 1 or 0)==0 then goto if_672_fin end 
                                                                                        reg3 = 1;
                                                                                        goto block_11_fin;
                                                                                    ::if_672_fin::
                                                                                    reg30 = bit_tobit(reg8 + -1);
                                                                                    reg8 = reg30;
                                                                                    __MEMORY_WRITE_8__(mem_0,reg27,reg8);
                                                                                    reg19 = (reg10 + reg23);
                                                                                    reg3 = ((reg19):_ge_u(reg12) and 1 or 0);
                                                                                    if ((reg5):_ge_u(reg14) and 1 or 0)~=0 then goto block_10_fin; end;
                                                                                    reg30 = reg10 - reg12;
                                                                                    reg10 = reg30;
                                                                                    reg7 = reg5;
                                                                                    if ((reg19):_ge_u(reg12) and 1 or 0)~=0 then goto loop_656_start; end;
                                                                                    break
                                                                                end
                                                                                
                                                                                goto block_10_fin;
                                                                            ::if_515_fin::
                                                                            __FUNCS__.func_82(17,17,1054476);
                                                                            error('unreachable');
                                                                        ::block_511_fin::
                                                                        __FUNCS__.func_82(reg3,17,1054508);
                                                                        error('unreachable');
                                                                    ::block_510_fin::
                                                                    __FUNCS__.func_84(reg1,17,1054524);
                                                                    error('unreachable');
                                                                ::block_509_fin::
                                                                reg30 = bit_tobit(reg1 + 1);
                                                                reg1 = reg30;
                                                                reg30 = __IDIV_U__(reg8,10);
                                                                reg33 = (__UNSIGNED__(reg8) < __UNSIGNED__(10)) and 1 or 0;
                                                                reg8 = reg30;
                                                                if ((reg33 == 0) and 1 or 0)~=0 then goto loop_504_start; end;
                                                                break
                                                            end
                                                            
                                                            __FUNCS__.func_110(1054448,25,1054424);
                                                            error('unreachable');
                                                        ::if_50_fin::
                                                        __FUNCS__.func_110(1054360,45,1054408);
                                                        error('unreachable');
                                                    ::block_46_fin::
                                                    __FUNCS__.func_82(reg1,81,1054248);
                                                    error('unreachable');
                                                ::block_45_fin::
                                                __FUNCS__.func_110(1051892,29,1051956);
                                                error('unreachable');
                                            ::if_44_fin::
                                            __FUNCS__.func_110(1052540,55,1054328);
                                            error('unreachable');
                                        ::if_37_fin::
                                        __FUNCS__.func_110(1052468,54,1054312);
                                        error('unreachable');
                                    ::if_30_fin::
                                    __FUNCS__.func_110(1052424,28,1054296);
                                    error('unreachable');
                                ::if_24_fin::
                                __FUNCS__.func_110(1052376,29,1054280);
                                error('unreachable');
                            ::if_18_fin::
                            __FUNCS__.func_110(1052331,28,1054264);
                            error('unreachable');
                        ::block_12_fin::
                        reg3 = (bit_tobit(reg1 + 1));
                        
                            if ((__UNSIGNED__(reg1) < __UNSIGNED__(17)) and 1 or 0)==0 then goto if_801_fin end 
                                reg6 = (reg19 - reg5);
                                reg9 = (((__LONG_INT__(reg8,0))):_shl(reg14));
                                reg1 = ((reg6):_ge_u(reg9) and 1 or 0);
                                reg14 = (reg23 - reg20);
                                reg12 = (reg14 + __LONG_INT__(1,0));
                                reg8 = reg14 + __LONG_INT__(-1,-1);
                                reg14 = reg8;
                                if (bit_bor(((reg6):_lt_u(reg9) and 1 or 0),((reg14):_le_u(reg5) and 1 or 0)))~=0 then goto block_797_fin; end;
                                reg6 = (((reg24 + reg26) + reg25) + reg22);
                                reg5 = (reg7 + reg9);
                                reg8 = ((((((reg5 + reg15) + reg16) + reg17) + (reg10 * (reg11 - reg21))) - reg24) - reg26) - reg25;
                                reg10 = reg8;
                                reg18 = (__LONG_INT__(0,0) - (reg20 + (reg7 + reg13)));
                                reg20 = (__LONG_INT__(2,0) - (reg29 + (reg5 + reg13)));
                                
                                while true do ::loop_878_start::
                                    reg11 = (reg5 + reg13);
                                    if (((bit_bor(((reg11):_lt_u(reg14) and 1 or 0),(((reg6 + reg18)):_ge_u((reg10 + reg13)) and 1 or 0))) == 0) and 1 or 0)==0 then goto if_894_fin end 
                                        reg5 = (reg7 + reg13);
                                        reg1 = 1;
                                        goto block_797_fin;
                                    ::if_894_fin::
                                    reg8 = bit_tobit(reg32 + -1);
                                    reg32 = reg8;
                                    __MEMORY_WRITE_8__(mem_0,reg31,reg32);
                                    reg8 = reg7 + reg9;
                                    reg7 = reg8;
                                    reg23 = (reg6 + reg20);
                                    if ((reg11):_lt_u(reg14) and 1 or 0)==0 then goto if_920_fin end 
                                        reg8 = reg5 + reg9;
                                        reg5 = reg8;
                                        reg8 = reg9 + reg10;
                                        reg10 = reg8;
                                        reg8 = reg6 - reg9;
                                        reg6 = reg8;
                                        if ((reg23):_ge_u(reg9) and 1 or 0)~=0 then goto loop_878_start; end;
                                    ::if_920_fin::
                                    break
                                end
                                
                                reg1 = ((reg23):_ge_u(reg9) and 1 or 0);
                                reg5 = (reg7 + reg13);
                                goto block_797_fin;
                            ::if_801_fin::
                            __FUNCS__.func_84(reg3,17,1054492);
                            error('unreachable');
                        ::block_797_fin::
                        
                            
                                if (((bit_bor(((reg1 == 0) and 1 or 0),((reg12):_le_u(reg5) and 1 or 0))) == 0) and 1 or 0)==0 then goto if_964_fin end 
                                    reg7 = (reg5 + reg9);
                                    if (bit_bor(((reg7):_lt_u(reg12) and 1 or 0),(((reg12 - reg5)):_ge_u((reg7 - reg12)) and 1 or 0)))~=0 then goto block_956_fin; end;
                                ::if_964_fin::
                                
                                if ((((reg5):_le_u((reg19 + __LONG_INT__(-4,-1))) and 1 or 0) == 0) and 0 or ((reg5):_ge_u(__LONG_INT__(2,0)) and 1 or 0))~=0 then goto block_955_fin; end;
                                __MEMORY_WRITE_32__(mem_0,reg0,0);
                                goto block_9_fin;
                            ::block_956_fin::
                            __MEMORY_WRITE_32__(mem_0,reg0,0);
                            goto block_9_fin;
                        ::block_955_fin::
                        __MEMORY_WRITE_32__(mem_0,reg0+4,reg3);
                        __MEMORY_WRITE_32__(mem_0,reg0,reg2);
                        __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg0 + 8)),reg28);
                        goto block_9_fin;
                    ::block_11_fin::
                    reg5 = reg7;
                ::block_10_fin::
                
                    
                        if (((bit_bor(((reg3 == 0) and 1 or 0),((reg13):_le_u(reg5) and 1 or 0))) == 0) and 1 or 0)==0 then goto if_1027_fin end 
                            reg7 = (reg5 + reg12);
                            if (bit_bor(((reg7):_lt_u(reg13) and 1 or 0),(((reg13 - reg5)):_ge_u((reg7 - reg13)) and 1 or 0)))~=0 then goto block_1019_fin; end;
                        ::if_1027_fin::
                        
                        if ((((reg5):_le_u(((reg9 * __LONG_INT__(-40,-1)) + reg6)) and 1 or 0) == 0) and 0 or (((reg9 * __LONG_INT__(20,0))):_le_u(reg5) and 1 or 0))~=0 then goto block_1018_fin; end;
                        __MEMORY_WRITE_32__(mem_0,reg0,0);
                        goto block_9_fin;
                    ::block_1019_fin::
                    __MEMORY_WRITE_32__(mem_0,reg0,0);
                    goto block_9_fin;
                ::block_1018_fin::
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg1);
                __MEMORY_WRITE_32__(mem_0,reg0,reg2);
                __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg0 + 8)),reg28);
            ::block_9_fin::
            __GLOBALS__[0] = (bit_tobit(reg4 + 48));
            do return  end
        ::block_8_fin::
        __MEMORY_WRITE_32__(mem_0,reg4+24,0);
        __FUNCS__.func_90((bit_tobit(reg4 + 16)),reg4,(bit_tobit(reg4 + 24)));
        error('unreachable');
    end
    function __FUNCS__.func_5()
        local reg0,reg1,reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19;
        reg0 = __GLOBALS__[0];
        reg1 = (bit_tobit(reg0 - 256));
        __GLOBALS__[0] = reg1;
        __FUNCS__.func_176();
        reg0 = __MEMORY_READ_32__(mem_0,reg1+96);
        reg2 = reg0;
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1+88);
        reg3 = reg0;
        
            reg0 = __FUNCS__.func_148(1000000,1);
            reg4 = reg0;
            if reg4==0 then goto if_20_fin end 
                -- FORCE INIT VAR | i32
                reg0 = 0;
                
                while true do ::loop_21_start::
                    reg5 = __FUNCS__.func_65(reg4,1,1000000);
                    reg6 = reg5;
                    reg5 = 3;
                    
                    while true do ::loop_29_start::
                        reg4 = reg5;
                        
                            
                            while true do ::loop_33_start::
                                reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + reg6)));
                                if reg7~=0 then goto block_32_fin; end;
                                reg7 = bit_tobit(reg4 + 2);
                                reg8 = (__UNSIGNED__(reg4) < __UNSIGNED__(998)) and 1 or 0;
                                reg4 = reg7;
                                if reg8~=0 then goto loop_33_start; end;
                                break
                            end
                            
                            reg4 = reg5;
                        ::block_32_fin::
                        reg7 = (__IMUL__(reg4,reg4));
                        if ((__UNSIGNED__(reg7) <= __UNSIGNED__(999999)) and 1 or 0)==0 then goto if_57_fin end 
                            reg5 = (bit_lshift(reg4,1));
                            
                            while true do ::loop_62_start::
                                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg7 + reg6)),0);
                                reg8 = bit_tobit(reg5 + reg7);
                                reg7 = reg8;
                                if ((__UNSIGNED__(reg7) < __UNSIGNED__(1000000)) and 1 or 0)~=0 then goto loop_62_start; end;
                                break
                            end
                            
                        ::if_57_fin::
                        reg5 = (bit_tobit(reg4 + 2));
                        if ((__UNSIGNED__(reg5) < __UNSIGNED__(1000)) and 1 or 0)~=0 then goto loop_29_start; end;
                        break
                    end
                    
                    __FUNCS__.func_176();
                    reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+72);
                    reg9 = __MEMORY_READ_32__(mem_0,reg1+80);
                    __FUNCS__.func_99((bit_tobit(reg1 + 56)),reg8,reg9,reg3,reg2);
                    reg8 = bit_tobit(reg0 + 1);
                    reg0 = reg8;
                    reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+56);
                    if ((reg8):_gt_u(__LONG_INT__(4,0)) and 1 or 0)~=0 then goto block_15_fin; end;
                    __FUNCS__.func_10(reg6);
                    reg8 = __FUNCS__.func_148(1000000,1);
                    reg4 = reg8;
                    if reg4~=0 then goto loop_21_start; end;
                    break
                end
                
            ::if_20_fin::
            __FUNCS__.func_170(1000000,1);
            error('unreachable');
        ::block_15_fin::
        __FUNCS__.func_176();
        reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+40);
        reg9 = __MEMORY_READ_32__(mem_0,reg1+48);
        __FUNCS__.func_99((bit_tobit(reg1 + 24)),reg8,reg9,reg3,reg2);
        reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+24);
        reg3 = reg8;
        reg8 = __MEMORY_READ_32__(mem_0,reg1+32);
        reg5 = reg8;
        (__LONG_INT__(1000000,1000000)):store(mem_0,(bit_tobit(reg1 + 112)));
        __MEMORY_WRITE_32__(mem_0,reg1+108,reg6);
        __MEMORY_WRITE_32__(mem_0,reg1+104,1000000);
        __MEMORY_WRITE_32__(mem_0,reg1+136,reg0);
        __MEMORY_WRITE_32__(mem_0,reg1+128,reg5);
        (reg3):store(mem_0,reg1+120);
        __MEMORY_WRITE_32__(mem_0,reg1+140,1);
        reg4 = 5;
        reg7 = 1;
        
            
                
                while true do ::loop_165_start::
                    reg5 = (bit_tobit(reg4 + reg6));
                    reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg5 + -2)));
                    if reg8==0 then goto if_173_fin end 
                        reg8 = bit_tobit(reg7 + 1);
                        reg7 = reg8;
                        __MEMORY_WRITE_32__(mem_0,reg1+140,reg7);
                    ::if_173_fin::
                    if ((__UNSIGNED__((bit_tobit(reg4 + -2))) > __UNSIGNED__(999998)) and 1 or 0)==0 then goto if_186_fin end 
                        reg5 = (bit_tobit(reg1 + 212));
                        __MEMORY_WRITE_32__(mem_0,reg5,0);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,1048676);
                        (__LONG_INT__(1,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048696);
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        reg7 = 1;
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048712);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,1);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 136)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048736);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,2);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 120)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+120);
                        reg9 = __MEMORY_READ_32__(mem_0,reg1+128);
                        reg10 = __MEMORY_READ_32__(mem_0,reg1+136);
                        __FUNCS__.func_109((bit_tobit(reg1 + 8)),reg8,reg9,reg10);
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        __MEMORY_WRITE_32__(mem_0,reg1+148,2);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048760);
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+16);
                        __MEMORY_WRITE_32__(mem_0,reg1+168,reg8);
                        reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg1+8);
                        (reg8):store(mem_0,reg1+160);
                        __MEMORY_WRITE_32__(mem_0,reg1+144,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 144)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048784);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,1);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 104)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048808);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,3);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 140)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        reg4 = 3;
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+108);
                        reg0 = reg8;
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+104);
                        reg6 = reg8;
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+116);
                        reg5 = reg8;
                        
                        while true do ::loop_367_start::
                            if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_164_fin; end;
                            reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + reg0)));
                            reg9 = bit_tobit(reg7 + reg8);
                            reg7 = reg9;
                            reg8 = bit_tobit(reg4 + 2);
                            reg4 = reg8;
                            if ((__UNSIGNED__(reg4) <= __UNSIGNED__(reg6)) and 1 or 0)~=0 then goto loop_367_start; end;
                            break
                        end
                        
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 212)),1);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,1);
                        __MEMORY_WRITE_32__(mem_0,reg1+144,reg7);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048832);
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 144)));
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __FUNCS__.func_62((bit_tobit(reg1 + 160)));
                        
                            reg9 = __FUNCS__.func_19((bit_tobit(reg1 + 160)),(bit_tobit(reg1 + 104)));
                            if ((reg9 == 0) and 1 or 0)==0 then goto if_431_fin end 
                                reg9 = __MEMORY_READ_32__(mem_0,reg1+176);
                                reg6 = reg9;
                                reg8 = 0; goto block_422_fin;
                            ::if_431_fin::
                            reg5 = (bit_tobit(reg1 + 248));
                            (__LONG_INT__(0,0)):store(mem_0,reg5);
                            reg4 = (bit_tobit(reg1 + 232));
                            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg1+168);
                            reg3 = reg9;
                            (((reg3):_xor(__LONG_INT__(2037671283,1952801890)))):store(mem_0,reg4);
                            reg0 = (bit_tobit(reg1 + 224));
                            (((reg3):_xor(__LONG_INT__(1852075885,1685025377)))):store(mem_0,reg0);
                            reg6 = (bit_tobit(reg1 + 216));
                            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg1+160);
                            reg10 = reg9;
                            (((reg10):_xor(__LONG_INT__(1852142177,1819895653)))):store(mem_0,reg6);
                            (__LONG_INT__(0,0)):store(mem_0,reg1+240);
                            (reg3):store(mem_0,reg1+200);
                            (reg10):store(mem_0,reg1+192);
                            (((reg10):_xor(__LONG_INT__(1886610805,1936682341)))):store(mem_0,reg1+208);
                            reg9 = __MEMORY_READ_32__(mem_0,reg1+104);
                            __FUNCS__.func_24(reg9,(bit_tobit(reg1 + 192)));
                            reg7 = 0;
                            reg9 = __MEMORY_READ_32__(mem_0,reg1+104);
                            reg11 = reg9;
                            
                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg1+240);
                                reg12 = __MEMORY_READ_32__(mem_0,reg5);reg12=__LONG_INT__(reg12,0);
                                reg3 = ((reg9):_or(((reg12):_shl(__LONG_INT__(56,0)))));
                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg4);
                                reg10 = ((reg3):_xor(reg9));
                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg6);
                                reg12 = reg10 + reg9;
                                reg9 = (reg10):_rotl(__LONG_INT__(16,0));
                                reg10 = reg12;
                                reg12 = ((reg9):_xor(reg10));
                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg0);
                                reg13 = reg9;
                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg1+208);
                                reg14 = (reg13 + reg9);
                                reg9 = (reg12 + ((reg14):_rotl(__LONG_INT__(32,0))));
                                reg15 = (reg9):_xor(reg3);
                                reg3 = ((((reg13):_rotl(__LONG_INT__(13,0)))):_xor(reg14));
                                reg16 = reg10 + reg3;
                                reg10 = reg16;
                                reg16 = (reg10):_xor(((reg3):_rotl(__LONG_INT__(17,0))));
                                reg3 = reg16;
                                reg13 = (reg15 + reg3);
                                reg15 = (reg13):_xor(((reg3):_rotl(__LONG_INT__(13,0))));
                                reg3 = reg15;
                                reg15 = (((reg12):_rotl(__LONG_INT__(21,0)))):_xor(reg9);
                                reg12 = reg15;
                                reg15 = reg12 + ((((reg10):_rotl(__LONG_INT__(32,0)))):_xor(__LONG_INT__(255,0)));
                                reg10 = reg15;
                                reg14 = (reg3 + reg10);
                                reg15 = (reg14):_xor(((reg3):_rotl(__LONG_INT__(17,0))));
                                reg3 = reg15;
                                reg15 = (((reg12):_rotl(__LONG_INT__(16,0)))):_xor(reg10);
                                reg10 = reg15;
                                reg12 = (reg10 + ((reg13):_rotl(__LONG_INT__(32,0))));
                                reg15 = reg3 + reg12;
                                reg16 = (reg3):_rotl(__LONG_INT__(13,0));
                                reg3 = reg15;
                                reg13 = ((reg16):_xor(reg3));
                                reg15 = (((reg10):_rotl(__LONG_INT__(21,0)))):_xor(reg12);
                                reg10 = reg15;
                                reg12 = (reg10 + ((reg14):_rotl(__LONG_INT__(32,0))));
                                reg15 = reg13 + reg12;
                                reg16 = (reg13):_rotl(__LONG_INT__(17,0));
                                reg13 = reg15;
                                reg14 = ((reg16):_xor(reg13));
                                reg15 = (((reg10):_rotl(__LONG_INT__(16,0)))):_xor(reg12);
                                reg10 = reg15;
                                reg15 = reg10 + ((reg3):_rotl(__LONG_INT__(32,0)));
                                reg3 = reg15;
                                reg12 = ((((reg14):_rotl(__LONG_INT__(13,0)))):_xor((reg14 + reg3)));
                                reg15 = (((reg10):_rotl(__LONG_INT__(21,0)))):_xor(reg3);
                                reg3 = reg15;
                                reg10 = (reg3 + ((reg13):_rotl(__LONG_INT__(32,0))));
                                reg13 = (reg12 + reg10);
                                reg5 = ((((((((reg13):_xor(((((((reg3):_rotl(__LONG_INT__(16,0)))):_xor(reg10))):_rotl(__LONG_INT__(21,0)))))):_xor(((reg12):_rotl(__LONG_INT__(17,0)))))):_xor(((reg13):_shr_u(__LONG_INT__(32,0))))))[1]);
                                reg15 = (__IMUL__((bit_rshift(reg5,25)),16843009));
                                reg16 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 180)));
                                reg17 = reg16;
                                reg16 = __MEMORY_READ_32__(mem_0,reg1+176);
                                reg6 = reg16;
                                reg2 = (bit_band(reg6,reg5));
                                reg16 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg17 + reg2)));
                                reg4 = reg16;
                                reg5 = (bit_bxor(reg15,reg4));
                                reg0 = (bit_band((bit_band((bit_bxor(reg5,-1)),(bit_tobit(reg5 + -16843009)))),-2139062144));
                                if ((reg0 == 0) and 1 or 0)==0 then goto if_688_fin end 
                                    
                                    while true do ::loop_689_start::
                                        if (bit_band((bit_band(reg4,(bit_lshift(reg4,1)))),-2139062144))~=0 then goto block_497_fin; end;
                                        reg5 = (bit_tobit(reg7 + reg2));
                                        reg16 = bit_tobit(reg7 + 4);
                                        reg7 = reg16;
                                        reg2 = (bit_band(reg6,(bit_tobit(reg5 + 4))));
                                        reg16 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg17 + reg2)));
                                        reg4 = reg16;
                                        reg5 = (bit_bxor(reg4,reg15));
                                        reg0 = (bit_band((bit_band((bit_bxor(reg5,-1)),(bit_tobit(reg5 + -16843009)))),-2139062144));
                                        if ((reg0 == 0) and 1 or 0)~=0 then goto loop_689_start; end;
                                        break
                                    end
                                    
                                ::if_688_fin::
                                reg16 = (bit_tobit((bit_tobit(reg17 - (bit_lshift((bit_band((bit_tobit((bit_rshift((__CTZ__(reg0)),3)) + reg2)),reg6)),3)))) + -8));
                                reg18 = __MEMORY_READ_32__(mem_0,reg16);
                                if ((reg18 == reg11) and 1 or 0)~=0 then goto block_497_fin; end;
                                reg5 = (bit_band((bit_tobit(reg0 + -1)),reg0));
                                
                                while true do ::loop_757_start::
                                    
                                        if reg5==0 then goto if_760_fin end 
                                            reg0 = reg5;
                                            goto block_758_fin;
                                        ::if_760_fin::
                                        
                                        while true do ::loop_765_start::
                                            if (bit_band((bit_band(reg4,(bit_lshift(reg4,1)))),-2139062144))==0 then goto if_773_fin end 
                                                reg16 = 0;
                                                goto block_497_fin;
                                            ::if_773_fin::
                                            reg5 = (bit_tobit(reg7 + reg2));
                                            reg18 = bit_tobit(reg7 + 4);
                                            reg7 = reg18;
                                            reg2 = (bit_band(reg6,(bit_tobit(reg5 + 4))));
                                            reg18 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg17 + reg2)));
                                            reg4 = reg18;
                                            reg5 = (bit_bxor(reg4,reg15));
                                            reg0 = (bit_band((bit_band((bit_bxor(reg5,-1)),(bit_tobit(reg5 + -16843009)))),-2139062144));
                                            if ((reg0 == 0) and 1 or 0)~=0 then goto loop_765_start; end;
                                            break
                                        end
                                        
                                    ::block_758_fin::
                                    reg5 = (bit_band((bit_tobit(reg0 + -1)),reg0));
                                    reg16 = (bit_tobit((bit_tobit(reg17 - (bit_lshift((bit_band((bit_tobit((bit_rshift((__CTZ__(reg0)),3)) + reg2)),reg6)),3)))) + -8));
                                    reg18 = __MEMORY_READ_32__(mem_0,reg16);
                                    if ((reg18 ~= reg11) and 1 or 0)~=0 then goto loop_757_start; end;
                                    break
                                end
                                
                            ::block_497_fin::
                            reg7 = 1;
                            reg4 = 3;
                            reg18 = __MEMORY_READ_32__(mem_0,reg1+108);
                            reg0 = reg18;
                            reg18 = __MEMORY_READ_32__(mem_0,reg1+116);
                            reg5 = reg18;
                            
                            while true do ::loop_849_start::
                                if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_163_fin; end;
                                reg18 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + reg0)));
                                reg19 = bit_tobit(reg7 + reg18);
                                reg7 = reg19;
                                reg18 = bit_tobit(reg4 + 2);
                                reg4 = reg18;
                                if ((__UNSIGNED__(reg4) <= __UNSIGNED__(reg11)) and 1 or 0)~=0 then goto loop_849_start; end;
                                break
                            end
                            
                            if ((reg16 == 0) and 1 or 0)~=0 then reg8 = 0; goto block_422_fin; end;
                            reg18 = __MEMORY_READ_32__(mem_0,reg16+4);
                            reg8 = ((reg18 == reg7) and 1 or 0)
                            -- BLOCK RET (block):
                        ::block_422_fin::
                        reg4 = reg8;
                        
                            if ((reg6 == 0) and 1 or 0)~=0 then goto block_880_fin; end;
                            reg5 = (bit_tobit((bit_lshift(reg6,3)) + 8));
                            if (((bit_tobit((bit_tobit(reg6 + reg5)) + 5)) == 0) and 1 or 0)~=0 then goto block_880_fin; end;
                            reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 180)));
                            __FUNCS__.func_10((bit_tobit(reg8 - reg5)));
                        ::block_880_fin::
                        reg5 = (bit_tobit(reg1 + 212));
                        __MEMORY_WRITE_32__(mem_0,reg5,1);
                        __MEMORY_WRITE_8__(mem_0,reg1+159,reg4);
                        __MEMORY_WRITE_32__(mem_0,reg1+148,4);
                        (__LONG_INT__(2,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048856);
                        __MEMORY_WRITE_32__(mem_0,reg1+144,(bit_tobit(reg1 + 159)));
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 144)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __MEMORY_WRITE_32__(mem_0,reg5,0);
                        __MEMORY_WRITE_32__(mem_0,reg1+208,1048676);
                        (__LONG_INT__(1,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048696);
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        __MEMORY_WRITE_32__(mem_0,reg5,2);
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 172)),5);
                        (__LONG_INT__(3,0)):store(mem_0,reg1+196);
                        __MEMORY_WRITE_32__(mem_0,reg1+192,1048912);
                        __MEMORY_WRITE_32__(mem_0,reg1+164,1);
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+128);
                        reg18 = __LONG_INT__(0,0); reg18:load(mem_0,reg1+120);
                        __MEMORY_WRITE_32F__(mem_0,reg1+144,(((__UNSIGNED__(reg8)) / 1000000000) + (__UNSIGNED__((reg18)[1]) + __UNSIGNED__((reg18)[2])*4294967296)));
                        __MEMORY_WRITE_32__(mem_0,reg1+208,(bit_tobit(reg1 + 160)));
                        __MEMORY_WRITE_32__(mem_0,reg1+168,(bit_tobit(reg1 + 144)));
                        __MEMORY_WRITE_32__(mem_0,reg1+160,(bit_tobit(reg1 + 136)));
                        __FUNCS__.func_12((bit_tobit(reg1 + 192)));
                        reg8 = __MEMORY_READ_32__(mem_0,reg1+112);
                        if reg8==0 then goto if_1001_fin end 
                            reg8 = __MEMORY_READ_32__(mem_0,reg1+108);
                            __FUNCS__.func_10(reg8);
                        ::if_1001_fin::
                        __GLOBALS__[0] = (bit_tobit(reg1 + 256));
                        do return  end
                    ::if_186_fin::
                    if ((reg4 ~= 1000000) and 1 or 0)==0 then goto if_1015_fin end 
                        reg8 = __MEMORY_READ_8__(mem_0,reg5);
                        if reg8==0 then goto if_1018_fin end 
                            reg8 = bit_tobit(reg7 + 1);
                            reg7 = reg8;
                            __MEMORY_WRITE_32__(mem_0,reg1+140,reg7);
                        ::if_1018_fin::
                        reg8 = bit_tobit(reg4 + 4);
                        reg4 = reg8;
                        goto loop_165_start;
                    ::if_1015_fin::
                    break
                end
                
                __FUNCS__.func_82(reg4,1000000,1048676);
                error('unreachable');
            ::block_164_fin::
            __FUNCS__.func_82(reg4,reg5,1048588);
            error('unreachable');
        ::block_163_fin::
        __FUNCS__.func_82(reg4,reg5,1048588);
        error('unreachable');
    end
    function __FUNCS__.func_6(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10;
        
            if ((__UNSIGNED__(reg1) <= __UNSIGNED__(1279)) and 1 or 0)==0 then goto if_6_fin end 
                reg2 = (bit_rshift(reg1,5));
                
                    
                        
                            reg3 = __MEMORY_READ_32__(mem_0,reg0);
                            reg4 = reg3;
                            if reg4==0 then goto if_17_fin end 
                                reg3 = (bit_tobit(reg0 + (bit_lshift(reg4,2))));
                                reg5 = (bit_tobit(reg0 + (bit_lshift((bit_tobit(reg4 + reg2)),2))));
                                reg6 = (bit_tobit(reg4 + -1));
                                reg4 = ((__UNSIGNED__(reg6) > __UNSIGNED__(39)) and 1 or 0);
                                
                                while true do ::loop_39_start::
                                    if reg4~=0 then goto block_11_fin; end;
                                    reg7 = (bit_tobit(reg6 + reg2));
                                    if ((__UNSIGNED__(reg7) >= __UNSIGNED__(40)) and 1 or 0)~=0 then goto block_13_fin; end;
                                    reg8 = __MEMORY_READ_32__(mem_0,reg3);
                                    __MEMORY_WRITE_32__(mem_0,reg5,reg8);
                                    reg8 = bit_tobit(reg5 + -4);
                                    reg5 = reg8;
                                    reg8 = bit_tobit(reg3 + -4);
                                    reg3 = reg8;
                                    reg8 = bit_tobit(reg6 + -1);
                                    reg6 = reg8;
                                    if ((reg6 ~= -1) and 1 or 0)~=0 then goto loop_39_start; end;
                                    break
                                end
                                
                            ::if_17_fin::
                            if ((__UNSIGNED__(reg1) < __UNSIGNED__(32)) and 1 or 0)~=0 then goto block_2_fin; end;
                            __MEMORY_WRITE_32__(mem_0,reg0+4,0);
                            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(64)) and 1 or 0)~=0 then goto block_12_fin; end;
                            goto block_2_fin;
                        ::block_13_fin::
                        __FUNCS__.func_82(reg7,40,1058148);
                        error('unreachable');
                    ::block_12_fin::
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),0);
                    
                    reg3 = ((((__UNSIGNED__(reg2) > __UNSIGNED__(1)) and 1 or 0) == 0) and 1 or reg2);
                    if ((reg3 == 2) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),0);
                    if ((reg3 == 3) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 16)),0);
                    if ((reg3 == 4) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 20)),0);
                    if ((reg3 == 5) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 24)),0);
                    if ((reg3 == 6) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 28)),0);
                    if ((reg3 == 7) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 32)),0);
                    if ((reg3 == 8) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 36)),0);
                    if ((reg3 == 9) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 40)),0);
                    if ((reg3 == 10) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 44)),0);
                    if ((reg3 == 11) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 48)),0);
                    if ((reg3 == 12) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 52)),0);
                    if ((reg3 == 13) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 56)),0);
                    if ((reg3 == 14) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 60)),0);
                    if ((reg3 == 15) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 - -64)),0);
                    if ((reg3 == 16) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 68)),0);
                    if ((reg3 == 17) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 72)),0);
                    if ((reg3 == 18) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 76)),0);
                    if ((reg3 == 19) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 80)),0);
                    if ((reg3 == 20) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 84)),0);
                    if ((reg3 == 21) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 88)),0);
                    if ((reg3 == 22) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 92)),0);
                    if ((reg3 == 23) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 96)),0);
                    if ((reg3 == 24) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 100)),0);
                    if ((reg3 == 25) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 104)),0);
                    if ((reg3 == 26) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 108)),0);
                    if ((reg3 == 27) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 112)),0);
                    if ((reg3 == 28) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 116)),0);
                    if ((reg3 == 29) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 120)),0);
                    if ((reg3 == 30) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 124)),0);
                    if ((reg3 == 31) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 128)),0);
                    if ((reg3 == 32) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 132)),0);
                    if ((reg3 == 33) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 136)),0);
                    if ((reg3 == 34) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 140)),0);
                    if ((reg3 == 35) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 144)),0);
                    if ((reg3 == 36) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 148)),0);
                    if ((reg3 == 37) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 152)),0);
                    if ((reg3 == 38) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 156)),0);
                    if ((reg3 == 39) and 1 or 0)~=0 then goto block_2_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 160)),0);
                    if ((reg3 == 40) and 1 or 0)~=0 then goto block_2_fin; end;
                    __FUNCS__.func_82(40,40,1058148);
                    error('unreachable');
                ::block_11_fin::
                __FUNCS__.func_82(reg6,40,1058148);
                error('unreachable');
            ::if_6_fin::
            __FUNCS__.func_110(1058190,29,1058148);
            error('unreachable');
        ::block_2_fin::
        reg8 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = (bit_tobit(reg8 + reg2));
        reg7 = (bit_band(reg1,31));
        if ((reg7 == 0) and 1 or 0)==0 then goto if_474_fin end 
            __MEMORY_WRITE_32__(mem_0,reg0,reg3);
            do return reg0 end
        ::if_474_fin::
        
            reg6 = (bit_tobit(reg3 + -1));
            if ((__UNSIGNED__(reg6) <= __UNSIGNED__(39)) and 1 or 0)==0 then goto if_488_fin end 
                reg4 = reg3;
                reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg0 + (bit_lshift(reg6,2)))) + 4)));
                reg5 = reg8;
                reg8 = bit_tobit(0 - reg1);
                reg1 = reg8;
                reg6 = (bit_rshift(reg5,reg1));
                if ((reg6 == 0) and 1 or 0)~=0 then goto block_481_fin; end;
                if ((__UNSIGNED__(reg3) <= __UNSIGNED__(39)) and 1 or 0)==0 then goto if_511_fin end 
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg0 + (bit_lshift(reg3,2)))) + 4)),reg6);
                    reg4 = (bit_tobit(reg3 + 1));
                    goto block_481_fin;
                ::if_511_fin::
                __FUNCS__.func_82(reg3,40,1058148);
                error('unreachable');
            ::if_488_fin::
            __FUNCS__.func_82(reg6,40,1058148);
            error('unreachable');
        ::block_481_fin::
        
            reg8 = (bit_tobit(reg2 + 1));
            if ((__UNSIGNED__(reg8) < __UNSIGNED__(reg3)) and 1 or 0)==0 then goto if_546_fin end 
                reg9 = bit_band(reg1,31);
                reg1 = reg9;
                reg6 = (bit_tobit((bit_tobit((bit_lshift(reg3,2)) + reg0)) + -4));
                
                while true do ::loop_559_start::
                    if ((__UNSIGNED__((bit_tobit(reg3 + -2))) >= __UNSIGNED__(40)) and 1 or 0)~=0 then goto block_539_fin; end;
                    reg9 = __MEMORY_READ_32__(mem_0,reg6);
                    reg10 = bit_lshift(reg5,reg7);
                    reg5 = reg9;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 4)),(bit_bor(reg10,(bit_rshift(reg5,reg1)))));
                    reg9 = bit_tobit(reg6 + -4);
                    reg6 = reg9;
                    reg9 = bit_tobit(reg3 + -1);
                    reg3 = reg9;
                    if ((__UNSIGNED__(reg8) < __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto loop_559_start; end;
                    break
                end
                
            ::if_546_fin::
            reg1 = (bit_tobit((bit_tobit(reg0 + (bit_lshift(reg2,2)))) + 4));
            reg2 = __MEMORY_READ_32__(mem_0,reg1);
            __MEMORY_WRITE_32__(mem_0,reg1,(bit_lshift(reg2,reg7)));
            __MEMORY_WRITE_32__(mem_0,reg0,reg4);
            do return reg0 end
        ::block_539_fin::
        __FUNCS__.func_82(-1,40,1058148);
        error('unreachable');
    end
    function __FUNCS__.func_7(reg0, reg1, reg2, reg3, reg4)
        local reg5,reg6,reg7,reg8,reg9,reg10,reg11;
        reg5 = __GLOBALS__[0];
        reg6 = (bit_tobit(reg5 - 112));
        __GLOBALS__[0] = reg6;
        __MEMORY_WRITE_32__(mem_0,reg6+12,reg3);
        __MEMORY_WRITE_32__(mem_0,reg6+8,reg2);
        
            
                
                    
                        
                            
                                
                                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(257)) and 1 or 0)==0 then goto if_25_fin end 
                                        -- FORCE INIT VAR | i32
                                        reg9 = 0;
                                        -- FORCE INIT VAR | i32
                                        reg9 = 0;
                                        -- FORCE INIT VAR | i32
                                        reg9 = 0;
                                        -- FORCE INIT VAR | i32
                                        reg9 = 0;
                                        
                                        while true do ::loop_26_start::
                                            reg10 = (bit_tobit(reg0 + reg9));
                                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg10 + 256)));reg11=bit_arshift(bit_lshift(reg11,24),24);
                                            if ((reg11 > -65) and 1 or 0)~=0 then reg8 = (bit_tobit(reg9 + 256)); goto block_19_fin; end;
                                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg10 + 255)));reg11=bit_arshift(bit_lshift(reg11,24),24);
                                            if ((reg11 > -65) and 1 or 0)~=0 then reg8 = (bit_tobit(reg9 + 255)); goto block_19_fin; end;
                                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg10 + 254)));reg11=bit_arshift(bit_lshift(reg11,24),24);
                                            if ((reg11 > -65) and 1 or 0)~=0 then goto block_20_fin; end;
                                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg10 + 253)));reg11=bit_arshift(bit_lshift(reg11,24),24);
                                            if ((reg11 > -65) and 1 or 0)~=0 then goto block_21_fin; end;
                                            reg11 = bit_tobit(reg9 + -4);
                                            reg9 = reg11;
                                            if ((reg9 ~= -256) and 1 or 0)~=0 then goto loop_26_start; end;
                                            break
                                        end
                                        
                                        reg7 = 0; goto block_18_fin;
                                    ::if_25_fin::
                                    __MEMORY_WRITE_32__(mem_0,reg6+20,reg1);
                                    __MEMORY_WRITE_32__(mem_0,reg6+16,reg0);
                                    __MEMORY_WRITE_32__(mem_0,reg6+24,1054920);
                                    reg5 = 0; goto block_16_fin;
                                ::block_21_fin::
                                reg8 = (bit_tobit(reg9 + 253)); goto block_19_fin;
                            ::block_20_fin::
                            reg8 = (bit_tobit(reg9 + 254))
                            -- BLOCK RET (block):
                        ::block_19_fin::
                        reg10 = reg8;
                        if ((__UNSIGNED__(reg10) >= __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_101_fin end 
                            if ((reg1 == reg10) and 1 or 0)~=0 then reg7 = reg1; goto block_18_fin; end;
                            goto block_14_fin;
                        ::if_101_fin::
                        reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg0 + reg10)));reg8=bit_arshift(bit_lshift(reg8,24),24);
                        if ((reg8 <= -65) and 1 or 0)~=0 then goto block_14_fin; end;
                        reg7 = reg10
                        -- BLOCK RET (block):
                    ::block_18_fin::
                    __MEMORY_WRITE_32__(mem_0,reg6+20,reg7);
                    __MEMORY_WRITE_32__(mem_0,reg6+16,reg0);
                    __MEMORY_WRITE_32__(mem_0,reg6+24,1056140);
                    reg5 = 5
                    -- BLOCK RET (block):
                ::block_16_fin::
                __MEMORY_WRITE_32__(mem_0,reg6+28,reg5);
                
                    
                        
                            
                                
                                    
                                        reg9 = ((__UNSIGNED__(reg2) > __UNSIGNED__(reg1)) and 1 or 0);
                                        if (((bit_bor(reg9,((__UNSIGNED__(reg3) > __UNSIGNED__(reg1)) and 1 or 0))) == 0) and 1 or 0)==0 then goto if_144_fin end 
                                            if ((__UNSIGNED__(reg2) > __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_134_fin; end;
                                            if ((reg2 == 0) and 1 or 0)~=0 then goto block_133_fin; end;
                                            
                                                if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_156_fin end 
                                                    if ((reg1 ~= reg2) and 1 or 0)~=0 then goto block_152_fin; end;
                                                    goto block_133_fin;
                                                ::if_156_fin::
                                                reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg0 + reg2)));reg5=bit_arshift(bit_lshift(reg5,24),24);
                                                if ((reg5 > -65) and 1 or 0)~=0 then goto block_133_fin; end;
                                            ::block_152_fin::
                                            __MEMORY_WRITE_32__(mem_0,reg6+32,reg2);
                                            reg3 = reg2;
                                            goto block_132_fin;
                                        ::if_144_fin::
                                        
                                        __MEMORY_WRITE_32__(mem_0,reg6+40,((reg9 == 0) and reg3 or reg2));
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 68)),3);
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 92)),51);
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 84)),51);
                                        (__LONG_INT__(3,0)):store(mem_0,reg6+52);
                                        __MEMORY_WRITE_32__(mem_0,reg6+48,1056180);
                                        __MEMORY_WRITE_32__(mem_0,reg6+76,1);
                                        __MEMORY_WRITE_32__(mem_0,reg6+64,(bit_tobit(reg6 + 72)));
                                        __MEMORY_WRITE_32__(mem_0,reg6+88,(bit_tobit(reg6 + 24)));
                                        __MEMORY_WRITE_32__(mem_0,reg6+80,(bit_tobit(reg6 + 16)));
                                        __MEMORY_WRITE_32__(mem_0,reg6+72,(bit_tobit(reg6 + 40)));
                                        goto block_13_fin;
                                    ::block_134_fin::
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 100)),51);
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 92)),51);
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 84)),1);
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 68)),4);
                                    (__LONG_INT__(4,0)):store(mem_0,reg6+52);
                                    __MEMORY_WRITE_32__(mem_0,reg6+48,1056240);
                                    __MEMORY_WRITE_32__(mem_0,reg6+76,1);
                                    __MEMORY_WRITE_32__(mem_0,reg6+64,(bit_tobit(reg6 + 72)));
                                    __MEMORY_WRITE_32__(mem_0,reg6+96,(bit_tobit(reg6 + 24)));
                                    __MEMORY_WRITE_32__(mem_0,reg6+88,(bit_tobit(reg6 + 16)));
                                    __MEMORY_WRITE_32__(mem_0,reg6+80,(bit_tobit(reg6 + 12)));
                                    __MEMORY_WRITE_32__(mem_0,reg6+72,(bit_tobit(reg6 + 8)));
                                    goto block_13_fin;
                                ::block_133_fin::
                                __MEMORY_WRITE_32__(mem_0,reg6+32,reg3);
                                if ((reg3 == 0) and 1 or 0)~=0 then goto block_131_fin; end;
                            ::block_132_fin::
                            
                            while true do ::loop_293_start::
                                
                                    reg2 = ((__UNSIGNED__(reg3) < __UNSIGNED__(reg1)) and 1 or 0);
                                    if ((reg2 == 0) and 1 or 0)==0 then goto if_300_fin end 
                                        if ((reg1 == reg3) and 1 or 0)~=0 then goto block_129_fin; end;
                                        goto block_294_fin;
                                    ::if_300_fin::
                                    reg9 = (bit_tobit(reg0 + reg3));
                                    reg5 = __MEMORY_READ_8__(mem_0,reg9);reg5=bit_arshift(bit_lshift(reg5,24),24);
                                    if ((reg5 < -64) and 1 or 0)~=0 then goto block_294_fin; end;
                                    
                                        if ((reg2 == 0) and 1 or 0)==0 then goto if_318_fin end 
                                            if ((reg1 ~= reg3) and 1 or 0)~=0 then goto block_315_fin; end;
                                            goto block_129_fin;
                                        ::if_318_fin::
                                        reg5 = __MEMORY_READ_8__(mem_0,reg9);reg5=bit_arshift(bit_lshift(reg5,24),24);
                                        if ((reg5 > -65) and 1 or 0)~=0 then goto block_130_fin; end;
                                    ::block_315_fin::
                                    __FUNCS__.func_7(reg0,reg1,reg3,reg1,reg4);
                                    error('unreachable');
                                ::block_294_fin::
                                reg5 = bit_tobit(reg3 + -1);
                                reg3 = reg5;
                                if reg3~=0 then goto loop_293_start; end;
                                break
                            end
                            
                        ::block_131_fin::
                        reg3 = 0;
                    ::block_130_fin::
                    if ((reg1 == reg3) and 1 or 0)~=0 then goto block_129_fin; end;
                    reg9 = 1;
                    
                        
                            
                                reg2 = (bit_tobit(reg0 + reg3));
                                reg5 = __MEMORY_READ_8__(mem_0,reg2);reg5=bit_arshift(bit_lshift(reg5,24),24);
                                reg10 = reg5;
                                if ((reg10 <= -1) and 1 or 0)==0 then goto if_366_fin end 
                                    reg5 = bit_tobit(reg0 + reg1);
                                    reg1 = reg5;
                                    reg0 = reg1;
                                    if ((reg1 ~= (bit_tobit(reg2 + 1))) and 1 or 0)==0 then goto if_377_fin end 
                                        reg5 = __MEMORY_READ_8__(mem_0,reg2+1);
                                        reg7 = (bit_band(reg5,63));
                                        reg0 = (bit_tobit(reg2 + 2));
                                    ::if_377_fin::
                                    reg5 = (bit_band(reg10,31));
                                    if ((__UNSIGNED__((bit_band(reg10,255))) > __UNSIGNED__(223)) and 1 or 0)~=0 then goto block_357_fin; end;
                                    reg10 = (bit_bor(reg7,(bit_lshift(reg5,6))));
                                    goto block_356_fin;
                                ::if_366_fin::
                                __MEMORY_WRITE_32__(mem_0,reg6+36,(bit_band(reg10,255)));
                                goto block_355_fin;
                            ::block_357_fin::
                            reg2 = 0;
                            reg9 = reg1;
                            if ((reg0 ~= reg1) and 1 or 0)==0 then goto if_420_else end 
                                reg9 = (bit_tobit(reg0 + 1));
                                reg11 = __MEMORY_READ_8__(mem_0,reg0);
                                reg8 = (bit_band(reg11,63))
                            goto if_420_fin
                            ::if_420_else::
                                reg8 = reg2
                                -- BLOCK RET (if):
                            ::if_420_fin::
                            reg0 = (bit_bor(reg8,(bit_lshift(reg7,6))));
                            if ((__UNSIGNED__((bit_band(reg10,255))) < __UNSIGNED__(240)) and 1 or 0)==0 then goto if_441_fin end 
                                reg10 = (bit_bor(reg0,(bit_lshift(reg5,12))));
                                goto block_356_fin;
                            ::if_441_fin::
                            reg10 = 0;
                            if ((reg1 ~= reg9) and 1 or 0)==0 then goto if_455_else end 
                                reg7 = __MEMORY_READ_8__(mem_0,reg9);
                                reg2 = (bit_band(reg7,63))
                            goto if_455_fin
                            ::if_455_else::
                                reg2 = reg10
                                -- BLOCK RET (if):
                            ::if_455_fin::
                            reg10 = (bit_bor(reg2,(bit_bor((bit_band((bit_lshift(reg5,18)),1835008)),(bit_lshift(reg0,6))))));
                            if ((reg10 == 1114112) and 1 or 0)~=0 then goto block_129_fin; end;
                        ::block_356_fin::
                        __MEMORY_WRITE_32__(mem_0,reg6+36,reg10);
                        reg9 = 1;
                        if ((__UNSIGNED__(reg10) < __UNSIGNED__(128)) and 1 or 0)~=0 then goto block_355_fin; end;
                        reg9 = 2;
                        if ((__UNSIGNED__(reg10) < __UNSIGNED__(2048)) and 1 or 0)~=0 then goto block_355_fin; end;
                        
                        reg9 = ((((__UNSIGNED__(reg10) < __UNSIGNED__(65536)) and 1 or 0) == 0) and 4 or 3);
                    ::block_355_fin::
                    __MEMORY_WRITE_32__(mem_0,reg6+40,reg3);
                    __MEMORY_WRITE_32__(mem_0,reg6+44,(bit_tobit(reg3 + reg9)));
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 68)),5);
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 108)),51);
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 100)),51);
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 92)),54);
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 84)),55);
                    (__LONG_INT__(5,0)):store(mem_0,reg6+52);
                    __MEMORY_WRITE_32__(mem_0,reg6+48,1056324);
                    __MEMORY_WRITE_32__(mem_0,reg6+76,1);
                    __MEMORY_WRITE_32__(mem_0,reg6+64,(bit_tobit(reg6 + 72)));
                    __MEMORY_WRITE_32__(mem_0,reg6+104,(bit_tobit(reg6 + 24)));
                    __MEMORY_WRITE_32__(mem_0,reg6+96,(bit_tobit(reg6 + 16)));
                    __MEMORY_WRITE_32__(mem_0,reg6+88,(bit_tobit(reg6 + 40)));
                    __MEMORY_WRITE_32__(mem_0,reg6+80,(bit_tobit(reg6 + 36)));
                    __MEMORY_WRITE_32__(mem_0,reg6+72,(bit_tobit(reg6 + 32)));
                    goto block_13_fin;
                ::block_129_fin::
                __FUNCS__.func_110(1055017,43,reg4);
                error('unreachable');
            ::block_14_fin::
            __FUNCS__.func_7(reg0,reg1,0,reg10,1056124);
            error('unreachable');
        ::block_13_fin::
        __FUNCS__.func_122((bit_tobit(reg6 + 48)),reg4);
        error('unreachable');
    end
    function __FUNCS__.func_8(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15;
        reg3 = __MEMORY_READ_32__(mem_0,reg0+16);
        reg4 = reg3;
        
            
                
                    
                        reg3 = __MEMORY_READ_32__(mem_0,reg0+8);
                        reg5 = reg3;
                        if ((reg5 ~= 1) and 1 or 0)==0 then goto if_14_fin end 
                            if ((reg4 == 1) and 1 or 0)~=0 then goto block_8_fin; end;
                            reg3 = __MEMORY_READ_32__(mem_0,reg0+24);
                            reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                            reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                            reg6 = __TABLE_FUNCS_0__[reg7+1](reg3,reg1,reg2);
                            reg4 = reg6;
                            goto block_6_fin;
                        ::if_14_fin::
                        if ((reg4 ~= 1) and 1 or 0)~=0 then goto block_7_fin; end;
                    ::block_8_fin::
                    reg3 = (bit_tobit(reg1 + reg2));
                    
                        
                            reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
                            reg7 = reg6;
                            if ((reg7 == 0) and 1 or 0)==0 then goto if_49_fin end 
                                reg4 = reg1;
                                goto block_42_fin;
                            ::if_49_fin::
                            reg4 = reg1;
                            -- FORCE INIT VAR | i32
                            reg6 = 0;
                            
                            while true do ::loop_56_start::
                                reg8 = reg4;
                                if ((reg8 == reg3) and 1 or 0)~=0 then goto block_41_fin; end;
                                reg4 = (bit_tobit(reg8 + 1));
                                
                                    reg9 = __MEMORY_READ_8__(mem_0,reg8);reg9=bit_arshift(bit_lshift(reg9,24),24);
                                    reg10 = reg9;
                                    if ((reg10 > -1) and 1 or 0)~=0 then goto block_66_fin; end;
                                    reg9 = (bit_band(reg10,255));
                                    
                                        if ((reg4 == reg3) and 1 or 0)==0 then goto if_81_fin end 
                                            reg12 = 0;
                                            reg11 = reg3; goto block_77_fin;
                                        ::if_81_fin::
                                        reg13 = __MEMORY_READ_8__(mem_0,reg8+1);
                                        reg12 = (bit_band(reg13,63));
                                        reg11 = (bit_tobit(reg8 + 2))
                                        -- BLOCK RET (block):
                                    ::block_77_fin::
                                    reg4 = reg11;
                                    if ((__UNSIGNED__(reg9) < __UNSIGNED__(224)) and 1 or 0)~=0 then goto block_66_fin; end;
                                    
                                        if ((reg4 == reg3) and 1 or 0)==0 then goto if_105_fin end 
                                            reg13 = 0;
                                            reg11 = reg3; goto block_101_fin;
                                        ::if_105_fin::
                                        reg14 = __MEMORY_READ_8__(mem_0,reg4);
                                        reg13 = (bit_band(reg14,63));
                                        reg11 = (bit_tobit(reg4 + 1))
                                        -- BLOCK RET (block):
                                    ::block_101_fin::
                                    reg10 = reg11;
                                    if ((__UNSIGNED__(reg9) < __UNSIGNED__(240)) and 1 or 0)==0 then goto if_124_fin end 
                                        reg4 = reg10;
                                        goto block_66_fin;
                                    ::if_124_fin::
                                    
                                        if ((reg3 == reg10) and 1 or 0)==0 then goto if_133_fin end 
                                            reg4 = reg3;
                                            reg11 = 0; goto block_129_fin;
                                        ::if_133_fin::
                                        reg4 = (bit_tobit(reg10 + 1));
                                        reg14 = __MEMORY_READ_8__(mem_0,reg10);
                                        reg11 = (bit_band(reg14,63))
                                        -- BLOCK RET (block):
                                    ::block_129_fin::
                                    if (((bit_bor(reg11,(bit_bor((bit_bor((bit_band((bit_lshift(reg9,18)),1835008)),(bit_lshift(reg12,12)))),(bit_lshift(reg13,6)))))) == 1114112) and 1 or 0)~=0 then goto block_41_fin; end;
                                ::block_66_fin::
                                reg11 = bit_tobit((bit_tobit(reg6 - reg8)) + reg4);
                                reg6 = reg11;
                                reg11 = bit_tobit(reg7 + -1);
                                reg7 = reg11;
                                if reg7~=0 then goto loop_56_start; end;
                                break
                            end
                            
                        ::block_42_fin::
                        if ((reg4 == reg3) and 1 or 0)~=0 then goto block_41_fin; end;
                        
                            reg11 = __MEMORY_READ_8__(mem_0,reg4);reg11=bit_arshift(bit_lshift(reg11,24),24);
                            reg8 = reg11;
                            if ((reg8 > -1) and 1 or 0)~=0 then goto block_183_fin; end;
                            
                                if ((reg3 == (bit_tobit(reg4 + 1))) and 1 or 0)==0 then goto if_196_fin end 
                                    reg7 = reg3;
                                    reg11 = 0; goto block_190_fin;
                                ::if_196_fin::
                                reg7 = (bit_tobit(reg4 + 2));
                                reg14 = __MEMORY_READ_8__(mem_0,reg4+1);
                                reg11 = (bit_lshift((bit_band(reg14,63)),6))
                                -- BLOCK RET (block):
                            ::block_190_fin::
                            if ((__UNSIGNED__((bit_band(reg8,255))) < __UNSIGNED__(224)) and 1 or 0)~=0 then goto block_183_fin; end;
                            
                                if ((reg3 == reg7) and 1 or 0)==0 then goto if_223_fin end 
                                    reg10 = reg3;
                                    reg14 = 0; goto block_219_fin;
                                ::if_223_fin::
                                reg10 = (bit_tobit(reg7 + 1));
                                reg15 = __MEMORY_READ_8__(mem_0,reg7);
                                reg14 = (bit_band(reg15,63))
                                -- BLOCK RET (block):
                            ::block_219_fin::
                            if ((__UNSIGNED__((bit_band(reg8,255))) < __UNSIGNED__(240)) and 1 or 0)~=0 then goto block_183_fin; end;
                            reg15 = bit_band(reg8,255);
                            reg8 = reg15;
                            reg4 = (bit_bor(reg11,reg14));
                            if ((reg3 == reg10) and 1 or 0)==0 then goto if_253_else end 
                                reg11 = 0
                            goto if_253_fin
                            ::if_253_else::
                                reg14 = __MEMORY_READ_8__(mem_0,reg10);
                                reg11 = (bit_band(reg14,63))
                                -- BLOCK RET (if):
                            ::if_253_fin::
                            if (((bit_bor(reg11,(bit_bor((bit_band((bit_lshift(reg8,18)),1835008)),(bit_lshift(reg4,6)))))) == 1114112) and 1 or 0)~=0 then goto block_41_fin; end;
                        ::block_183_fin::
                        
                            
                                if ((reg6 == 0) and 1 or 0)==0 then goto if_278_fin end 
                                    reg3 = 0;
                                    goto block_275_fin;
                                ::if_278_fin::
                                if ((__UNSIGNED__(reg6) >= __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_286_fin end 
                                    reg4 = 0;
                                    reg3 = reg2;
                                    if ((reg6 == reg3) and 1 or 0)~=0 then goto block_275_fin; end;
                                    goto block_274_fin;
                                ::if_286_fin::
                                reg4 = 0;
                                reg3 = reg6;
                                reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg3 + reg1)));reg8=bit_arshift(bit_lshift(reg8,24),24);
                                if ((reg8 < -64) and 1 or 0)~=0 then goto block_274_fin; end;
                            ::block_275_fin::
                            reg6 = reg3;
                            reg4 = reg1;
                        ::block_274_fin::
                        
                        reg8 = (reg4 == 0) and reg2 or reg6;
                        reg2 = reg8;
                        
                        reg8 = (reg4 == 0) and reg1 or reg4;
                        reg1 = reg8;
                    ::block_41_fin::
                    if ((reg5 == 1) and 1 or 0)~=0 then goto block_7_fin; end;
                    goto block_5_fin;
                ::block_7_fin::
                reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                reg7 = reg5;
                
                    if ((reg2 == 0) and 1 or 0)==0 then goto if_337_fin end 
                        reg3 = 0;
                        goto block_334_fin;
                    ::if_337_fin::
                    reg6 = (bit_band(reg2,3));
                    
                        if ((__UNSIGNED__((bit_tobit(reg2 + -1))) < __UNSIGNED__(3)) and 1 or 0)==0 then goto if_352_fin end 
                            reg3 = 0;
                            reg4 = reg1;
                            goto block_346_fin;
                        ::if_352_fin::
                        reg3 = 0;
                        reg10 = (bit_tobit(0 - (bit_band(reg2,-4))));
                        reg4 = reg1;
                        
                        while true do ::loop_369_start::
                            reg5 = __MEMORY_READ_8__(mem_0,reg4);
                            reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 1)));
                            reg11 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 2)));
                            reg14 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 3)));
                            reg15 = bit_tobit((bit_tobit((bit_tobit((bit_tobit(reg3 + (((bit_band(reg5,192)) ~= 128) and 1 or 0))) + (((bit_band(reg8,192)) ~= 128) and 1 or 0))) + (((bit_band(reg11,192)) ~= 128) and 1 or 0))) + (((bit_band(reg14,192)) ~= 128) and 1 or 0));
                            reg3 = reg15;
                            reg5 = bit_tobit(reg4 + 4);
                            reg4 = reg5;
                            reg5 = bit_tobit(reg10 + 4);
                            reg10 = reg5;
                            if reg10~=0 then goto loop_369_start; end;
                            break
                        end
                        
                    ::block_346_fin::
                    if ((reg6 == 0) and 1 or 0)~=0 then goto block_334_fin; end;
                    
                    while true do ::loop_420_start::
                        reg5 = __MEMORY_READ_8__(mem_0,reg4);
                        reg8 = bit_tobit(reg3 + (((bit_band(reg5,192)) ~= 128) and 1 or 0));
                        reg3 = reg8;
                        reg5 = bit_tobit(reg4 + 1);
                        reg4 = reg5;
                        reg5 = bit_tobit(reg6 + -1);
                        reg6 = reg5;
                        if reg6~=0 then goto loop_420_start; end;
                        break
                    end
                    
                ::block_334_fin::
                if ((__UNSIGNED__(reg7) > __UNSIGNED__(reg3)) and 1 or 0)==0 then goto if_444_fin end 
                    reg4 = 0;
                    reg5 = bit_tobit(reg7 - reg3);
                    reg3 = reg5;
                    reg7 = reg3;
                    
                        
                            
                                reg5 = __MEMORY_READ_8__(mem_0,reg0+32);
                                reg6 = reg5;
                                
                                
                                if (bit_tobit((bit_band(((((reg6 == 3) and 1 or 0) == 0) and reg6 or 0),3)) - 1)) == 0 then goto block_454_fin;
                                elseif (bit_tobit((bit_band(((((reg6 == 3) and 1 or 0) == 0) and reg6 or 0),3)) - 1)) == 1 then goto block_453_fin;
                                else goto block_452_fin;
                                end
                            ::block_454_fin::
                            reg7 = 0;
                            reg4 = reg3;
                            goto block_452_fin;
                        ::block_453_fin::
                        reg4 = (bit_rshift(reg3,1));
                        reg7 = (bit_rshift((bit_tobit(reg3 + 1)),1));
                    ::block_452_fin::
                    reg5 = bit_tobit(reg4 + 1);
                    reg4 = reg5;
                    reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg3 = reg5;
                    reg5 = __MEMORY_READ_32__(mem_0,reg0+4);
                    reg6 = reg5;
                    reg5 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg0 = reg5;
                    
                        
                        while true do ::loop_502_start::
                            reg5 = bit_tobit(reg4 + -1);
                            reg4 = reg5;
                            if ((reg4 == 0) and 1 or 0)~=0 then goto block_501_fin; end;
                            reg5 = __MEMORY_READ_32__(mem_0,reg3+16);
                            reg5 = __TABLE_FUNCS_0__[reg5+1](reg0,reg6);
                            if ((reg5 == 0) and 1 or 0)~=0 then goto loop_502_start; end;
                            break
                        end
                        
                        do return 1 end
                    ::block_501_fin::
                    reg4 = 1;
                    if ((reg6 == 1114112) and 1 or 0)~=0 then goto block_6_fin; end;
                    reg5 = __MEMORY_READ_32__(mem_0,reg3+12);
                    reg5 = __TABLE_FUNCS_0__[reg5+1](reg0,reg1,reg2);
                    if reg5~=0 then goto block_6_fin; end;
                    reg4 = 0;
                    
                    while true do ::loop_535_start::
                        if ((reg4 == reg7) and 1 or 0)==0 then goto if_539_fin end 
                            do return 0 end
                        ::if_539_fin::
                        reg5 = bit_tobit(reg4 + 1);
                        reg4 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,reg3+16);
                        reg5 = __TABLE_FUNCS_0__[reg5+1](reg0,reg6);
                        if ((reg5 == 0) and 1 or 0)~=0 then goto loop_535_start; end;
                        break
                    end
                    
                    do return ((__UNSIGNED__((bit_tobit(reg4 + -1))) < __UNSIGNED__(reg7)) and 1 or 0) end
                ::if_444_fin::
                goto block_5_fin;
            ::block_6_fin::
            do return reg4 end
        ::block_5_fin::
        reg4 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg0 = __MEMORY_READ_32__(mem_0,reg5+12);
        reg0 = __TABLE_FUNCS_0__[reg0+1](reg4,reg1,reg2);
        do return reg0; end;
    end
    function __FUNCS__.func_9(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11;
        reg4 = __GLOBALS__[0];
        reg5 = (bit_tobit(reg4 - 96));
        __GLOBALS__[0] = reg5;
        (reg1):store(mem_0,reg5+8);
        __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg5 + 24)),48);
        (__LONG_INT__(808464432,808464432)):store(mem_0,reg5+16);
        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
        reg6 = reg4;
        reg4 = __MEMORY_READ_32__(mem_0,reg0+16);
        reg7 = reg4;
        
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_26_fin; end;
            
                
                reg4 = ((reg7 == 0) and 9 or reg6);
                if ((reg4 == 0) and 1 or 0)==0 then goto if_37_fin end 
                    if ((__UNSIGNED__((__IMUL__(reg3,5))) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_26_fin; end;
                    goto block_30_fin;
                ::if_37_fin::
                
                    
                        if ((reg3 == 0) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg8 = (__IDIV_U__(reg2,reg3));
                        __MEMORY_WRITE_8__(mem_0,reg5+16,(bit_tobit(reg8 + 48)));
                        reg9 = (__IDIV_U__(reg3,10));
                        reg10 = bit_tobit(reg2 - (__IMUL__(reg3,reg8)));
                        reg8 = reg10;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_70_fin end 
                            reg8 = 1;
                            goto block_26_fin;
                        ::if_70_fin::
                        if ((reg4 == 1) and 1 or 0)~=0 then goto block_46_fin; end;
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(10)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = (__IDIV_U__(reg8,reg9));
                        __MEMORY_WRITE_8__(mem_0,reg5+17,(bit_tobit(reg10 + 48)));
                        reg2 = (__IDIV_U__(reg3,100));
                        reg11 = bit_tobit(reg8 - (__IMUL__(reg9,reg10)));
                        reg8 = reg11;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_102_fin end 
                            reg8 = 2;
                            goto block_26_fin;
                        ::if_102_fin::
                        if ((reg4 == 2) and 1 or 0)==0 then goto if_110_fin end 
                            reg9 = reg2;
                            goto block_46_fin;
                        ::if_110_fin::
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(100)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = (__IDIV_U__(reg8,reg2));
                        __MEMORY_WRITE_8__(mem_0,reg5+18,(bit_tobit(reg10 + 48)));
                        reg9 = (__IDIV_U__(reg3,1000));
                        reg11 = bit_tobit(reg8 - (__IMUL__(reg2,reg10)));
                        reg8 = reg11;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_138_fin end 
                            reg8 = 3;
                            goto block_26_fin;
                        ::if_138_fin::
                        if ((reg4 == 3) and 1 or 0)~=0 then goto block_46_fin; end;
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(1000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = (__IDIV_U__(reg8,reg9));
                        __MEMORY_WRITE_8__(mem_0,reg5+19,(bit_tobit(reg10 + 48)));
                        reg2 = (__IDIV_U__(reg3,10000));
                        reg11 = bit_tobit(reg8 - (__IMUL__(reg9,reg10)));
                        reg8 = reg11;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_170_fin end 
                            reg8 = 4;
                            goto block_26_fin;
                        ::if_170_fin::
                        if ((reg4 == 4) and 1 or 0)==0 then goto if_178_fin end 
                            reg9 = reg2;
                            goto block_46_fin;
                        ::if_178_fin::
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(10000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = (__IDIV_U__(reg8,reg2));
                        __MEMORY_WRITE_8__(mem_0,reg5+20,(bit_tobit(reg10 + 48)));
                        reg9 = (__IDIV_U__(reg3,100000));
                        reg11 = bit_tobit(reg8 - (__IMUL__(reg2,reg10)));
                        reg8 = reg11;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_206_fin end 
                            reg8 = 5;
                            goto block_26_fin;
                        ::if_206_fin::
                        if ((reg4 == 5) and 1 or 0)~=0 then goto block_46_fin; end;
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(100000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = (__IDIV_U__(reg8,reg9));
                        __MEMORY_WRITE_8__(mem_0,reg5+21,(bit_tobit(reg10 + 48)));
                        reg2 = (__IDIV_U__(reg3,1000000));
                        reg11 = bit_tobit(reg8 - (__IMUL__(reg9,reg10)));
                        reg8 = reg11;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_238_fin end 
                            reg8 = 6;
                            goto block_26_fin;
                        ::if_238_fin::
                        if ((reg4 == 6) and 1 or 0)==0 then goto if_246_fin end 
                            reg9 = reg2;
                            goto block_46_fin;
                        ::if_246_fin::
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(1000000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg10 = bit_band(reg8,65535);
                        reg8 = reg10;
                        __MEMORY_WRITE_8__(mem_0,reg5+22,(bit_tobit((__IDIV_U__(reg8,reg2)) + 48)));
                        reg9 = (__IDIV_U__(reg3,10000000));
                        reg10 = __IMOD_U__(reg8,reg2);
                        reg8 = reg10;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_274_fin end 
                            reg8 = 7;
                            goto block_26_fin;
                        ::if_274_fin::
                        if ((reg4 == 7) and 1 or 0)~=0 then goto block_46_fin; end;
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(10000000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        __MEMORY_WRITE_8__(mem_0,reg5+23,(bit_tobit((__IDIV_U__(reg8,reg9)) + 48)));
                        reg2 = (__IDIV_U__(reg3,100000000));
                        reg10 = __IMOD_U__(reg8,reg9);
                        reg8 = reg10;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_303_fin end 
                            reg8 = 8;
                            goto block_26_fin;
                        ::if_303_fin::
                        if ((reg4 == 8) and 1 or 0)==0 then goto if_311_fin end 
                            reg9 = reg2;
                            goto block_46_fin;
                        ::if_311_fin::
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(100000000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        __MEMORY_WRITE_8__(mem_0,reg5+24,(bit_tobit((__IDIV_U__(reg8,reg2)) + 48)));
                        reg10 = __IMOD_U__(reg8,reg2);
                        reg8 = reg10;
                        if ((reg8 == 0) and 1 or 0)==0 then goto if_332_fin end 
                            reg8 = 9;
                            goto block_26_fin;
                        ::if_332_fin::
                        reg9 = (__IDIV_U__(reg3,1000000000));
                        if ((reg4 == 9) and 1 or 0)~=0 then goto block_46_fin; end;
                        if ((__UNSIGNED__(reg3) < __UNSIGNED__(1000000000)) and 1 or 0)~=0 then goto block_47_fin; end;
                        __FUNCS__.func_82(9,9,1056492);
                        error('unreachable');
                    ::block_47_fin::
                    __FUNCS__.func_110(1054448,25,1056476);
                    error('unreachable');
                ::block_46_fin::
                if ((__UNSIGNED__(reg8) < __UNSIGNED__((__IMUL__(reg9,5)))) and 1 or 0)==0 then goto if_366_fin end 
                    reg8 = reg4;
                    goto block_26_fin;
                ::if_366_fin::
                reg2 = (bit_tobit(reg4 + -1));
                
                while true do ::loop_375_start::
                    
                        reg3 = reg2;
                        reg2 = (bit_tobit(reg3 + (bit_tobit(reg5 + 16))));
                        reg10 = __MEMORY_READ_8__(mem_0,reg2);
                        reg9 = reg10;
                        reg10 = reg2;
                        reg2 = ((__UNSIGNED__(reg9) < __UNSIGNED__(57)) and 1 or 0);
                        
                        __MEMORY_WRITE_8__(mem_0,reg10,((reg2 == 0) and 48 or (bit_tobit(reg9 + 1))));
                        if reg2~=0 then goto block_376_fin; end;
                        reg2 = (bit_tobit(reg3 + -1));
                        if reg3~=0 then goto loop_375_start; end;
                    ::block_376_fin::
                    break
                end
                
                if ((__UNSIGNED__(reg9) >= __UNSIGNED__(57)) and 1 or 0)~=0 then goto block_30_fin; end;
                reg8 = reg4;
                goto block_26_fin;
            ::block_30_fin::
            ((reg1 + __LONG_INT__(1,0))):store(mem_0,reg5+8);
            reg8 = reg4;
        ::block_26_fin::
        
            
                
                
                reg2 = ((reg7 == 0) and reg8 or ((((__UNSIGNED__(reg6) < __UNSIGNED__(9)) and 1 or 0) == 0) and 9 or reg6));
                if ((reg2 == 0) and 1 or 0)==0 then goto if_435_fin end 
                    __MEMORY_WRITE_32__(mem_0,reg5+52,56);
                    reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg2 = reg4;
                    __MEMORY_WRITE_32__(mem_0,reg5+48,(bit_tobit(reg5 + 8)));
                    reg4 = __MEMORY_READ_32__(mem_0,reg0+24);
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 92)),1);
                    (__LONG_INT__(1,0)):store(mem_0,reg5+76);
                    __MEMORY_WRITE_32__(mem_0,reg5+72,1055060);
                    __MEMORY_WRITE_32__(mem_0,reg5+88,(bit_tobit(reg5 + 48)));
                    reg9 = __FUNCS__.func_27(reg4,reg2,(bit_tobit(reg5 + 72)));
                    reg1 = reg9; goto block_423_fin;
                ::if_435_fin::
                if ((__UNSIGNED__(reg2) >= __UNSIGNED__(10)) and 1 or 0)~=0 then goto block_422_fin; end;
                __MEMORY_WRITE_32__(mem_0,reg5+36,reg2);
                __MEMORY_WRITE_32__(mem_0,reg5+32,(bit_tobit(reg5 + 16)));
                
                __MEMORY_WRITE_32__(mem_0,reg5+44,((reg7 == 0) and reg8 or reg6));
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 68)),50);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 60)),51);
                __MEMORY_WRITE_32__(mem_0,reg5+52,56);
                reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                reg2 = reg4;
                __MEMORY_WRITE_32__(mem_0,reg5+64,(bit_tobit(reg5 + 44)));
                __MEMORY_WRITE_32__(mem_0,reg5+56,(bit_tobit(reg5 + 32)));
                __MEMORY_WRITE_32__(mem_0,reg5+48,(bit_tobit(reg5 + 8)));
                reg4 = __MEMORY_READ_32__(mem_0,reg0+24);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 92)),3);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 84)),2);
                __MEMORY_WRITE_32__(mem_0,reg5+80,1056540);
                __MEMORY_WRITE_32__(mem_0,reg5+76,2);
                __MEMORY_WRITE_32__(mem_0,reg5+72,1056524);
                __MEMORY_WRITE_32__(mem_0,reg5+88,(bit_tobit(reg5 + 48)));
                reg0 = __FUNCS__.func_27(reg4,reg2,(bit_tobit(reg5 + 72)));
                reg1 = reg0
                -- BLOCK RET (block):
            ::block_423_fin::
            __GLOBALS__[0] = (bit_tobit(reg5 + 96));
            do return reg1 end
        ::block_422_fin::
        __FUNCS__.func_84(reg2,9,1056508);
        error('unreachable');
    end
    function __FUNCS__.func_10(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9;
        reg1 = __FUNCS__.func_175(reg0);
        reg0 = reg1;
        reg1 = __FUNCS__.func_166(reg0);
        reg2 = reg1;
        reg1 = __FUNCS__.func_172(reg0,reg2);
        reg3 = reg1;
        
            
                
                    reg1 = __FUNCS__.func_167(reg0);
                    if reg1~=0 then goto block_12_fin; end;
                    reg1 = __MEMORY_READ_32__(mem_0,reg0);
                    reg4 = reg1;
                    
                        reg1 = __FUNCS__.func_156(reg0);
                        if ((reg1 == 0) and 1 or 0)==0 then goto if_23_fin end 
                            reg1 = bit_tobit(reg2 + reg4);
                            reg2 = reg1;
                            reg1 = __FUNCS__.func_173(reg0,reg4);
                            reg0 = reg1;
                            reg1 = __MEMORY_READ_32__(mem_0,1059604);
                            if ((reg0 ~= reg1) and 1 or 0)~=0 then goto block_19_fin; end;
                            reg1 = __MEMORY_READ_32__(mem_0,reg3+4);
                            if (((bit_band(reg1,3)) ~= 3) and 1 or 0)~=0 then goto block_12_fin; end;
                            __MEMORY_WRITE_32__(mem_0,1059596,reg2);
                            __FUNCS__.func_131(reg0,reg2,reg3);
                            do return  end
                        ::if_23_fin::
                        reg0 = (bit_tobit((bit_tobit(reg2 + reg4)) + 16));
                        goto block_11_fin;
                    ::block_19_fin::
                    if ((__UNSIGNED__(reg4) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_63_fin end 
                        __FUNCS__.func_54(reg0);
                        goto block_12_fin;
                    ::if_63_fin::
                    reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                    reg5 = reg1;
                    reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                    reg6 = reg1;
                    if ((reg5 ~= reg6) and 1 or 0)==0 then goto if_79_fin end 
                        __MEMORY_WRITE_32__(mem_0,reg6+12,reg5);
                        __MEMORY_WRITE_32__(mem_0,reg5+8,reg6);
                        goto block_12_fin;
                    ::if_79_fin::
                    reg1 = __MEMORY_READ_32__(mem_0,1059196);
                    __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg1,(bit_rol(-2,(bit_rshift(reg4,3)))))));
                ::block_12_fin::
                
                    reg1 = __FUNCS__.func_151(reg3);
                    if reg1==0 then goto if_102_fin end 
                        __FUNCS__.func_131(reg0,reg2,reg3);
                        goto block_99_fin;
                    ::if_102_fin::
                    
                        
                            
                                reg1 = __MEMORY_READ_32__(mem_0,1059608);
                                if ((reg1 ~= reg3) and 1 or 0)==0 then goto if_116_fin end 
                                    reg1 = __MEMORY_READ_32__(mem_0,1059604);
                                    if ((reg3 ~= reg1) and 1 or 0)~=0 then goto block_111_fin; end;
                                    __MEMORY_WRITE_32__(mem_0,1059604,reg0);
                                    reg1 = __MEMORY_READ_32__(mem_0,1059596);
                                    reg3 = (bit_tobit(reg1 + reg2));
                                    __MEMORY_WRITE_32__(mem_0,1059596,reg3);
                                    __FUNCS__.func_140(reg0,reg3);
                                    do return  end
                                ::if_116_fin::
                                __MEMORY_WRITE_32__(mem_0,1059608,reg0);
                                reg1 = __MEMORY_READ_32__(mem_0,1059600);
                                reg3 = (bit_tobit(reg1 + reg2));
                                __MEMORY_WRITE_32__(mem_0,1059600,reg3);
                                __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg3,1)));
                                reg1 = __MEMORY_READ_32__(mem_0,1059604);
                                if ((reg0 == reg1) and 1 or 0)~=0 then goto block_110_fin; end;
                                goto block_109_fin;
                            ::block_111_fin::
                            reg1 = __FUNCS__.func_166(reg3);
                            reg4 = reg1;
                            reg1 = bit_tobit(reg4 + reg2);
                            reg2 = reg1;
                            
                                if ((__UNSIGNED__(reg4) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_169_fin end 
                                    __FUNCS__.func_54(reg3);
                                    goto block_165_fin;
                                ::if_169_fin::
                                reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 12)));
                                reg5 = reg1;
                                reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 8)));
                                reg3 = reg1;
                                if ((reg5 ~= reg3) and 1 or 0)==0 then goto if_185_fin end 
                                    __MEMORY_WRITE_32__(mem_0,reg3+12,reg5);
                                    __MEMORY_WRITE_32__(mem_0,reg5+8,reg3);
                                    goto block_165_fin;
                                ::if_185_fin::
                                reg1 = __MEMORY_READ_32__(mem_0,1059196);
                                __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg1,(bit_rol(-2,(bit_rshift(reg4,3)))))));
                            ::block_165_fin::
                            __FUNCS__.func_140(reg0,reg2);
                            reg1 = __MEMORY_READ_32__(mem_0,1059604);
                            if ((reg0 ~= reg1) and 1 or 0)~=0 then goto block_99_fin; end;
                            __MEMORY_WRITE_32__(mem_0,1059596,reg2);
                            goto block_11_fin;
                        ::block_110_fin::
                        __MEMORY_WRITE_32__(mem_0,1059596,0);
                        __MEMORY_WRITE_32__(mem_0,1059604,0);
                    ::block_109_fin::
                    reg1 = __MEMORY_READ_32__(mem_0,1059636);
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_11_fin; end;
                    reg1 = __FUNCS__.func_174(0);
                    reg0 = reg1;
                    reg1 = __FUNCS__.func_143(reg0,8);
                    reg7 = __FUNCS__.func_143(20,8);
                    reg8 = __FUNCS__.func_143(16,8);
                    reg9 = bit_tobit((bit_band((bit_tobit((bit_tobit(reg0 - (bit_tobit((bit_tobit(reg1 + reg7)) + reg8)))) + -65544)),-9)) + -3);
                    reg0 = reg9;
                    reg1 = __FUNCS__.func_143(16,8);
                    reg3 = (bit_tobit(0 - (bit_lshift(reg1,2))));
                    
                    if ((((((__UNSIGNED__(reg3) > __UNSIGNED__(reg0)) and 1 or 0) == 0) and reg3 or reg0) == 0) and 1 or 0)~=0 then goto block_11_fin; end;
                    reg1 = __MEMORY_READ_32__(mem_0,1059608);
                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_11_fin; end;
                    reg1 = __FUNCS__.func_174(0);
                    reg0 = reg1;
                    reg1 = __FUNCS__.func_143(reg0,8);
                    reg3 = reg1;
                    reg1 = __FUNCS__.func_143(20,8);
                    reg2 = reg1;
                    reg1 = __FUNCS__.func_143(16,8);
                    reg5 = reg1;
                    
                        reg1 = __MEMORY_READ_32__(mem_0,1059600);
                        reg6 = reg1;
                        reg1 = bit_tobit(reg5 + (bit_tobit(reg2 + (bit_tobit(reg3 - reg0)))));
                        reg2 = reg1;
                        if ((__UNSIGNED__(reg6) <= __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_285_fin; end;
                        reg1 = __MEMORY_READ_32__(mem_0,1059608);
                        reg3 = reg1;
                        reg0 = 1059620;
                        
                            
                            while true do ::loop_305_start::
                                reg1 = __MEMORY_READ_32__(mem_0,reg0);
                                if ((__UNSIGNED__(reg1) <= __UNSIGNED__(reg3)) and 1 or 0)==0 then goto if_310_fin end 
                                    reg1 = __FUNCS__.func_158(reg0);
                                    if ((__UNSIGNED__(reg1) > __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_304_fin; end;
                                ::if_310_fin::
                                reg1 = __MEMORY_READ_32__(mem_0,reg0+8);
                                reg0 = reg1;
                                if reg0~=0 then goto loop_305_start; end;
                                break
                            end
                            
                            reg0 = 0;
                        ::block_304_fin::
                        reg1 = __FUNCS__.func_168(reg0);
                        if reg1~=0 then goto block_285_fin; end;
                        reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                        goto block_285_fin;
                    ::block_285_fin::
                    reg1 = __FUNCS__.func_56();
                    if ((0 ~= (bit_tobit(0 - reg1))) and 1 or 0)~=0 then goto block_11_fin; end;
                    reg1 = __MEMORY_READ_32__(mem_0,1059600);
                    reg5 = __MEMORY_READ_32__(mem_0,1059636);
                    if ((__UNSIGNED__(reg1) <= __UNSIGNED__(reg5)) and 1 or 0)~=0 then goto block_11_fin; end;
                    __MEMORY_WRITE_32__(mem_0,1059636,-1);
                    do return  end
                ::block_99_fin::
                if ((__UNSIGNED__(reg2) < __UNSIGNED__(256)) and 1 or 0)~=0 then goto block_10_fin; end;
                __FUNCS__.func_52(reg0,reg2);
                reg1 = __MEMORY_READ_32__(mem_0,1059644);
                reg0 = (bit_tobit(reg1 + -1));
                __MEMORY_WRITE_32__(mem_0,1059644,reg0);
                if reg0~=0 then goto block_11_fin; end;
                reg1 = __FUNCS__.func_56();
                do return  end
            ::block_11_fin::
            do return  end
        ::block_10_fin::
        reg4 = (bit_rshift(reg2,3));
        reg3 = (bit_tobit((bit_lshift(reg4,3)) + 1059204));
        
            reg5 = __MEMORY_READ_32__(mem_0,1059196);
            reg2 = reg5;
            reg5 = bit_lshift(1,reg4);
            reg4 = reg5;
            if (bit_band(reg2,reg4))==0 then goto if_391_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,reg3+8);
                reg1 = reg5; goto block_382_fin;
            ::if_391_fin::
            __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg2,reg4)));
            reg1 = reg3
            -- BLOCK RET (block):
        ::block_382_fin::
        reg4 = reg1;
        __MEMORY_WRITE_32__(mem_0,reg3+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg4+12,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0+12,reg3);
        __MEMORY_WRITE_32__(mem_0,reg0+8,reg4);
    end
    function __FUNCS__.func_11(reg0, reg1, reg2, reg3, reg4)
        local reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18;
        
            
                
                    
                        
                            
                                reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg1);
                                reg6 = reg5;
                                if (((((reg6)[1] == 0) and ((reg6)[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_14_fin end 
                                    if ((reg6):_gt_u(__LONG_INT__(-1,536870911)) and 1 or 0)~=0 then goto block_8_fin; end;
                                    if ((reg3 == 0) and 1 or 0)~=0 then goto block_6_fin; end;
                                    reg5 = __MEMORY_READ_16__(mem_0,reg1+24);
                                    reg1 = reg5;
                                    reg5 = bit_tobit(reg1 + -32);
                                    reg7 = reg1;
                                    reg1 = ((reg6):_lt_u(__LONG_INT__(0,1)) and 1 or 0);
                                    
                                    reg8 = ((reg1 == 0) and reg7 or reg5);
                                    
                                    reg5 = (reg1 == 0) and reg6 or ((reg6):_shl(__LONG_INT__(32,0)));
                                    reg6 = reg5;
                                    reg1 = ((reg6):_lt_u(__LONG_INT__(0,65536)) and 1 or 0);
                                    
                                    reg5 = (reg1 == 0) and reg8 or (bit_tobit(reg8 + -16));
                                    reg8 = reg5;
                                    
                                    reg5 = (reg1 == 0) and reg6 or ((reg6):_shl(__LONG_INT__(16,0)));
                                    reg6 = reg5;
                                    reg1 = ((reg6):_lt_u(__LONG_INT__(0,16777216)) and 1 or 0);
                                    
                                    reg5 = (reg1 == 0) and reg8 or (bit_tobit(reg8 + -8));
                                    reg8 = reg5;
                                    
                                    reg5 = (reg1 == 0) and reg6 or ((reg6):_shl(__LONG_INT__(8,0)));
                                    reg6 = reg5;
                                    reg1 = ((reg6):_lt_u(__LONG_INT__(0,268435456)) and 1 or 0);
                                    
                                    reg5 = (reg1 == 0) and reg8 or (bit_tobit(reg8 + -4));
                                    reg8 = reg5;
                                    
                                    reg5 = (reg1 == 0) and reg6 or ((reg6):_shl(__LONG_INT__(4,0)));
                                    reg6 = reg5;
                                    reg1 = ((reg6):_lt_u(__LONG_INT__(0,1073741824)) and 1 or 0);
                                    
                                    
                                    reg5 = (reg1 == 0) and reg6 or ((reg6):_shl(__LONG_INT__(2,0)));
                                    reg6 = reg5;
                                    reg5 = bit_tobit(((reg1 == 0) and reg8 or (bit_tobit(reg8 + -2))) + (bit_bxor(((((reg6):_shr_s(__LONG_INT__(63,0))))[1]),-1)));
                                    reg8 = reg5;
                                    reg1 = (__IDIV_S__((bit_tobit((__IMUL__((bit_arshift((bit_lshift((bit_tobit(-96 - reg8)),16)),16)),80)) + 86960)),2126));
                                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(81)) and 1 or 0)~=0 then goto block_7_fin; end;
                                    reg5 = bit_lshift(reg1,4);
                                    reg1 = reg5;
                                    reg5 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg1 + 1052914)));
                                    reg7 = reg5;
                                    
                                        
                                            
                                                reg9 = __LONG_INT__(0,0); reg9:load(mem_0,(bit_tobit(reg1 + 1052904)));
                                                reg10 = reg9;
                                                reg9 = ((reg10):_and(__LONG_INT__(-1,0)));
                                                reg11 = (reg6):_shl(((((reg6):_xor(__LONG_INT__(-1,-1)))):_shr_u(__LONG_INT__(63,0))));
                                                reg6 = reg11;
                                                reg11 = ((reg6):_shr_u(__LONG_INT__(32,0)));
                                                reg12 = (reg9 * reg11);
                                                reg13 = (reg10):_shr_u(__LONG_INT__(32,0));
                                                reg10 = reg13;
                                                reg13 = (reg6):_and(__LONG_INT__(-1,0));
                                                reg6 = reg13;
                                                reg13 = reg10 * reg6;
                                                reg14 = ((reg12):_shr_u(__LONG_INT__(32,0))) + (reg10 * reg11);
                                                reg10 = reg13;
                                                reg13 = (reg14 + ((reg10):_shr_u(__LONG_INT__(32,0)))) + (((((((reg12):_and(__LONG_INT__(-1,0))) + (((reg6 * reg9)):_shr_u(__LONG_INT__(32,0)))) + ((reg10):_and(__LONG_INT__(-1,0)))) + __LONG_INT__(-2147483648,0))):_shr_u(__LONG_INT__(32,0)));
                                                reg9 = reg13;
                                                reg13 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg1 + 1052912)));
                                                reg1 = (bit_tobit(-64 - (bit_tobit(reg8 + reg13))));
                                                reg6 = (__LONG_INT__((bit_band(reg1,63)),0));
                                                reg8 = ((((reg9):_shr_u(reg6)))[1]);
                                                if ((__UNSIGNED__(reg8) >= __UNSIGNED__(10000)) and 1 or 0)==0 then goto if_211_fin end 
                                                    if ((__UNSIGNED__(reg8) < __UNSIGNED__(1000000)) and 1 or 0)~=0 then goto block_133_fin; end;
                                                    if ((__UNSIGNED__(reg8) < __UNSIGNED__(100000000)) and 1 or 0)~=0 then goto block_132_fin; end;
                                                    reg13 = ((__UNSIGNED__(reg8) < __UNSIGNED__(1000000000)) and 1 or 0);
                                                    
                                                    reg14 = ((reg13 == 0) and 9 or 8);
                                                    
                                                    reg5 = ((reg13 == 0) and 1000000000 or 100000000); goto block_131_fin;
                                                ::if_211_fin::
                                                if ((__UNSIGNED__(reg8) >= __UNSIGNED__(100)) and 1 or 0)==0 then goto if_237_fin end 
                                                    reg13 = ((__UNSIGNED__(reg8) < __UNSIGNED__(1000)) and 1 or 0);
                                                    
                                                    reg14 = ((reg13 == 0) and 3 or 2);
                                                    
                                                    reg5 = ((reg13 == 0) and 1000 or 100); goto block_131_fin;
                                                ::if_237_fin::
                                                reg14 = ((__UNSIGNED__(reg8) > __UNSIGNED__(9)) and 1 or 0);
                                                
                                                reg5 = ((((__UNSIGNED__(reg8) < __UNSIGNED__(10)) and 1 or 0) == 0) and 10 or 1); goto block_131_fin;
                                            ::block_133_fin::
                                            reg13 = ((__UNSIGNED__(reg8) < __UNSIGNED__(100000)) and 1 or 0);
                                            
                                            reg14 = ((reg13 == 0) and 5 or 4);
                                            
                                            reg5 = ((reg13 == 0) and 100000 or 10000); goto block_131_fin;
                                        ::block_132_fin::
                                        reg13 = ((__UNSIGNED__(reg8) < __UNSIGNED__(10000000)) and 1 or 0);
                                        
                                        reg14 = ((reg13 == 0) and 7 or 6);
                                        
                                        reg5 = ((reg13 == 0) and 10000000 or 1000000)
                                        -- BLOCK RET (block):
                                    ::block_131_fin::
                                    reg13 = reg5;
                                    reg10 = ((__LONG_INT__(1,0)):_shl(reg6));
                                    
                                        reg5 = bit_arshift((bit_tobit((bit_lshift((bit_tobit(reg14 - reg7)),16)) + 65536)),16);
                                        reg7 = reg5;
                                        reg5 = (bit_arshift((bit_lshift(reg4,16)),16));
                                        if ((reg7 > reg5) and 1 or 0)==0 then goto if_314_fin end 
                                            reg12 = (reg10 + __LONG_INT__(-1,-1));
                                            reg15 = (reg9):_and(reg12);
                                            reg9 = reg15;
                                            reg15 = (bit_band(reg1,65535));
                                            
                                            reg16 = (((__UNSIGNED__((bit_tobit(reg7 - reg5))) < __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg3 or (bit_arshift((bit_lshift((bit_tobit(reg7 - reg4)),16)),16));
                                            reg5 = reg16;
                                            reg16 = (bit_tobit(reg5 + -1));
                                            reg1 = 0;
                                            
                                            while true do ::loop_346_start::
                                                reg17 = (__IDIV_U__(reg8,reg13));
                                                if ((reg1 == reg3) and 1 or 0)~=0 then goto block_5_fin; end;
                                                reg18 = bit_tobit(reg8 - (__IMUL__(reg13,reg17)));
                                                reg8 = reg18;
                                                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + reg2)),(bit_tobit(reg17 + 48)));
                                                if ((reg1 == reg16) and 1 or 0)~=0 then goto block_4_fin; end;
                                                if ((reg1 == reg14) and 1 or 0)~=0 then goto block_296_fin; end;
                                                reg17 = bit_tobit(reg1 + 1);
                                                reg1 = reg17;
                                                reg17 = __IDIV_U__(reg13,10);
                                                reg18 = (__UNSIGNED__(reg13) < __UNSIGNED__(10)) and 1 or 0;
                                                reg13 = reg17;
                                                if ((reg18 == 0) and 1 or 0)~=0 then goto loop_346_start; end;
                                                break
                                            end
                                            
                                            __FUNCS__.func_110(1054448,25,1054660);
                                            error('unreachable');
                                        ::if_314_fin::
                                        __FUNCS__.func_34(reg0,reg2,reg3,0,reg7,reg4,((reg9):_div_u(__LONG_INT__(10,0))),(((__LONG_INT__(reg13,0))):_shl(reg6)),reg10);
                                        do return  end
                                    ::block_296_fin::
                                    reg17 = bit_tobit(reg1 + 1);
                                    reg1 = reg17;
                                    
                                    reg8 = ((((__UNSIGNED__(reg1) > __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg3 or reg1);
                                    reg17 = (__LONG_INT__((bit_band((bit_tobit(reg15 + -1)),63)),0));
                                    reg11 = __LONG_INT__(1,0);
                                    
                                    while true do ::loop_432_start::
                                        if (((((((reg11):_shr_u(reg17)))[1] == 0) and ((((reg11):_shr_u(reg17)))[2] == 0) and 1 or 0) == 0) and 1 or 0)==0 then goto if_438_fin end 
                                            __MEMORY_WRITE_32__(mem_0,reg0,0);
                                            do return  end
                                        ::if_438_fin::
                                        if ((reg1 == reg8) and 1 or 0)~=0 then goto block_3_fin; end;
                                        reg15 = reg11 * __LONG_INT__(10,0);
                                        reg11 = reg15;
                                        reg15 = (reg9 * __LONG_INT__(10,0));
                                        reg9 = ((reg15):_and(reg12));
                                        __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + reg2)),(bit_tobit(((((reg15):_shr_u(reg6)))[1]) + 48)));
                                        reg15 = bit_tobit(reg1 + 1);
                                        reg1 = reg15;
                                        if ((reg5 ~= reg1) and 1 or 0)~=0 then goto loop_432_start; end;
                                        break
                                    end
                                    
                                    __FUNCS__.func_34(reg0,reg2,reg3,reg5,reg7,reg4,reg9,reg10,reg11);
                                    do return  end
                                ::if_14_fin::
                                __FUNCS__.func_110(1052331,28,1054576);
                                error('unreachable');
                            ::block_8_fin::
                            __FUNCS__.func_110(1054592,36,1054628);
                            error('unreachable');
                        ::block_7_fin::
                        __FUNCS__.func_82(reg1,81,1054248);
                        error('unreachable');
                    ::block_6_fin::
                    __FUNCS__.func_110(1054540,33,1054644);
                    error('unreachable');
                ::block_5_fin::
                __FUNCS__.func_82(reg3,reg3,1054676);
                error('unreachable');
            ::block_4_fin::
            __FUNCS__.func_34(reg0,reg2,reg3,reg5,reg7,reg4,((((__LONG_INT__(reg8,0))):_shl(reg6)) + reg9),(((__LONG_INT__(reg13,0))):_shl(reg6)),reg10);
            do return  end
        ::block_3_fin::
        __FUNCS__.func_82(reg8,reg3,1054692);
        error('unreachable');
    end
    function __FUNCS__.func_12(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6,reg7;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 80));
        __GLOBALS__[0] = reg2;
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg0 + 16)));
        (reg1):store(mem_0,(bit_tobit(reg2 + 16)));
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg0 + 8)));
        (reg1):store(mem_0,(bit_tobit(reg2 + 8)));
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg0);
        (reg1):store(mem_0,reg2);
        __MEMORY_WRITE_32__(mem_0,reg2+28,6);
        __MEMORY_WRITE_32__(mem_0,reg2+24,1050488);
        
            
                reg1 = __MEMORY_READ_8__(mem_0,1059657);
                if ((reg1 == 0) and 1 or 0)~=0 then goto block_35_fin; end;
                reg1 = __MEMORY_READ_32__(mem_0,1059176);
                if ((reg1 ~= 1) and 1 or 0)==0 then goto if_44_fin end 
                    (__LONG_INT__(1,0)):store(mem_0,1059176);
                    goto block_35_fin;
                ::if_44_fin::
                reg1 = __MEMORY_READ_32__(mem_0,1059180);
                reg0 = reg1;
                __MEMORY_WRITE_32__(mem_0,1059180,0);
                if ((reg0 == 0) and 1 or 0)~=0 then goto block_35_fin; end;
                reg1 = __MEMORY_READ_8__(mem_0,reg0+8);
                reg3 = reg1;
                reg1 = 1;
                __MEMORY_WRITE_8__(mem_0,reg0+8,1);
                reg4 = bit_band(reg3,1);
                reg3 = reg4;
                __MEMORY_WRITE_8__(mem_0,reg2+40,reg3);
                if ((reg3 == 0) and 1 or 0)==0 then goto if_75_fin end 
                    reg4 = __MEMORY_READ_32__(mem_0,1059144);
                    if (bit_band(reg4,2147483647))==0 then goto if_80_fin end 
                        reg4 = __FUNCS__.func_134();
                        reg1 = reg4;
                    ::if_80_fin::
                    __MEMORY_WRITE_8__(mem_0,reg2+44,4);
                    __MEMORY_WRITE_32__(mem_0,reg2+40,(bit_tobit(reg0 + 12)));
                    reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg2 + 16)));
                    (reg4):store(mem_0,(bit_tobit(reg2 + 72)));
                    reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg2 + 8)));
                    (reg4):store(mem_0,(bit_tobit(reg2 - -64)));
                    reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg2);
                    (reg4):store(mem_0,reg2+56);
                    reg4 = __FUNCS__.func_27((bit_tobit(reg2 + 40)),1050544,(bit_tobit(reg2 + 56)));
                    reg5 = reg4;
                    reg4 = __MEMORY_READ_8__(mem_0,reg2+44);
                    reg3 = reg4;
                    
                        if reg5==0 then goto if_126_fin end 
                            if (bit_bor(((reg3 == 4) and 1 or 0),((reg3 ~= 3) and 1 or 0)))~=0 then goto block_124_fin; end;
                            reg4 = __MEMORY_READ_32__(mem_0,reg2+45);reg4=__LONG_INT__(reg4,0);
                            reg6 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg2 + 49)));reg6=__LONG_INT__(reg6,0);
                            reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg2 + 51)));reg7=__LONG_INT__(reg7,0);
                            reg3 = ((((((reg4):_or(((((reg6):_or(((reg7):_shl(__LONG_INT__(16,0)))))):_shl(__LONG_INT__(32,0)))))):_shr_u(__LONG_INT__(24,0))))[1]);
                            reg4 = __MEMORY_READ_32__(mem_0,reg3);
                            reg6 = __MEMORY_READ_32__(mem_0,reg3+4);
                            reg7 = __MEMORY_READ_32__(mem_0,reg6);
                            __TABLE_FUNCS_0__[reg7+1](reg4);
                            reg4 = __MEMORY_READ_32__(mem_0,reg3+4);
                            reg5 = reg4;
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+4);
                            if reg4==0 then goto if_164_fin end 
                                reg4 = __MEMORY_READ_32__(mem_0,reg5+8);
                                reg4 = __MEMORY_READ_32__(mem_0,reg3);
                                __FUNCS__.func_10(reg4);
                            ::if_164_fin::
                            __FUNCS__.func_10(reg3);
                            goto block_124_fin;
                        ::if_126_fin::
                        if ((reg3 ~= 3) and 1 or 0)~=0 then goto block_124_fin; end;
                        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 48)));
                        reg3 = reg4;
                        reg4 = __MEMORY_READ_32__(mem_0,reg3);
                        reg6 = __MEMORY_READ_32__(mem_0,reg3+4);
                        reg7 = __MEMORY_READ_32__(mem_0,reg6);
                        __TABLE_FUNCS_0__[reg7+1](reg4);
                        reg4 = __MEMORY_READ_32__(mem_0,reg3+4);
                        reg5 = reg4;
                        reg4 = __MEMORY_READ_32__(mem_0,reg5+4);
                        if reg4==0 then goto if_194_fin end 
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+8);
                            reg4 = __MEMORY_READ_32__(mem_0,reg3);
                            __FUNCS__.func_10(reg4);
                        ::if_194_fin::
                        reg4 = __MEMORY_READ_32__(mem_0,reg2+48);
                        __FUNCS__.func_10(reg4);
                    ::block_124_fin::
                    
                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_206_fin; end;
                        reg1 = __MEMORY_READ_32__(mem_0,1059144);
                        if (((bit_band(reg1,2147483647)) == 0) and 1 or 0)~=0 then goto block_206_fin; end;
                        reg1 = __FUNCS__.func_134();
                        if reg1~=0 then goto block_206_fin; end;
                        __MEMORY_WRITE_8__(mem_0,reg0+9,1);
                    ::block_206_fin::
                    __MEMORY_WRITE_8__(mem_0,reg0+8,0);
                    reg1 = __MEMORY_READ_32__(mem_0,1059180);
                    reg3 = reg1;
                    __MEMORY_WRITE_32__(mem_0,1059180,reg0);
                    if ((reg3 == 0) and 1 or 0)~=0 then goto block_34_fin; end;
                    reg1 = __MEMORY_READ_32__(mem_0,reg3);
                    reg0 = reg1;
                    __MEMORY_WRITE_32__(mem_0,reg3,(bit_tobit(reg0 + -1)));
                    if ((reg0 ~= 1) and 1 or 0)~=0 then goto block_34_fin; end;
                    __FUNCS__.func_106(reg3);
                    goto block_34_fin;
                ::if_75_fin::
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 76)),0);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 72)),1049032);
                (__LONG_INT__(1,0)):store(mem_0,reg2+60);
                __MEMORY_WRITE_32__(mem_0,reg2+56,1051628);
                __FUNCS__.func_88((bit_tobit(reg2 + 40)),(bit_tobit(reg2 + 56)));
                error('unreachable');
            ::block_35_fin::
            
                reg1 = __MEMORY_READ_32__(mem_0,1059104);
                if ((reg1 == 3) and 1 or 0)~=0 then goto block_274_fin; end;
                __MEMORY_WRITE_32__(mem_0,reg2+32,1059108);
                reg1 = __MEMORY_READ_32__(mem_0,1059104);
                if ((reg1 == 3) and 1 or 0)~=0 then goto block_274_fin; end;
                __MEMORY_WRITE_32__(mem_0,reg2+40,(bit_tobit(reg2 + 32)));
                __MEMORY_WRITE_32__(mem_0,reg2+56,(bit_tobit(reg2 + 40)));
                __FUNCS__.func_21((bit_tobit(reg2 + 56)));
            ::block_274_fin::
            __MEMORY_WRITE_32__(mem_0,reg2+32,1059108);
            __MEMORY_WRITE_8__(mem_0,reg2+44,4);
            __MEMORY_WRITE_32__(mem_0,reg2+40,(bit_tobit(reg2 + 32)));
            reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg2 + 16)));
            (reg1):store(mem_0,(bit_tobit(reg2 + 72)));
            reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg2 + 8)));
            (reg1):store(mem_0,(bit_tobit(reg2 - -64)));
            reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg2);
            (reg1):store(mem_0,reg2+56);
            reg1 = __FUNCS__.func_27((bit_tobit(reg2 + 40)),1050520,(bit_tobit(reg2 + 56)));
            reg3 = reg1;
            reg1 = __MEMORY_READ_8__(mem_0,reg2+44);
            reg0 = reg1;
            
                
                    if reg3==0 then goto if_350_fin end 
                        if ((reg0 ~= 4) and 1 or 0)~=0 then goto block_348_fin; end;
                        reg0 = 2;
                        reg1 = __LONG_INT__(-1879048152,4103); goto block_347_fin;
                    ::if_350_fin::
                    if ((reg0 ~= 3) and 1 or 0)~=0 then goto block_34_fin; end;
                    reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 48)));
                    reg0 = reg4;
                    reg4 = __MEMORY_READ_32__(mem_0,reg0);
                    reg5 = __MEMORY_READ_32__(mem_0,reg0+4);
                    reg6 = __MEMORY_READ_32__(mem_0,reg5);
                    __TABLE_FUNCS_0__[reg6+1](reg4);
                    reg4 = __MEMORY_READ_32__(mem_0,reg0+4);
                    reg3 = reg4;
                    reg4 = __MEMORY_READ_32__(mem_0,reg3+4);
                    if reg4==0 then goto if_378_fin end 
                        reg4 = __MEMORY_READ_32__(mem_0,reg3+8);
                        reg3 = __MEMORY_READ_32__(mem_0,reg0);
                        __FUNCS__.func_10(reg3);
                    ::if_378_fin::
                    reg3 = __MEMORY_READ_32__(mem_0,reg2+48);
                    __FUNCS__.func_10(reg3);
                    goto block_34_fin;
                ::block_348_fin::
                reg3 = __MEMORY_READ_32__(mem_0,reg2+45);reg3=__LONG_INT__(reg3,0);
                reg4 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg2 + 49)));reg4=__LONG_INT__(reg4,0);
                reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg2 + 51)));reg5=__LONG_INT__(reg5,0);
                reg1 = ((reg3):_or(((((reg4):_or(((reg5):_shl(__LONG_INT__(16,0)))))):_shl(__LONG_INT__(32,0)))))
                -- BLOCK RET (block):
            ::block_347_fin::
            reg3 = reg1;
            (((reg3):_shr_u(__LONG_INT__(24,0)))):store32(mem_0,reg2+36);
            __MEMORY_WRITE_32__(mem_0,reg2+32,(bit_bor((bit_lshift(((reg3)[1]),8)),reg0)));
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 76)),2);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 52)),8);
            (__LONG_INT__(2,0)):store(mem_0,reg2+60);
            __MEMORY_WRITE_32__(mem_0,reg2+56,1050456);
            __MEMORY_WRITE_32__(mem_0,reg2+44,7);
            __MEMORY_WRITE_32__(mem_0,reg2+72,(bit_tobit(reg2 + 40)));
            __MEMORY_WRITE_32__(mem_0,reg2+48,(bit_tobit(reg2 + 32)));
            __MEMORY_WRITE_32__(mem_0,reg2+40,(bit_tobit(reg2 + 24)));
            __FUNCS__.func_119((bit_tobit(reg2 + 56)));
            error('unreachable');
        ::block_34_fin::
        __GLOBALS__[0] = (bit_tobit(reg2 + 80));
    end
    function __FUNCS__.func_13(reg0, reg1, reg2, reg3, reg4, reg5)
        local reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16;
        
            if reg1==0 then goto if_4_fin end 
                reg7 = __MEMORY_READ_32__(mem_0,reg0);
                reg8 = reg7;
                reg1 = (bit_band(reg8,1));
                
                reg7 = ((reg1 == 0) and 1114112 or 43);
                reg6 = (bit_tobit(reg1 + reg5)); goto block_2_fin;
            ::if_4_fin::
            reg9 = __MEMORY_READ_32__(mem_0,reg0);
            reg8 = reg9;
            reg7 = 45;
            reg6 = (bit_tobit(reg5 + 1))
            -- BLOCK RET (block):
        ::block_2_fin::
        reg9 = reg6;
        
            if (((bit_band(reg8,4)) == 0) and 1 or 0)==0 then goto if_35_fin end 
                reg2 = 0;
                goto block_30_fin;
            ::if_35_fin::
            
                if ((reg3 == 0) and 1 or 0)==0 then goto if_43_fin end 
                    goto block_40_fin;
                ::if_43_fin::
                reg6 = (bit_band(reg3,3));
                
                    if ((__UNSIGNED__((bit_tobit(reg3 + -1))) < __UNSIGNED__(3)) and 1 or 0)==0 then goto if_56_fin end 
                        reg1 = reg2;
                        goto block_50_fin;
                    ::if_56_fin::
                    reg10 = (bit_tobit(0 - (bit_band(reg3,-4))));
                    reg1 = reg2;
                    -- FORCE INIT VAR | i32
                    reg11 = 0;
                    
                    while true do ::loop_69_start::
                        reg12 = __MEMORY_READ_8__(mem_0,reg1);
                        reg13 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 1)));
                        reg14 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 2)));
                        reg15 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 3)));
                        reg16 = bit_tobit((bit_tobit((bit_tobit((bit_tobit(reg11 + (((bit_band(reg12,192)) ~= 128) and 1 or 0))) + (((bit_band(reg13,192)) ~= 128) and 1 or 0))) + (((bit_band(reg14,192)) ~= 128) and 1 or 0))) + (((bit_band(reg15,192)) ~= 128) and 1 or 0));
                        reg11 = reg16;
                        reg12 = bit_tobit(reg1 + 4);
                        reg1 = reg12;
                        reg12 = bit_tobit(reg10 + 4);
                        reg10 = reg12;
                        if reg10~=0 then goto loop_69_start; end;
                        break
                    end
                    
                ::block_50_fin::
                if ((reg6 == 0) and 1 or 0)~=0 then goto block_40_fin; end;
                
                while true do ::loop_120_start::
                    reg12 = __MEMORY_READ_8__(mem_0,reg1);
                    reg13 = bit_tobit(reg11 + (((bit_band(reg12,192)) ~= 128) and 1 or 0));
                    reg11 = reg13;
                    reg12 = bit_tobit(reg1 + 1);
                    reg1 = reg12;
                    reg12 = bit_tobit(reg6 + -1);
                    reg6 = reg12;
                    if reg6~=0 then goto loop_120_start; end;
                    break
                end
                
            ::block_40_fin::
            reg12 = bit_tobit(reg9 + reg11);
            reg9 = reg12;
        ::block_30_fin::
        reg1 = 1;
        
            
                reg12 = __MEMORY_READ_32__(mem_0,reg0+8);
                if ((reg12 ~= 1) and 1 or 0)==0 then goto if_154_fin end 
                    reg12 = __FUNCS__.func_108(reg0,reg7,reg2,reg3);
                    if reg12~=0 then goto block_149_fin; end;
                    goto block_148_fin;
                ::if_154_fin::
                
                    
                        
                            
                                reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                                reg6 = reg12;
                                if ((__UNSIGNED__(reg6) > __UNSIGNED__(reg9)) and 1 or 0)==0 then goto if_174_fin end 
                                    if (bit_band(reg8,8))~=0 then goto block_163_fin; end;
                                    reg1 = 0;
                                    reg12 = bit_tobit(reg6 - reg9);
                                    reg6 = reg12;
                                    reg9 = reg6;
                                    reg12 = __MEMORY_READ_8__(mem_0,reg0+32);
                                    reg11 = reg12;
                                    
                                    
                                    if (bit_tobit((bit_band(((((reg11 == 3) and 1 or 0) == 0) and reg11 or 1),3)) - 1)) == 0 then goto block_166_fin;
                                    elseif (bit_tobit((bit_band(((((reg11 == 3) and 1 or 0) == 0) and reg11 or 1),3)) - 1)) == 1 then goto block_165_fin;
                                    else goto block_164_fin;
                                    end
                                ::if_174_fin::
                                reg12 = __FUNCS__.func_108(reg0,reg7,reg2,reg3);
                                if reg12~=0 then goto block_149_fin; end;
                                goto block_148_fin;
                            ::block_166_fin::
                            reg9 = 0;
                            reg1 = reg6;
                            goto block_164_fin;
                        ::block_165_fin::
                        reg1 = (bit_rshift(reg6,1));
                        reg9 = (bit_rshift((bit_tobit(reg6 + 1)),1));
                    ::block_164_fin::
                    reg12 = bit_tobit(reg1 + 1);
                    reg1 = reg12;
                    reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg11 = reg12;
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+4);
                    reg6 = reg12;
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg8 = reg12;
                    
                        
                        while true do ::loop_241_start::
                            reg12 = bit_tobit(reg1 + -1);
                            reg1 = reg12;
                            if ((reg1 == 0) and 1 or 0)~=0 then goto block_240_fin; end;
                            reg12 = __MEMORY_READ_32__(mem_0,reg11+16);
                            reg12 = __TABLE_FUNCS_0__[reg12+1](reg8,reg6);
                            if ((reg12 == 0) and 1 or 0)~=0 then goto loop_241_start; end;
                            break
                        end
                        
                        do return 1 end
                    ::block_240_fin::
                    reg1 = 1;
                    if ((reg6 == 1114112) and 1 or 0)~=0 then goto block_149_fin; end;
                    reg12 = __FUNCS__.func_108(reg0,reg7,reg2,reg3);
                    if reg12~=0 then goto block_149_fin; end;
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg13 = __MEMORY_READ_32__(mem_0,reg0+28);
                    reg14 = __MEMORY_READ_32__(mem_0,reg13+12);
                    reg13 = __TABLE_FUNCS_0__[reg14+1](reg12,reg4,reg5);
                    if reg13~=0 then goto block_149_fin; end;
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+28);
                    reg2 = reg12;
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg0 = reg12;
                    reg1 = 0;
                    
                        
                        while true do ::loop_289_start::
                            if ((reg1 == reg9) and 1 or 0)~=0 then reg12 = reg9; goto block_288_fin; end;
                            reg13 = bit_tobit(reg1 + 1);
                            reg1 = reg13;
                            reg13 = __MEMORY_READ_32__(mem_0,reg2+16);
                            reg13 = __TABLE_FUNCS_0__[reg13+1](reg0,reg6);
                            if ((reg13 == 0) and 1 or 0)~=0 then goto loop_289_start; end;
                            break
                        end
                        
                        reg12 = (bit_tobit(reg1 + -1))
                        -- BLOCK RET (block):
                    ::block_288_fin::
                    reg1 = ((__UNSIGNED__(reg12) < __UNSIGNED__(reg9)) and 1 or 0);
                    goto block_149_fin;
                ::block_163_fin::
                reg12 = __MEMORY_READ_32__(mem_0,reg0+4);
                reg11 = reg12;
                __MEMORY_WRITE_32__(mem_0,reg0+4,48);
                reg12 = __MEMORY_READ_8__(mem_0,reg0+32);
                reg8 = reg12;
                __MEMORY_WRITE_8__(mem_0,reg0+32,1);
                reg12 = __FUNCS__.func_108(reg0,reg7,reg2,reg3);
                if reg12~=0 then goto block_149_fin; end;
                reg1 = 0;
                reg2 = (bit_tobit(reg6 - reg9));
                reg3 = reg2;
                
                    
                        
                            reg7 = __MEMORY_READ_8__(mem_0,reg0+32);
                            reg9 = reg7;
                            
                            
                            if (bit_tobit((bit_band(((((reg9 == 3) and 1 or 0) == 0) and reg9 or 1),3)) - 1)) == 0 then goto block_344_fin;
                            elseif (bit_tobit((bit_band(((((reg9 == 3) and 1 or 0) == 0) and reg9 or 1),3)) - 1)) == 1 then goto block_343_fin;
                            else goto block_342_fin;
                            end
                        ::block_344_fin::
                        reg3 = 0;
                        reg1 = reg2;
                        goto block_342_fin;
                    ::block_343_fin::
                    reg1 = (bit_rshift(reg2,1));
                    reg3 = (bit_rshift((bit_tobit(reg2 + 1)),1));
                ::block_342_fin::
                reg7 = bit_tobit(reg1 + 1);
                reg1 = reg7;
                reg7 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                reg9 = reg7;
                reg7 = __MEMORY_READ_32__(mem_0,reg0+4);
                reg2 = reg7;
                reg7 = __MEMORY_READ_32__(mem_0,reg0+24);
                reg6 = reg7;
                
                    
                    while true do ::loop_392_start::
                        reg7 = bit_tobit(reg1 + -1);
                        reg1 = reg7;
                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_391_fin; end;
                        reg7 = __MEMORY_READ_32__(mem_0,reg9+16);
                        reg7 = __TABLE_FUNCS_0__[reg7+1](reg6,reg2);
                        if ((reg7 == 0) and 1 or 0)~=0 then goto loop_392_start; end;
                        break
                    end
                    
                    do return 1 end
                ::block_391_fin::
                reg1 = 1;
                if ((reg2 == 1114112) and 1 or 0)~=0 then goto block_149_fin; end;
                reg7 = __MEMORY_READ_32__(mem_0,reg0+24);
                reg12 = __MEMORY_READ_32__(mem_0,reg0+28);
                reg13 = __MEMORY_READ_32__(mem_0,reg12+12);
                reg12 = __TABLE_FUNCS_0__[reg13+1](reg7,reg4,reg5);
                if reg12~=0 then goto block_149_fin; end;
                reg7 = __MEMORY_READ_32__(mem_0,reg0+28);
                reg1 = reg7;
                reg7 = __MEMORY_READ_32__(mem_0,reg0+24);
                reg4 = reg7;
                reg6 = 0;
                
                    
                    while true do ::loop_434_start::
                        if ((reg3 == reg6) and 1 or 0)~=0 then goto block_433_fin; end;
                        reg7 = bit_tobit(reg6 + 1);
                        reg6 = reg7;
                        reg7 = __MEMORY_READ_32__(mem_0,reg1+16);
                        reg7 = __TABLE_FUNCS_0__[reg7+1](reg4,reg2);
                        if ((reg7 == 0) and 1 or 0)~=0 then goto loop_434_start; end;
                        break
                    end
                    
                    reg1 = 1;
                    if ((__UNSIGNED__((bit_tobit(reg6 + -1))) < __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_149_fin; end;
                ::block_433_fin::
                __MEMORY_WRITE_8__(mem_0,reg0+32,reg8);
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg11);
                do return 0 end
            ::block_149_fin::
            do return reg1 end
        ::block_148_fin::
        reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg0 = __MEMORY_READ_32__(mem_0,reg3+12);
        reg0 = __TABLE_FUNCS_0__[reg0+1](reg1,reg4,reg5);
        do return reg0; end;
    end
    function __FUNCS__.func_14(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12;
        reg4 = __GLOBALS__[0];
        reg5 = (bit_tobit(reg4 - 1136));
        __GLOBALS__[0] = reg5;
        
            reg6 = (FloatToUInt32(reg1));
            if (((bit_band(reg6,2147483647)) == 0) and 1 or 0)~=0 then reg4 = 4; goto block_8_fin; end;
            reg1 = (bit_band(reg6,8388607));
            reg7 = (bit_band((bit_rshift(reg6,23)),255));
            
            reg8 = ((reg7 == 0) and (bit_band((bit_lshift(reg6,1)),16777214)) or (bit_bor(reg1,8388608)));
            reg9 = (__LONG_INT__(reg8,0));
            reg10 = ((reg9):_and(__LONG_INT__(1,0)));
            
                reg11 = (bit_band(reg6,2139095040));
                if reg11==0 then goto if_47_fin end 
                    if ((reg11 ~= 2139095040) and 1 or 0)~=0 then goto block_42_fin; end;
                    
                    reg4 = ((reg1 == 0) and 3 or 2); goto block_8_fin;
                ::if_47_fin::
                reg11 = bit_tobit(reg7 + -150);
                reg7 = reg11;
                reg11 = __LONG_INT__(1,0);
                reg4 = (bit_bxor(((reg10)[1]),1)); goto block_8_fin;
            ::block_42_fin::
            reg12 = (reg8 == 8388608) and 1 or 0;
            reg8 = reg12;
            
            reg12 = (reg8 == 0) and ((reg9):_shl(__LONG_INT__(1,0))) or __LONG_INT__(33554432,0);
            reg9 = reg12;
            
            reg11 = ((reg8 == 0) and __LONG_INT__(1,0) or __LONG_INT__(2,0));
            
            reg12 = bit_tobit(((reg8 == 0) and -151 or -152) + reg7);
            reg7 = reg12;
            reg4 = (bit_bxor(((reg10)[1]),1))
            -- BLOCK RET (block):
        ::block_8_fin::
        reg1 = reg4;
        __MEMORY_WRITE_16__(mem_0,reg5+1128,reg7);
        (reg11):store(mem_0,reg5+1120);
        (__LONG_INT__(1,0)):store(mem_0,reg5+1112);
        (reg9):store(mem_0,reg5+1104);
        __MEMORY_WRITE_8__(mem_0,reg5+1130,reg1);
        
            if ((reg1 == 2) and 1 or 0)==0 then goto if_117_fin end 
                reg2 = 1054920;
                reg4 = 0; goto block_113_fin;
            ::if_117_fin::
            reg8 = bit_band((bit_rshift(reg6,24)),128);
            reg6 = reg8;
            if ((reg2 == 0) and 1 or 0)==0 then goto if_131_fin end 
                
                reg2 = ((reg6 == 0) and 1054920 or 1054915);
                reg4 = (bit_rshift(reg6,7)); goto block_113_fin;
            ::if_131_fin::
            
            reg2 = ((reg6 == 0) and 1054916 or 1054915);
            reg4 = 1
            -- BLOCK RET (block):
        ::block_113_fin::
        reg6 = reg4;
        
            
                
                    
                        
                            
                                
                                    reg4 = bit_tobit(reg1 + -2);
                                    reg1 = reg4;
                                    
                                    
                                    if (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg1,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg1),255)) - 1)) == 0 then goto block_155_fin;
                                    elseif (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg1,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg1),255)) - 1)) == 1 then goto block_153_fin;
                                    elseif (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg1,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg1),255)) - 1)) == 2 then goto block_154_fin;
                                    else goto block_156_fin;
                                    end
                                ::block_156_fin::
                                __MEMORY_WRITE_32__(mem_0,reg5+1048,3);
                                __MEMORY_WRITE_32__(mem_0,reg5+1044,1054924);
                                __MEMORY_WRITE_16__(mem_0,reg5+1040,2);
                                __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                                __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                                __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
                                reg1 = 1;
                                goto block_150_fin;
                            ::block_155_fin::
                            __MEMORY_WRITE_32__(mem_0,reg5+1048,3);
                            __MEMORY_WRITE_32__(mem_0,reg5+1044,1054921);
                            __MEMORY_WRITE_16__(mem_0,reg5+1040,2);
                            __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                            __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                            __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
                            reg1 = 1;
                            goto block_150_fin;
                        ::block_154_fin::
                        reg1 = (bit_arshift((bit_lshift(reg7,16)),16));
                        
                        reg4 = __IMUL__(((((reg1 < 0) and 1 or 0) == 0) and 5 or -12),reg1);
                        reg1 = reg4;
                        if ((__UNSIGNED__(reg1) > __UNSIGNED__(16063)) and 1 or 0)~=0 then goto block_152_fin; end;
                        reg7 = (bit_tobit((bit_rshift(reg1,4)) + 21));
                        
                        reg1 = ((((__UNSIGNED__(reg3) < __UNSIGNED__(32768)) and 1 or 0) == 0) and -32768 or (bit_tobit(0 - reg3)));
                        __FUNCS__.func_11((bit_tobit(reg5 + 1040)),(bit_tobit(reg5 + 1104)),(bit_tobit(reg5 + 16)),reg7,reg1);
                        reg4 = bit_arshift((bit_lshift(reg1,16)),16);
                        reg1 = reg4;
                        
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+1040);
                            if ((reg4 == 0) and 1 or 0)==0 then goto if_274_fin end 
                                __FUNCS__.func_1((bit_tobit(reg5 + 1088)),(bit_tobit(reg5 + 1104)),(bit_tobit(reg5 + 16)),reg7,reg1);
                                goto block_270_fin;
                            ::if_274_fin::
                            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + 1048)));
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 1096)),reg4);
                            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5+1040);
                            (reg4):store(mem_0,reg5+1088);
                        ::block_270_fin::
                        reg4 = __MEMORY_READ_16__(mem_0,reg5+1096);reg4=bit_arshift(bit_lshift(reg4,16),16);
                        reg7 = reg4;
                        if ((reg7 > reg1) and 1 or 0)==0 then goto if_307_fin end 
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+1088);
                            reg8 = __MEMORY_READ_32__(mem_0,reg5+1092);
                            __FUNCS__.func_42((bit_tobit(reg5 + 8)),reg4,reg8,reg7,reg3,(bit_tobit(reg5 + 1040)));
                            __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                            __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+8);
                            __MEMORY_WRITE_32__(mem_0,reg5+1096,reg4);
                            reg4 = __MEMORY_READ_32__(mem_0,reg5+12);
                            reg1 = reg4;
                            goto block_150_fin;
                        ::if_307_fin::
                        reg1 = 2;
                        __MEMORY_WRITE_16__(mem_0,reg5+1040,2);
                        if ((reg3 == 0) and 1 or 0)==0 then goto if_343_fin end 
                            reg1 = 1;
                            __MEMORY_WRITE_32__(mem_0,reg5+1048,1);
                            __MEMORY_WRITE_32__(mem_0,reg5+1044,1054920);
                            __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                            __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                            __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
                            goto block_150_fin;
                        ::if_343_fin::
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 1056)),reg3);
                        __MEMORY_WRITE_16__(mem_0,reg5+1052,0);
                        __MEMORY_WRITE_32__(mem_0,reg5+1048,2);
                        __MEMORY_WRITE_32__(mem_0,reg5+1044,1054912);
                        __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                        __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                        __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
                        goto block_150_fin;
                    ::block_153_fin::
                    reg1 = 2;
                    __MEMORY_WRITE_16__(mem_0,reg5+1040,2);
                    if ((reg3 == 0) and 1 or 0)~=0 then goto block_151_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 1056)),reg3);
                    __MEMORY_WRITE_16__(mem_0,reg5+1052,0);
                    __MEMORY_WRITE_32__(mem_0,reg5+1048,2);
                    __MEMORY_WRITE_32__(mem_0,reg5+1044,1054912);
                    __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
                    __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
                    __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
                    goto block_150_fin;
                ::block_152_fin::
                __FUNCS__.func_110(1054927,37,1054964);
                error('unreachable');
            ::block_151_fin::
            reg1 = 1;
            __MEMORY_WRITE_32__(mem_0,reg5+1048,1);
            __MEMORY_WRITE_32__(mem_0,reg5+1044,1054920);
            __MEMORY_WRITE_32__(mem_0,reg5+1092,reg6);
            __MEMORY_WRITE_32__(mem_0,reg5+1088,reg2);
            __MEMORY_WRITE_32__(mem_0,reg5+1096,(bit_tobit(reg5 + 1040)));
        ::block_150_fin::
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + 1100)),reg1);
        reg1 = __FUNCS__.func_28(reg0,(bit_tobit(reg5 + 1088)));
        __GLOBALS__[0] = (bit_tobit(reg5 + 1136));
        do return reg1; end;
    end
    function __FUNCS__.func_15(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11;
        
            
                
                    
                        
                            
                                reg2 = (bit_band(reg1,7));
                                if reg2==0 then goto if_13_fin end 
                                    
                                        
                                            reg3 = __MEMORY_READ_32__(mem_0,reg0);
                                            reg4 = reg3;
                                            if ((__UNSIGNED__(reg4) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_21_fin end 
                                                if ((reg4 == 0) and 1 or 0)==0 then goto if_24_fin end 
                                                    reg4 = 0;
                                                    goto block_14_fin;
                                                ::if_24_fin::
                                                reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift(reg2,2)) + 1051988)));reg3=__LONG_INT__(reg3,0);
                                                reg5 = reg3;
                                                reg3 = (bit_tobit(reg0 + 4));
                                                reg2 = (bit_tobit((bit_lshift(reg4,2)) + -4));
                                                reg6 = (bit_tobit((bit_rshift(reg2,2)) + 1));
                                                reg7 = (bit_band(reg6,3));
                                                if ((__UNSIGNED__(reg2) < __UNSIGNED__(12)) and 1 or 0)~=0 then goto block_15_fin; end;
                                                reg2 = (bit_tobit(0 - (bit_band(reg6,2147483644))));
                                                -- FORCE INIT VAR | i64
                                                reg8 = __LONG_INT__(0,0);
                                                
                                                while true do ::loop_64_start::
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg3);reg9=__LONG_INT__(reg9,0);
                                                    reg10 = (reg9 * reg5) + reg8;
                                                    reg8 = reg10;
                                                    (reg8):store32(mem_0,reg3);
                                                    reg6 = (bit_tobit(reg3 + 4));
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg6);reg9=__LONG_INT__(reg9,0);
                                                    reg10 = (reg9 * reg5) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                                    reg8 = reg10;
                                                    (reg8):store32(mem_0,reg6);
                                                    reg6 = (bit_tobit(reg3 + 8));
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg6);reg9=__LONG_INT__(reg9,0);
                                                    reg10 = (reg9 * reg5) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                                    reg8 = reg10;
                                                    (reg8):store32(mem_0,reg6);
                                                    reg6 = (bit_tobit(reg3 + 12));
                                                    reg9 = __MEMORY_READ_32__(mem_0,reg6);reg9=__LONG_INT__(reg9,0);
                                                    reg10 = (reg9 * reg5) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                                    reg8 = reg10;
                                                    (reg8):store32(mem_0,reg6);
                                                    reg9 = (reg8):_shr_u(__LONG_INT__(32,0));
                                                    reg8 = reg9;
                                                    reg9 = bit_tobit(reg3 + 16);
                                                    reg3 = reg9;
                                                    reg9 = bit_tobit(reg2 + 4);
                                                    reg2 = reg9;
                                                    if reg2~=0 then goto loop_64_start; end;
                                                    break
                                                end
                                                
                                                goto block_15_fin;
                                            ::if_21_fin::
                                            __FUNCS__.func_84(reg4,40,1058148);
                                            error('unreachable');
                                        ::block_15_fin::
                                        if reg7==0 then goto if_139_fin end 
                                            reg2 = (bit_tobit(0 - reg7));
                                            
                                            while true do ::loop_144_start::
                                                reg9 = __MEMORY_READ_32__(mem_0,reg3);reg9=__LONG_INT__(reg9,0);
                                                reg10 = (reg9 * reg5) + reg8;
                                                reg8 = reg10;
                                                (reg8):store32(mem_0,reg3);
                                                reg9 = bit_tobit(reg3 + 4);
                                                reg3 = reg9;
                                                reg9 = (reg8):_shr_u(__LONG_INT__(32,0));
                                                reg8 = reg9;
                                                reg7 = (bit_tobit(reg2 + 1));
                                                reg9 = (__UNSIGNED__(reg7) >= __UNSIGNED__(reg2)) and 1 or 0;
                                                reg2 = reg7;
                                                if reg9~=0 then goto loop_144_start; end;
                                                break
                                            end
                                            
                                        ::if_139_fin::
                                        reg2 = ((reg8)[1]);
                                        if ((reg2 == 0) and 1 or 0)~=0 then goto block_14_fin; end;
                                        if ((__UNSIGNED__(reg4) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_8_fin; end;
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg0 + (bit_lshift(reg4,2)))) + 4)),reg2);
                                        reg9 = bit_tobit(reg4 + 1);
                                        reg4 = reg9;
                                    ::block_14_fin::
                                    __MEMORY_WRITE_32__(mem_0,reg0,reg4);
                                ::if_13_fin::
                                if (((bit_band(reg1,8)) == 0) and 1 or 0)~=0 then goto block_4_fin; end;
                                reg9 = __MEMORY_READ_32__(mem_0,reg0);
                                reg4 = reg9;
                                if ((__UNSIGNED__(reg4) >= __UNSIGNED__(41)) and 1 or 0)~=0 then goto block_7_fin; end;
                                if ((reg4 == 0) and 1 or 0)==0 then goto if_213_fin end 
                                    reg4 = 0;
                                    goto block_5_fin;
                                ::if_213_fin::
                                reg3 = (bit_tobit(reg0 + 4));
                                reg6 = (bit_lshift(reg4,2));
                                reg2 = (bit_tobit(reg6 + -4));
                                reg9 = (bit_tobit((bit_rshift(reg2,2)) + 1));
                                reg7 = (bit_band(reg9,3));
                                if ((__UNSIGNED__(reg2) < __UNSIGNED__(12)) and 1 or 0)==0 then goto if_240_fin end 
                                    reg8 = __LONG_INT__(0,0);
                                    goto block_6_fin;
                                ::if_240_fin::
                                reg2 = (bit_tobit(0 - (bit_band(reg9,2147483644))));
                                reg8 = __LONG_INT__(0,0);
                                
                                while true do ::loop_253_start::
                                    reg10 = __MEMORY_READ_32__(mem_0,reg3);reg10=__LONG_INT__(reg10,0);
                                    reg11 = (reg10 * __LONG_INT__(100000000,0)) + reg8;
                                    reg8 = reg11;
                                    (reg8):store32(mem_0,reg3);
                                    reg9 = (bit_tobit(reg3 + 4));
                                    reg10 = __MEMORY_READ_32__(mem_0,reg9);reg10=__LONG_INT__(reg10,0);
                                    reg11 = (reg10 * __LONG_INT__(100000000,0)) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                    reg8 = reg11;
                                    (reg8):store32(mem_0,reg9);
                                    reg9 = (bit_tobit(reg3 + 8));
                                    reg10 = __MEMORY_READ_32__(mem_0,reg9);reg10=__LONG_INT__(reg10,0);
                                    reg11 = (reg10 * __LONG_INT__(100000000,0)) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                    reg8 = reg11;
                                    (reg8):store32(mem_0,reg9);
                                    reg9 = (bit_tobit(reg3 + 12));
                                    reg10 = __MEMORY_READ_32__(mem_0,reg9);reg10=__LONG_INT__(reg10,0);
                                    reg11 = (reg10 * __LONG_INT__(100000000,0)) + ((reg8):_shr_u(__LONG_INT__(32,0)));
                                    reg8 = reg11;
                                    (reg8):store32(mem_0,reg9);
                                    reg9 = (reg8):_shr_u(__LONG_INT__(32,0));
                                    reg8 = reg9;
                                    reg9 = bit_tobit(reg3 + 16);
                                    reg3 = reg9;
                                    reg9 = bit_tobit(reg2 + 4);
                                    reg2 = reg9;
                                    if reg2~=0 then goto loop_253_start; end;
                                    break
                                end
                                
                                goto block_6_fin;
                            ::block_8_fin::
                            __FUNCS__.func_82(reg4,40,1058148);
                            error('unreachable');
                        ::block_7_fin::
                        __FUNCS__.func_84(reg4,40,1058148);
                        error('unreachable');
                    ::block_6_fin::
                    if reg7==0 then goto if_334_fin end 
                        reg2 = (bit_tobit(0 - reg7));
                        
                        while true do ::loop_339_start::
                            reg9 = __MEMORY_READ_32__(mem_0,reg3);reg9=__LONG_INT__(reg9,0);
                            reg10 = (reg9 * __LONG_INT__(100000000,0)) + reg8;
                            reg8 = reg10;
                            (reg8):store32(mem_0,reg3);
                            reg9 = bit_tobit(reg3 + 4);
                            reg3 = reg9;
                            reg9 = (reg8):_shr_u(__LONG_INT__(32,0));
                            reg8 = reg9;
                            reg7 = (bit_tobit(reg2 + 1));
                            reg9 = (__UNSIGNED__(reg7) >= __UNSIGNED__(reg2)) and 1 or 0;
                            reg2 = reg7;
                            if reg9~=0 then goto loop_339_start; end;
                            break
                        end
                        
                    ::if_334_fin::
                    reg2 = ((reg8)[1]);
                    if ((reg2 == 0) and 1 or 0)~=0 then goto block_5_fin; end;
                    if ((__UNSIGNED__(reg4) > __UNSIGNED__(39)) and 1 or 0)~=0 then goto block_3_fin; end;
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit((bit_tobit(reg0 + reg6)) + 4)),reg2);
                    reg2 = bit_tobit(reg4 + 1);
                    reg4 = reg2;
                ::block_5_fin::
                __MEMORY_WRITE_32__(mem_0,reg0,reg4);
            ::block_4_fin::
            if (bit_band(reg1,16))==0 then goto if_396_fin end 
                __FUNCS__.func_16(reg0,1052068,2);
            ::if_396_fin::
            if (bit_band(reg1,32))==0 then goto if_405_fin end 
                __FUNCS__.func_16(reg0,1052076,4);
            ::if_405_fin::
            if (bit_band(reg1,64))==0 then goto if_414_fin end 
                __FUNCS__.func_16(reg0,1052092,7);
            ::if_414_fin::
            if (bit_band(reg1,128))==0 then goto if_423_fin end 
                __FUNCS__.func_16(reg0,1052120,14);
            ::if_423_fin::
            if (bit_band(reg1,256))==0 then goto if_432_fin end 
                __FUNCS__.func_16(reg0,1052176,27);
            ::if_432_fin::
            do return  end
        ::block_3_fin::
        __FUNCS__.func_82(reg4,40,1058148);
        error('unreachable');
    end
    function __FUNCS__.func_16(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17,reg18,reg19,reg20,reg21,reg22;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 160));
        __GLOBALS__[0] = reg4;
        reg3 = __FUNCS__.func_65(reg4,0,160);
        reg5 = reg3;
        
            
                reg3 = __MEMORY_READ_32__(mem_0,reg0);
                reg6 = reg3;
                if ((__UNSIGNED__(reg6) >= __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_20_fin end 
                    if ((__UNSIGNED__(reg6) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_24_fin end 
                        reg3 = (bit_tobit(reg1 + (bit_lshift(reg2,2))));
                        if ((reg6 == 0) and 1 or 0)~=0 then goto block_14_fin; end;
                        reg7 = (bit_tobit(reg6 + 1));
                        reg8 = (bit_tobit(reg0 + 4));
                        reg9 = (bit_lshift(reg6,2));
                        -- FORCE INIT VAR | i32
                        reg10 = 0;
                        -- FORCE INIT VAR | i32
                        reg10 = 0;
                        -- FORCE INIT VAR | i32
                        reg10 = 0;
                        -- FORCE INIT VAR | i32
                        reg11 = 0;
                        -- FORCE INIT VAR | i32
                        reg11 = 0;
                        
                        while true do ::loop_46_start::
                            reg12 = (bit_tobit(reg10 + 1));
                            reg2 = (bit_tobit(reg5 + (bit_lshift(reg10,2))));
                            
                            while true do ::loop_57_start::
                                reg13 = reg10;
                                reg14 = reg12;
                                reg4 = reg2;
                                if ((reg1 == reg3) and 1 or 0)~=0 then goto block_13_fin; end;
                                reg2 = (bit_tobit(reg4 + 4));
                                reg12 = (bit_tobit(reg14 + 1));
                                reg10 = (bit_tobit(reg13 + 1));
                                reg15 = __MEMORY_READ_32__(mem_0,reg1);
                                reg16 = reg15;
                                reg15 = (bit_tobit(reg1 + 4));
                                reg1 = reg15;
                                if ((reg16 == 0) and 1 or 0)~=0 then goto loop_57_start; end;
                                break
                            end
                            
                            
                            reg17 = ((((__UNSIGNED__(reg13) > __UNSIGNED__(40)) and 1 or 0) == 0) and 40 or reg13);
                            reg18 = (__LONG_INT__(reg16,0));
                            reg19 = __LONG_INT__(0,0);
                            reg2 = reg9;
                            reg1 = reg13;
                            reg12 = reg8;
                            
                                
                                    
                                        
                                        while true do ::loop_113_start::
                                            if ((reg1 == reg17) and 1 or 0)~=0 then goto block_112_fin; end;
                                            reg20 = __MEMORY_READ_32__(mem_0,reg4);reg20=__LONG_INT__(reg20,0);
                                            reg21 = __MEMORY_READ_32__(mem_0,reg12);reg21=__LONG_INT__(reg21,0);
                                            reg22 = (reg19 + reg20) + (reg21 * reg18);
                                            reg19 = reg22;
                                            (reg19):store32(mem_0,reg4);
                                            reg20 = (reg19):_shr_u(__LONG_INT__(32,0));
                                            reg19 = reg20;
                                            reg20 = bit_tobit(reg4 + 4);
                                            reg4 = reg20;
                                            reg20 = bit_tobit(reg14 + 1);
                                            reg14 = reg20;
                                            reg20 = bit_tobit(reg1 + 1);
                                            reg1 = reg20;
                                            reg20 = bit_tobit(reg12 + 4);
                                            reg12 = reg20;
                                            reg20 = bit_tobit(reg2 + -4);
                                            reg2 = reg20;
                                            if reg2~=0 then goto loop_113_start; end;
                                            break
                                        end
                                        
                                        reg4 = reg6;
                                        reg1 = ((reg19)[1]);
                                        if reg1~=0 then goto block_111_fin; end;
                                        goto block_110_fin;
                                    ::block_112_fin::
                                    __FUNCS__.func_82((bit_tobit(reg14 + -1)),40,1058148);
                                    error('unreachable');
                                ::block_111_fin::
                                reg2 = (bit_tobit(reg6 + reg13));
                                if ((__UNSIGNED__(reg2) <= __UNSIGNED__(39)) and 1 or 0)==0 then goto if_178_fin end 
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + (bit_lshift(reg2,2)))),reg1);
                                    reg4 = reg7;
                                    goto block_110_fin;
                                ::if_178_fin::
                                __FUNCS__.func_82(reg2,40,1058148);
                                error('unreachable');
                            ::block_110_fin::
                            reg1 = (bit_tobit(reg4 + reg13));
                            
                            reg20 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg1)) and 1 or 0) == 0) and reg11 or reg1;
                            reg11 = reg20;
                            reg1 = reg15;
                            goto loop_46_start;
                            break
                        end
                        
                        error('unreachable');
                    ::if_24_fin::
                    __FUNCS__.func_84(reg6,40,1058148);
                    error('unreachable');
                ::if_20_fin::
                if ((__UNSIGNED__(reg6) < __UNSIGNED__(41)) and 1 or 0)==0 then goto if_221_fin end 
                    reg14 = (bit_tobit(reg0 + 4));
                    reg16 = (bit_tobit(reg14 + (bit_lshift(reg6,2))));
                    reg7 = (bit_lshift(reg2,2));
                    reg8 = (bit_tobit(reg2 + 1));
                    
                    while true do ::loop_239_start::
                        reg10 = (bit_tobit(reg17 + 1));
                        reg13 = (bit_tobit(reg5 + (bit_lshift(reg17,2))));
                        
                        while true do ::loop_250_start::
                            reg15 = reg17;
                            reg12 = reg10;
                            reg4 = reg13;
                            if ((reg14 == reg16) and 1 or 0)~=0 then goto block_13_fin; end;
                            reg13 = (bit_tobit(reg4 + 4));
                            reg10 = (bit_tobit(reg12 + 1));
                            reg17 = (bit_tobit(reg15 + 1));
                            reg20 = __MEMORY_READ_32__(mem_0,reg14);
                            reg3 = reg20;
                            reg9 = (bit_tobit(reg14 + 4));
                            reg14 = reg9;
                            if ((reg3 == 0) and 1 or 0)~=0 then goto loop_250_start; end;
                            break
                        end
                        
                        
                        reg6 = ((((__UNSIGNED__(reg15) > __UNSIGNED__(40)) and 1 or 0) == 0) and 40 or reg15);
                        reg18 = (__LONG_INT__(reg3,0));
                        reg19 = __LONG_INT__(0,0);
                        reg13 = reg7;
                        reg14 = reg15;
                        reg10 = reg1;
                        
                            
                                
                                while true do ::loop_305_start::
                                    if ((reg14 == reg6) and 1 or 0)~=0 then goto block_304_fin; end;
                                    reg20 = __MEMORY_READ_32__(mem_0,reg4);reg20=__LONG_INT__(reg20,0);
                                    reg21 = __MEMORY_READ_32__(mem_0,reg10);reg21=__LONG_INT__(reg21,0);
                                    reg22 = (reg19 + reg20) + (reg21 * reg18);
                                    reg19 = reg22;
                                    (reg19):store32(mem_0,reg4);
                                    reg20 = (reg19):_shr_u(__LONG_INT__(32,0));
                                    reg19 = reg20;
                                    reg20 = bit_tobit(reg4 + 4);
                                    reg4 = reg20;
                                    reg20 = bit_tobit(reg12 + 1);
                                    reg12 = reg20;
                                    reg20 = bit_tobit(reg14 + 1);
                                    reg14 = reg20;
                                    reg20 = bit_tobit(reg10 + 4);
                                    reg10 = reg20;
                                    reg20 = bit_tobit(reg13 + -4);
                                    reg13 = reg20;
                                    if reg13~=0 then goto loop_305_start; end;
                                    break
                                end
                                
                                reg4 = reg2;
                                reg14 = ((reg19)[1]);
                                if ((reg14 == 0) and 1 or 0)~=0 then goto block_303_fin; end;
                                reg4 = (bit_tobit(reg2 + reg15));
                                if ((__UNSIGNED__(reg4) <= __UNSIGNED__(39)) and 1 or 0)==0 then goto if_361_fin end 
                                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg5 + (bit_lshift(reg4,2)))),reg14);
                                    reg4 = reg8;
                                    goto block_303_fin;
                                ::if_361_fin::
                                __FUNCS__.func_82(reg4,40,1058148);
                                error('unreachable');
                            ::block_304_fin::
                            __FUNCS__.func_82((bit_tobit(reg12 + -1)),40,1058148);
                            error('unreachable');
                        ::block_303_fin::
                        reg20 = bit_tobit(reg4 + reg15);
                        reg4 = reg20;
                        
                        reg20 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg4)) and 1 or 0) == 0) and reg11 or reg4;
                        reg11 = reg20;
                        reg14 = reg9;
                        goto loop_239_start;
                        break
                    end
                    
                    error('unreachable');
                ::if_221_fin::
                __FUNCS__.func_84(reg6,40,1058148);
                error('unreachable');
            ::block_14_fin::
            reg4 = 0;
            
            while true do ::loop_411_start::
                if ((reg1 == reg3) and 1 or 0)~=0 then goto block_13_fin; end;
                reg6 = bit_tobit(reg4 + 1);
                reg4 = reg6;
                reg6 = __MEMORY_READ_32__(mem_0,reg1);
                reg2 = (bit_tobit(reg1 + 4));
                reg1 = reg2;
                if ((reg6 == 0) and 1 or 0)~=0 then goto loop_411_start; end;
                reg1 = (bit_tobit(reg4 + -1));
                
                reg6 = (((__UNSIGNED__(reg11) < __UNSIGNED__(reg1)) and 1 or 0) == 0) and reg11 or reg1;
                reg11 = reg6;
                reg1 = reg2;
                goto loop_411_start;
                break
            end
            
            error('unreachable');
        ::block_13_fin::
        reg2 = __FUNCS__.func_64((bit_tobit(reg0 + 4)),reg5,160);
        __MEMORY_WRITE_32__(mem_0,reg0,reg11);
        __GLOBALS__[0] = (bit_tobit(reg5 + 160));
    end
    function __FUNCS__.func_17(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15,reg16,reg17;
        reg4 = __GLOBALS__[0];
        reg5 = (bit_tobit(reg4 + -64));
        __GLOBALS__[0] = reg5;
        reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg1 + 8)));
        reg6 = reg4;
        reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg1);
        reg7 = reg4;
        reg4 = (bit_tobit(reg5 + 56));
        (__LONG_INT__(0,0)):store(mem_0,reg4);
        reg8 = (bit_tobit(reg5 + 40));
        (((reg6):_xor(__LONG_INT__(2037671283,1952801890)))):store(mem_0,reg8);
        reg9 = (bit_tobit(reg5 + 32));
        (((reg6):_xor(__LONG_INT__(1852075885,1685025377)))):store(mem_0,reg9);
        reg10 = (bit_tobit(reg5 + 24));
        (((reg7):_xor(__LONG_INT__(1852142177,1819895653)))):store(mem_0,reg10);
        (__LONG_INT__(0,0)):store(mem_0,reg5+48);
        (((reg7):_xor(__LONG_INT__(1886610805,1936682341)))):store(mem_0,reg5+16);
        (reg6):store(mem_0,reg5+8);
        (reg7):store(mem_0,reg5);
        __FUNCS__.func_24(reg2,reg5);
        
            
                
                    reg12 = __LONG_INT__(0,0); reg12:load(mem_0,reg5+48);
                    reg13 = __MEMORY_READ_32__(mem_0,reg4);reg13=__LONG_INT__(reg13,0);
                    reg6 = ((reg12):_or(((reg13):_shl(__LONG_INT__(56,0)))));
                    reg12 = __LONG_INT__(0,0); reg12:load(mem_0,reg8);
                    reg7 = ((reg6):_xor(reg12));
                    reg12 = __LONG_INT__(0,0); reg12:load(mem_0,reg10);
                    reg13 = reg7 + reg12;
                    reg12 = (reg7):_rotl(__LONG_INT__(16,0));
                    reg7 = reg13;
                    reg13 = ((reg12):_xor(reg7));
                    reg12 = __LONG_INT__(0,0); reg12:load(mem_0,reg9);
                    reg14 = reg12;
                    reg12 = __LONG_INT__(0,0); reg12:load(mem_0,reg5+16);
                    reg15 = (reg14 + reg12);
                    reg12 = (reg13 + ((reg15):_rotl(__LONG_INT__(32,0))));
                    reg16 = (reg12):_xor(reg6);
                    reg6 = ((((reg14):_rotl(__LONG_INT__(13,0)))):_xor(reg15));
                    reg17 = reg7 + reg6;
                    reg7 = reg17;
                    reg17 = (reg7):_xor(((reg6):_rotl(__LONG_INT__(17,0))));
                    reg6 = reg17;
                    reg14 = (reg16 + reg6);
                    reg16 = (reg14):_xor(((reg6):_rotl(__LONG_INT__(13,0))));
                    reg6 = reg16;
                    reg16 = (((reg13):_rotl(__LONG_INT__(21,0)))):_xor(reg12);
                    reg13 = reg16;
                    reg12 = reg13 + ((((reg7):_rotl(__LONG_INT__(32,0)))):_xor(__LONG_INT__(255,0)));
                    reg7 = reg12;
                    reg15 = (reg6 + reg7);
                    reg12 = (reg15):_xor(((reg6):_rotl(__LONG_INT__(17,0))));
                    reg6 = reg12;
                    reg12 = (((reg13):_rotl(__LONG_INT__(16,0)))):_xor(reg7);
                    reg7 = reg12;
                    reg13 = (reg7 + ((reg14):_rotl(__LONG_INT__(32,0))));
                    reg12 = reg6 + reg13;
                    reg16 = (reg6):_rotl(__LONG_INT__(13,0));
                    reg6 = reg12;
                    reg14 = ((reg16):_xor(reg6));
                    reg12 = (((reg7):_rotl(__LONG_INT__(21,0)))):_xor(reg13);
                    reg7 = reg12;
                    reg13 = (reg7 + ((reg15):_rotl(__LONG_INT__(32,0))));
                    reg12 = reg14 + reg13;
                    reg16 = (reg14):_rotl(__LONG_INT__(17,0));
                    reg14 = reg12;
                    reg15 = ((reg16):_xor(reg14));
                    reg12 = (((reg7):_rotl(__LONG_INT__(16,0)))):_xor(reg13);
                    reg7 = reg12;
                    reg12 = reg7 + ((reg6):_rotl(__LONG_INT__(32,0)));
                    reg6 = reg12;
                    reg13 = ((((reg15):_rotl(__LONG_INT__(13,0)))):_xor((reg15 + reg6)));
                    reg12 = (((reg7):_rotl(__LONG_INT__(21,0)))):_xor(reg6);
                    reg6 = reg12;
                    reg7 = (reg6 + ((reg14):_rotl(__LONG_INT__(32,0))));
                    reg14 = (reg13 + reg7);
                    reg12 = (((((reg14):_xor(((((((reg6):_rotl(__LONG_INT__(16,0)))):_xor(reg7))):_rotl(__LONG_INT__(21,0)))))):_xor(((reg13):_rotl(__LONG_INT__(17,0)))))):_xor(((reg14):_rotl(__LONG_INT__(32,0))));
                    reg6 = reg12;
                    reg4 = ((reg6)[1]);
                    reg7 = (__IMUL__((bit_rshift(reg4,25)),16843009));
                    reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 20)));
                    reg13 = reg12;
                    reg12 = (bit_tobit(reg1 + 16));
                    reg14 = __MEMORY_READ_32__(mem_0,reg12);
                    reg15 = reg14;
                    reg14 = (bit_band(reg15,reg4));
                    reg16 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg13 + reg14)));
                    reg9 = reg16;
                    reg4 = (bit_bxor(reg7,reg9));
                    reg16 = bit_band((bit_band((bit_bxor(reg4,-1)),(bit_tobit(reg4 + -16843009)))),-2139062144);
                    reg4 = reg16;
                    if reg4==0 then goto if_259_fin end 
                        reg10 = 0;
                        goto block_65_fin;
                    ::if_259_fin::
                    reg10 = 0;
                    
                    while true do ::loop_266_start::
                        if (bit_band((bit_band(reg9,(bit_lshift(reg9,1)))),-2139062144))~=0 then goto block_64_fin; end;
                        reg4 = (bit_tobit(reg10 + reg14));
                        reg16 = bit_tobit(reg10 + 4);
                        reg10 = reg16;
                        reg14 = (bit_band(reg15,(bit_tobit(reg4 + 4))));
                        reg16 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg13 + reg14)));
                        reg9 = reg16;
                        reg4 = (bit_bxor(reg9,reg7));
                        reg16 = bit_band((bit_band((bit_bxor(reg4,-1)),(bit_tobit(reg4 + -16843009)))),-2139062144);
                        reg4 = reg16;
                        if ((reg4 == 0) and 1 or 0)~=0 then goto loop_266_start; end;
                        break
                    end
                    
                ::block_65_fin::
                
                    reg8 = (bit_band((bit_tobit((bit_rshift((__CTZ__(reg4)),3)) + reg14)),reg15));
                    reg17 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg13 - (bit_lshift(reg8,3)))) + -8)));
                    if ((reg2 == reg17) and 1 or 0)==0 then goto if_329_fin end 
                        reg16 = (bit_tobit(0 - reg8)); goto block_310_fin;
                    ::if_329_fin::
                    reg8 = (bit_band((bit_tobit(reg4 + -1)),reg4));
                    
                    while true do ::loop_341_start::
                        
                            if reg8==0 then goto if_344_fin end 
                                reg4 = reg8;
                                goto block_342_fin;
                            ::if_344_fin::
                            
                            while true do ::loop_349_start::
                                if (bit_band((bit_band(reg9,(bit_lshift(reg9,1)))),-2139062144))~=0 then goto block_64_fin; end;
                                reg4 = (bit_tobit(reg10 + reg14));
                                reg17 = bit_tobit(reg10 + 4);
                                reg10 = reg17;
                                reg14 = (bit_band(reg15,(bit_tobit(reg4 + 4))));
                                reg17 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg13 + reg14)));
                                reg9 = reg17;
                                reg4 = (bit_bxor(reg9,reg7));
                                reg17 = bit_band((bit_band((bit_bxor(reg4,-1)),(bit_tobit(reg4 + -16843009)))),-2139062144);
                                reg4 = reg17;
                                if ((reg4 == 0) and 1 or 0)~=0 then goto loop_349_start; end;
                                break
                            end
                            
                        ::block_342_fin::
                        reg8 = (bit_band((bit_tobit(reg4 + -1)),reg4));
                        reg17 = bit_band((bit_tobit((bit_rshift((__CTZ__(reg4)),3)) + reg14)),reg15);
                        reg4 = reg17;
                        reg17 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg13 - (bit_lshift(reg4,3)))) + -8)));
                        if ((reg17 ~= reg2) and 1 or 0)~=0 then goto loop_341_start; end;
                        break
                    end
                    
                    reg16 = (bit_tobit(0 - reg4))
                    -- BLOCK RET (block):
                ::block_310_fin::
                reg1 = (bit_tobit((bit_tobit(reg13 + (bit_lshift(reg16,3)))) + -4));
                reg4 = __MEMORY_READ_32__(mem_0,reg1);
                reg9 = reg4;
                __MEMORY_WRITE_32__(mem_0,reg1,reg3);
                reg11 = 1; goto block_63_fin;
            ::block_64_fin::
            __FUNCS__.func_37(reg12,reg6,reg2,reg3,reg1);
            reg11 = 0
            -- BLOCK RET (block):
        ::block_63_fin::
        reg10 = reg11;
        __MEMORY_WRITE_32__(mem_0,reg0+4,reg9);
        __MEMORY_WRITE_32__(mem_0,reg0,reg10);
        __GLOBALS__[0] = (bit_tobit(reg5 - -64));
    end
    function __FUNCS__.func_18(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9;
        
            
                reg2 = __FUNCS__.func_174(0);
                reg3 = reg2;
                reg2 = __FUNCS__.func_143(reg3,8);
                reg4 = __FUNCS__.func_143(20,8);
                reg5 = __FUNCS__.func_143(16,8);
                reg6 = bit_tobit((bit_band((bit_tobit((bit_tobit(reg3 - (bit_tobit((bit_tobit(reg2 + reg4)) + reg5)))) + -65544)),-9)) + -3);
                reg3 = reg6;
                reg2 = __FUNCS__.func_143(16,8);
                reg4 = (bit_tobit(0 - (bit_lshift(reg2,2))));
                
                if ((__UNSIGNED__(((((__UNSIGNED__(reg4) > __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg4 or reg3)) <= __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_3_fin; end;
                reg2 = __FUNCS__.func_143(16,8);
                
                reg5 = __FUNCS__.func_143(((((__UNSIGNED__((bit_tobit(reg2 + -5))) > __UNSIGNED__(reg1)) and 1 or 0) == 0) and (bit_tobit(reg1 + 4)) or 16),8);
                reg4 = reg5;
                reg2 = __FUNCS__.func_175(reg0);
                reg3 = reg2;
                reg2 = __FUNCS__.func_166(reg3);
                reg5 = reg2;
                reg2 = __FUNCS__.func_172(reg3,reg5);
                reg6 = reg2;
                
                    
                        
                            
                                
                                    
                                        
                                            reg2 = __FUNCS__.func_156(reg3);
                                            if ((reg2 == 0) and 1 or 0)==0 then goto if_74_fin end 
                                                if ((__UNSIGNED__(reg5) >= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_70_fin; end;
                                                reg2 = __MEMORY_READ_32__(mem_0,1059608);
                                                if ((reg6 == reg2) and 1 or 0)~=0 then goto block_69_fin; end;
                                                reg2 = __MEMORY_READ_32__(mem_0,1059604);
                                                if ((reg6 == reg2) and 1 or 0)~=0 then goto block_68_fin; end;
                                                reg2 = __FUNCS__.func_151(reg6);
                                                if reg2~=0 then goto block_64_fin; end;
                                                reg2 = __FUNCS__.func_166(reg6);
                                                reg7 = reg2;
                                                reg2 = (bit_tobit(reg7 + reg5));
                                                if ((__UNSIGNED__(reg2) < __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_64_fin; end;
                                                reg5 = (bit_tobit(reg2 - reg4));
                                                if ((__UNSIGNED__(reg7) < __UNSIGNED__(256)) and 1 or 0)~=0 then goto block_67_fin; end;
                                                __FUNCS__.func_54(reg6);
                                                goto block_66_fin;
                                            ::if_74_fin::
                                            reg8 = __FUNCS__.func_166(reg3);
                                            reg6 = reg8;
                                            if ((__UNSIGNED__(reg4) < __UNSIGNED__(256)) and 1 or 0)~=0 then goto block_64_fin; end;
                                            
                                            if ((((__UNSIGNED__((bit_tobit(reg6 - reg4))) < __UNSIGNED__(131073)) and 1 or 0) == 0) and 0 or ((__UNSIGNED__(reg6) >= __UNSIGNED__((bit_tobit(reg4 + 4)))) and 1 or 0))~=0 then goto block_65_fin; end;
                                            reg8 = __MEMORY_READ_32__(mem_0,reg3);
                                            reg5 = reg8;
                                            reg7 = (bit_tobit((bit_tobit(reg5 + reg6)) + 16));
                                            reg8 = __FUNCS__.func_143((bit_tobit(reg4 + 31)),65536);
                                            reg6 = reg8;
                                            reg4 = 0;
                                            if ((reg4 == 0) and 1 or 0)~=0 then goto block_64_fin; end;
                                            reg3 = (bit_tobit(reg4 + reg5));
                                            reg0 = (bit_tobit(reg6 - reg5));
                                            reg1 = (bit_tobit(reg0 + -16));
                                            __MEMORY_WRITE_32__(mem_0,reg3+4,reg1);
                                            reg8 = __FUNCS__.func_172(reg3,reg1);
                                            __MEMORY_WRITE_32__(mem_0,reg8+4,7);
                                            reg8 = __FUNCS__.func_172(reg3,(bit_tobit(reg0 + -12)));
                                            __MEMORY_WRITE_32__(mem_0,reg8+4,0);
                                            reg8 = __MEMORY_READ_32__(mem_0,1059612);
                                            reg0 = (bit_tobit(reg8 + (bit_tobit(reg6 - reg7))));
                                            __MEMORY_WRITE_32__(mem_0,1059612,reg0);
                                            reg8 = __MEMORY_READ_32__(mem_0,1059640);
                                            reg1 = reg8;
                                            
                                            __MEMORY_WRITE_32__(mem_0,1059640,((((__UNSIGNED__(reg4) > __UNSIGNED__(reg1)) and 1 or 0) == 0) and reg4 or reg1));
                                            reg8 = __MEMORY_READ_32__(mem_0,1059616);
                                            reg1 = reg8;
                                            
                                            __MEMORY_WRITE_32__(mem_0,1059616,((((__UNSIGNED__(reg1) > __UNSIGNED__(reg0)) and 1 or 0) == 0) and reg0 or reg1));
                                            goto block_2_fin;
                                        ::block_70_fin::
                                        reg6 = (bit_tobit(reg5 - reg4));
                                        reg8 = __FUNCS__.func_143(16,8);
                                        if ((__UNSIGNED__(reg6) < __UNSIGNED__(reg8)) and 1 or 0)~=0 then goto block_65_fin; end;
                                        reg8 = __FUNCS__.func_172(reg3,reg4);
                                        reg5 = reg8;
                                        __FUNCS__.func_121(reg3,reg4);
                                        __FUNCS__.func_121(reg5,reg6);
                                        __FUNCS__.func_31(reg5,reg6);
                                        goto block_65_fin;
                                    ::block_69_fin::
                                    reg8 = __MEMORY_READ_32__(mem_0,1059600);
                                    reg9 = bit_tobit(reg8 + reg5);
                                    reg5 = reg9;
                                    if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_64_fin; end;
                                    reg8 = __FUNCS__.func_172(reg3,reg4);
                                    reg6 = reg8;
                                    __FUNCS__.func_121(reg3,reg4);
                                    reg8 = bit_tobit(reg5 - reg4);
                                    reg4 = reg8;
                                    __MEMORY_WRITE_32__(mem_0,reg6+4,(bit_bor(reg4,1)));
                                    __MEMORY_WRITE_32__(mem_0,1059600,reg4);
                                    __MEMORY_WRITE_32__(mem_0,1059608,reg6);
                                    goto block_65_fin;
                                ::block_68_fin::
                                reg8 = __MEMORY_READ_32__(mem_0,1059596);
                                reg9 = bit_tobit(reg8 + reg5);
                                reg5 = reg9;
                                if ((__UNSIGNED__(reg5) < __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_64_fin; end;
                                
                                    reg6 = (bit_tobit(reg5 - reg4));
                                    reg8 = __FUNCS__.func_143(16,8);
                                    if ((__UNSIGNED__(reg6) < __UNSIGNED__(reg8)) and 1 or 0)==0 then goto if_278_fin end 
                                        __FUNCS__.func_121(reg3,reg5);
                                        reg6 = 0;
                                        reg5 = 0;
                                        goto block_269_fin;
                                    ::if_278_fin::
                                    reg8 = __FUNCS__.func_172(reg3,reg4);
                                    reg5 = reg8;
                                    reg8 = __FUNCS__.func_172(reg5,reg6);
                                    reg7 = reg8;
                                    __FUNCS__.func_121(reg3,reg4);
                                    __FUNCS__.func_140(reg5,reg6);
                                    reg8 = __MEMORY_READ_32__(mem_0,reg7+4);
                                    __MEMORY_WRITE_32__(mem_0,reg7+4,(bit_band(reg8,-2)));
                                ::block_269_fin::
                                __MEMORY_WRITE_32__(mem_0,1059604,reg5);
                                __MEMORY_WRITE_32__(mem_0,1059596,reg6);
                                goto block_65_fin;
                            ::block_67_fin::
                            reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg6 + 12)));
                            reg9 = reg8;
                            reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg6 + 8)));
                            reg6 = reg8;
                            if ((reg9 ~= reg6) and 1 or 0)==0 then goto if_327_fin end 
                                __MEMORY_WRITE_32__(mem_0,reg6+12,reg9);
                                __MEMORY_WRITE_32__(mem_0,reg9+8,reg6);
                                goto block_66_fin;
                            ::if_327_fin::
                            reg8 = __MEMORY_READ_32__(mem_0,1059196);
                            __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg8,(bit_rol(-2,(bit_rshift(reg7,3)))))));
                        ::block_66_fin::
                        reg7 = __FUNCS__.func_143(16,8);
                        if ((__UNSIGNED__(reg5) >= __UNSIGNED__(reg7)) and 1 or 0)==0 then goto if_352_fin end 
                            reg7 = __FUNCS__.func_172(reg3,reg4);
                            reg6 = reg7;
                            __FUNCS__.func_121(reg3,reg4);
                            __FUNCS__.func_121(reg6,reg5);
                            __FUNCS__.func_31(reg6,reg5);
                            goto block_65_fin;
                        ::if_352_fin::
                        __FUNCS__.func_121(reg3,reg2);
                    ::block_65_fin::
                    if reg3~=0 then goto block_2_fin; end;
                ::block_64_fin::
                reg2 = __FUNCS__.func_2(reg1);
                reg4 = reg2;
                if ((reg4 == 0) and 1 or 0)~=0 then goto block_3_fin; end;
                reg2 = __FUNCS__.func_166(reg3);
                reg5 = __FUNCS__.func_156(reg3);
                
                reg3 = (bit_tobit(reg2 + ((reg5 == 0) and -4 or -8)));
                
                reg2 = __FUNCS__.func_64(reg4,reg0,((((__UNSIGNED__(reg3) > __UNSIGNED__(reg1)) and 1 or 0) == 0) and reg3 or reg1));
                __FUNCS__.func_10(reg0);
                do return reg2 end
            ::block_3_fin::
            do return 0 end
        ::block_2_fin::
        reg0 = __FUNCS__.func_156(reg3);
        reg0 = __FUNCS__.func_174(reg3);
        do return reg0; end;
    end
    function __FUNCS__.func_19(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14,reg15;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 + -64));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        reg4 = reg2;
        reg2 = (bit_tobit(reg3 + 56));
        (__LONG_INT__(0,0)):store(mem_0,reg2);
        reg5 = (bit_tobit(reg3 + 40));
        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,(bit_tobit(reg0 + 8)));
        reg7 = reg6;
        (((reg7):_xor(__LONG_INT__(2037671283,1952801890)))):store(mem_0,reg5);
        reg6 = (bit_tobit(reg3 + 32));
        (((reg7):_xor(__LONG_INT__(1852075885,1685025377)))):store(mem_0,reg6);
        reg8 = (bit_tobit(reg3 + 24));
        reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg0);
        reg10 = reg9;
        (((reg10):_xor(__LONG_INT__(1852142177,1819895653)))):store(mem_0,reg8);
        (__LONG_INT__(0,0)):store(mem_0,reg3+48);
        (reg7):store(mem_0,reg3+8);
        (reg10):store(mem_0,reg3);
        (((reg10):_xor(__LONG_INT__(1886610805,1936682341)))):store(mem_0,reg3+16);
        __FUNCS__.func_24(reg4,reg3);
        reg1 = 0;
        
            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg3+48);
            reg11 = __MEMORY_READ_32__(mem_0,reg2);reg11=__LONG_INT__(reg11,0);
            reg7 = ((reg9):_or(((reg11):_shl(__LONG_INT__(56,0)))));
            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg5);
            reg10 = ((reg7):_xor(reg9));
            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg8);
            reg11 = reg10 + reg9;
            reg9 = (reg10):_rotl(__LONG_INT__(16,0));
            reg10 = reg11;
            reg11 = ((reg9):_xor(reg10));
            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg6);
            reg12 = reg9;
            reg9 = __LONG_INT__(0,0); reg9:load(mem_0,reg3+16);
            reg13 = (reg12 + reg9);
            reg9 = (reg11 + ((reg13):_rotl(__LONG_INT__(32,0))));
            reg14 = (reg9):_xor(reg7);
            reg7 = ((((reg12):_rotl(__LONG_INT__(13,0)))):_xor(reg13));
            reg15 = reg10 + reg7;
            reg10 = reg15;
            reg15 = (reg10):_xor(((reg7):_rotl(__LONG_INT__(17,0))));
            reg7 = reg15;
            reg12 = (reg14 + reg7);
            reg14 = (reg12):_xor(((reg7):_rotl(__LONG_INT__(13,0))));
            reg7 = reg14;
            reg14 = (((reg11):_rotl(__LONG_INT__(21,0)))):_xor(reg9);
            reg11 = reg14;
            reg9 = reg11 + ((((reg10):_rotl(__LONG_INT__(32,0)))):_xor(__LONG_INT__(255,0)));
            reg10 = reg9;
            reg13 = (reg7 + reg10);
            reg9 = (reg13):_xor(((reg7):_rotl(__LONG_INT__(17,0))));
            reg7 = reg9;
            reg9 = (((reg11):_rotl(__LONG_INT__(16,0)))):_xor(reg10);
            reg10 = reg9;
            reg11 = (reg10 + ((reg12):_rotl(__LONG_INT__(32,0))));
            reg9 = reg7 + reg11;
            reg14 = (reg7):_rotl(__LONG_INT__(13,0));
            reg7 = reg9;
            reg12 = ((reg14):_xor(reg7));
            reg9 = (((reg10):_rotl(__LONG_INT__(21,0)))):_xor(reg11);
            reg10 = reg9;
            reg11 = (reg10 + ((reg13):_rotl(__LONG_INT__(32,0))));
            reg9 = reg12 + reg11;
            reg14 = (reg12):_rotl(__LONG_INT__(17,0));
            reg12 = reg9;
            reg13 = ((reg14):_xor(reg12));
            reg9 = (((reg10):_rotl(__LONG_INT__(16,0)))):_xor(reg11);
            reg10 = reg9;
            reg9 = reg10 + ((reg7):_rotl(__LONG_INT__(32,0)));
            reg7 = reg9;
            reg11 = ((((reg13):_rotl(__LONG_INT__(13,0)))):_xor((reg13 + reg7)));
            reg9 = (((reg10):_rotl(__LONG_INT__(21,0)))):_xor(reg7);
            reg7 = reg9;
            reg10 = (reg7 + ((reg12):_rotl(__LONG_INT__(32,0))));
            reg12 = (reg11 + reg10);
            reg2 = ((((((((reg12):_xor(((((((reg7):_rotl(__LONG_INT__(16,0)))):_xor(reg10))):_rotl(__LONG_INT__(21,0)))))):_xor(((reg11):_rotl(__LONG_INT__(17,0)))))):_xor(((reg12):_shr_u(__LONG_INT__(32,0))))))[1]);
            reg7 = (__IMUL__((bit_rshift(reg2,25)),16843009));
            reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
            reg8 = reg9;
            reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 16)));
            reg10 = reg9;
            reg6 = (bit_band(reg10,reg2));
            reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + reg6)));
            reg0 = reg9;
            reg2 = (bit_bxor(reg7,reg0));
            reg9 = bit_band((bit_band((bit_bxor(reg2,-1)),(bit_tobit(reg2 + -16843009)))),-2139062144);
            reg2 = reg9;
            if ((reg2 == 0) and 1 or 0)==0 then goto if_259_fin end 
                reg5 = 0;
                
                while true do ::loop_262_start::
                    if (bit_band((bit_band(reg0,(bit_lshift(reg0,1)))),-2139062144))~=0 then goto block_66_fin; end;
                    reg0 = (bit_tobit(reg1 + reg6));
                    reg9 = bit_tobit(reg1 + 4);
                    reg1 = reg9;
                    reg6 = (bit_band(reg10,(bit_tobit(reg0 + 4))));
                    reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + reg6)));
                    reg0 = reg9;
                    reg2 = (bit_bxor(reg0,reg7));
                    reg9 = bit_band((bit_band((bit_bxor(reg2,-1)),(bit_tobit(reg2 + -16843009)))),-2139062144);
                    reg2 = reg9;
                    if ((reg2 == 0) and 1 or 0)~=0 then goto loop_262_start; end;
                    break
                end
                
            ::if_259_fin::
            reg5 = 1;
            reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg8 - (bit_lshift((bit_band((bit_tobit((bit_rshift((__CTZ__(reg2)),3)) + reg6)),reg10)),3)))) + -8)));
            if ((reg9 == reg4) and 1 or 0)~=0 then goto block_66_fin; end;
            reg5 = (bit_band((bit_tobit(reg2 + -1)),reg2));
            
            while true do ::loop_331_start::
                
                    if reg5==0 then goto if_334_fin end 
                        reg2 = reg5;
                        goto block_332_fin;
                    ::if_334_fin::
                    
                    while true do ::loop_339_start::
                        if (bit_band((bit_band(reg0,(bit_lshift(reg0,1)))),-2139062144))==0 then goto if_347_fin end 
                            reg5 = 0;
                            goto block_66_fin;
                        ::if_347_fin::
                        reg0 = (bit_tobit(reg1 + reg6));
                        reg9 = bit_tobit(reg1 + 4);
                        reg1 = reg9;
                        reg6 = (bit_band(reg10,(bit_tobit(reg0 + 4))));
                        reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + reg6)));
                        reg0 = reg9;
                        reg2 = (bit_bxor(reg0,reg7));
                        reg9 = bit_band((bit_band((bit_bxor(reg2,-1)),(bit_tobit(reg2 + -16843009)))),-2139062144);
                        reg2 = reg9;
                        if ((reg2 == 0) and 1 or 0)~=0 then goto loop_339_start; end;
                        break
                    end
                    
                ::block_332_fin::
                reg5 = (bit_band((bit_tobit(reg2 + -1)),reg2));
                reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg8 - (bit_lshift((bit_band((bit_tobit((bit_rshift((__CTZ__(reg2)),3)) + reg6)),reg10)),3)))) + -8)));
                if ((reg9 ~= reg4) and 1 or 0)~=0 then goto loop_331_start; end;
                break
            end
            
            reg5 = 1;
        ::block_66_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 - -64));
        do return reg5; end;
    end
    function __FUNCS__.func_20(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 + -64));
        __GLOBALS__[0] = reg3;
        
            
                
                    
                        
                            
                                reg2 = __MEMORY_READ_8__(mem_0,reg0);
                                
                                if (bit_tobit(reg2 - 1)) == 0 then goto block_11_fin;
                                elseif (bit_tobit(reg2 - 1)) == 1 then goto block_10_fin;
                                elseif (bit_tobit(reg2 - 1)) == 2 then goto block_9_fin;
                                else goto block_12_fin;
                                end
                            ::block_12_fin::
                            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                            __MEMORY_WRITE_32__(mem_0,reg3+4,reg2);
                            reg2 = __FUNCS__.func_148(20,1);
                            reg0 = reg2;
                            if ((reg0 == 0) and 1 or 0)~=0 then goto block_7_fin; end;
                            reg2 = __MEMORY_READ_32__(mem_0,1051400);
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 16)),reg2);
                            reg2 = __LONG_INT__(0,0); reg2:load(mem_0,1051392);
                            (reg2):store(mem_0,(bit_tobit(reg0 + 8)));
                            reg2 = __LONG_INT__(0,0); reg2:load(mem_0,1051384);
                            (reg2):store(mem_0,reg0);
                            (__LONG_INT__(20,20)):store(mem_0,reg3+12);
                            __MEMORY_WRITE_32__(mem_0,reg3+8,reg0);
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 60)),2);
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 36)),3);
                            (__LONG_INT__(3,0)):store(mem_0,reg3+44);
                            __MEMORY_WRITE_32__(mem_0,reg3+40,1050364);
                            __MEMORY_WRITE_32__(mem_0,reg3+28,6);
                            __MEMORY_WRITE_32__(mem_0,reg3+56,(bit_tobit(reg3 + 24)));
                            __MEMORY_WRITE_32__(mem_0,reg3+32,(bit_tobit(reg3 + 4)));
                            __MEMORY_WRITE_32__(mem_0,reg3+24,(bit_tobit(reg3 + 8)));
                            reg2 = __FUNCS__.func_87(reg1,(bit_tobit(reg3 + 40)));
                            reg0 = reg2;
                            reg2 = __MEMORY_READ_32__(mem_0,reg3+12);
                            if ((reg2 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                            reg2 = __MEMORY_READ_32__(mem_0,reg3+8);
                            reg1 = reg2;
                            if ((reg1 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                            __FUNCS__.func_10(reg1);
                            goto block_8_fin;
                        ::block_11_fin::
                        reg2 = 1050334;
                        reg4 = 16;
                        
                            
                                
                                    
                                        
                                            
                                                
                                                    
                                                        
                                                            
                                                                
                                                                    
                                                                        
                                                                            
                                                                                
                                                                                    
                                                                                        
                                                                                            
                                                                                                
                                                                                                    
                                                                                                        
                                                                                                            
                                                                                                                
                                                                                                                    
                                                                                                                        
                                                                                                                            
                                                                                                                                
                                                                                                                                    
                                                                                                                                        
                                                                                                                                            
                                                                                                                                                
                                                                                                                                                    
                                                                                                                                                        
                                                                                                                                                            
                                                                                                                                                                
                                                                                                                                                                    
                                                                                                                                                                        
                                                                                                                                                                            
                                                                                                                                                                                
                                                                                                                                                                                    
                                                                                                                                                                                        
                                                                                                                                                                                            
                                                                                                                                                                                                reg6 = __MEMORY_READ_8__(mem_0,reg0+1);
                                                                                                                                                                                                
                                                                                                                                                                                                if (bit_tobit(reg6 - 1)) == 0 then goto block_151_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 1 then goto block_150_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 2 then goto block_149_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 3 then goto block_148_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 4 then goto block_147_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 5 then goto block_146_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 6 then goto block_145_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 7 then goto block_144_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 8 then goto block_143_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 9 then goto block_142_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 10 then goto block_141_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 11 then goto block_140_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 12 then goto block_139_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 13 then goto block_138_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 14 then goto block_137_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 15 then goto block_136_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 16 then goto block_135_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 17 then goto block_134_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 18 then goto block_133_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 19 then goto block_132_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 20 then goto block_131_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 21 then goto block_130_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 22 then goto block_129_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 23 then goto block_128_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 24 then goto block_127_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 25 then goto block_126_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 26 then goto block_125_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 27 then goto block_124_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 28 then goto block_123_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 29 then goto block_122_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 30 then goto block_121_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 31 then goto block_120_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 32 then goto block_119_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 33 then goto block_118_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 34 then goto block_117_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 35 then goto block_116_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 36 then goto block_115_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 37 then goto block_114_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 38 then goto block_113_fin;
                                                                                                                                                                                                elseif (bit_tobit(reg6 - 1)) == 39 then goto block_112_fin;
                                                                                                                                                                                                else goto block_110_fin;
                                                                                                                                                                                                end
                                                                                                                                                                                            ::block_151_fin::
                                                                                                                                                                                            reg2 = 1050317;
                                                                                                                                                                                            reg4 = 17;
                                                                                                                                                                                            goto block_110_fin;
                                                                                                                                                                                        ::block_150_fin::
                                                                                                                                                                                        reg2 = 1050299;
                                                                                                                                                                                        reg4 = 18;
                                                                                                                                                                                        goto block_110_fin;
                                                                                                                                                                                    ::block_149_fin::
                                                                                                                                                                                    reg2 = 1050283;
                                                                                                                                                                                    goto block_110_fin;
                                                                                                                                                                                ::block_148_fin::
                                                                                                                                                                                reg2 = 1050267;
                                                                                                                                                                                goto block_110_fin;
                                                                                                                                                                            ::block_147_fin::
                                                                                                                                                                            reg5 = 1050248; goto block_111_fin;
                                                                                                                                                                        ::block_146_fin::
                                                                                                                                                                        reg2 = 1050230;
                                                                                                                                                                        reg4 = 18;
                                                                                                                                                                        goto block_110_fin;
                                                                                                                                                                    ::block_145_fin::
                                                                                                                                                                    reg2 = 1050217;
                                                                                                                                                                    reg4 = 13;
                                                                                                                                                                    goto block_110_fin;
                                                                                                                                                                ::block_144_fin::
                                                                                                                                                                reg2 = 1050203;
                                                                                                                                                                reg4 = 14;
                                                                                                                                                                goto block_110_fin;
                                                                                                                                                            ::block_143_fin::
                                                                                                                                                            reg2 = 1050182;
                                                                                                                                                            reg4 = 21;
                                                                                                                                                            goto block_110_fin;
                                                                                                                                                        ::block_142_fin::
                                                                                                                                                        reg2 = 1050170;
                                                                                                                                                        reg4 = 12;
                                                                                                                                                        goto block_110_fin;
                                                                                                                                                    ::block_141_fin::
                                                                                                                                                    reg2 = 1050159;
                                                                                                                                                    reg4 = 11;
                                                                                                                                                    goto block_110_fin;
                                                                                                                                                ::block_140_fin::
                                                                                                                                                reg2 = 1050138;
                                                                                                                                                reg4 = 21;
                                                                                                                                                goto block_110_fin;
                                                                                                                                            ::block_139_fin::
                                                                                                                                            reg2 = 1050117;
                                                                                                                                            reg4 = 21;
                                                                                                                                            goto block_110_fin;
                                                                                                                                        ::block_138_fin::
                                                                                                                                        reg2 = 1050102;
                                                                                                                                        reg4 = 15;
                                                                                                                                        goto block_110_fin;
                                                                                                                                    ::block_137_fin::
                                                                                                                                    reg2 = 1050088;
                                                                                                                                    reg4 = 14;
                                                                                                                                    goto block_110_fin;
                                                                                                                                ::block_136_fin::
                                                                                                                                reg5 = 1050069; goto block_111_fin;
                                                                                                                            ::block_135_fin::
                                                                                                                            reg2 = 1050031;
                                                                                                                            reg4 = 38;
                                                                                                                            goto block_110_fin;
                                                                                                                        ::block_134_fin::
                                                                                                                        reg2 = 1049975;
                                                                                                                        reg4 = 56;
                                                                                                                        goto block_110_fin;
                                                                                                                    ::block_133_fin::
                                                                                                                    reg2 = 1049950;
                                                                                                                    reg4 = 25;
                                                                                                                    goto block_110_fin;
                                                                                                                ::block_132_fin::
                                                                                                                reg2 = 1049927;
                                                                                                                reg4 = 23;
                                                                                                                goto block_110_fin;
                                                                                                            ::block_131_fin::
                                                                                                            reg2 = 1049915;
                                                                                                            reg4 = 12;
                                                                                                            goto block_110_fin;
                                                                                                        ::block_130_fin::
                                                                                                        reg2 = 1049906;
                                                                                                        reg4 = 9;
                                                                                                        goto block_110_fin;
                                                                                                    ::block_129_fin::
                                                                                                    reg2 = 1049896;
                                                                                                    reg4 = 10;
                                                                                                    goto block_110_fin;
                                                                                                ::block_128_fin::
                                                                                                reg2 = 1049880;
                                                                                                goto block_110_fin;
                                                                                            ::block_127_fin::
                                                                                            reg2 = 1049857;
                                                                                            reg4 = 23;
                                                                                            goto block_110_fin;
                                                                                        ::block_126_fin::
                                                                                        reg2 = 1049832;
                                                                                        reg4 = 25;
                                                                                        goto block_110_fin;
                                                                                    ::block_125_fin::
                                                                                    reg2 = 1049818;
                                                                                    reg4 = 14;
                                                                                    goto block_110_fin;
                                                                                ::block_124_fin::
                                                                                reg2 = 1049805;
                                                                                reg4 = 13;
                                                                                goto block_110_fin;
                                                                            ::block_123_fin::
                                                                            reg2 = 1049785;
                                                                            reg4 = 20;
                                                                            goto block_110_fin;
                                                                        ::block_122_fin::
                                                                        reg2 = 1049777;
                                                                        reg4 = 8;
                                                                        goto block_110_fin;
                                                                    ::block_121_fin::
                                                                    reg2 = 1049750;
                                                                    reg4 = 27;
                                                                    goto block_110_fin;
                                                                ::block_120_fin::
                                                                reg2 = 1049736;
                                                                reg4 = 14;
                                                                goto block_110_fin;
                                                            ::block_119_fin::
                                                            reg2 = 1049719;
                                                            reg4 = 17;
                                                            goto block_110_fin;
                                                        ::block_118_fin::
                                                        reg2 = 1049697;
                                                        reg4 = 22;
                                                        goto block_110_fin;
                                                    ::block_117_fin::
                                                    reg2 = 1049676;
                                                    reg4 = 21;
                                                    goto block_110_fin;
                                                ::block_116_fin::
                                                reg2 = 1049665;
                                                reg4 = 11;
                                                goto block_110_fin;
                                            ::block_115_fin::
                                            reg2 = 1049643;
                                            reg4 = 22;
                                            goto block_110_fin;
                                        ::block_114_fin::
                                        reg2 = 1049630;
                                        reg4 = 13;
                                        goto block_110_fin;
                                    ::block_113_fin::
                                    reg2 = 1049619;
                                    reg4 = 11;
                                    goto block_110_fin;
                                ::block_112_fin::
                                reg5 = 1049600
                                -- BLOCK RET (block):
                            ::block_111_fin::
                            reg2 = reg5;
                            reg4 = 19;
                        ::block_110_fin::
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 60)),1);
                        __MEMORY_WRITE_32__(mem_0,reg3+28,reg4);
                        __MEMORY_WRITE_32__(mem_0,reg3+24,reg2);
                        __MEMORY_WRITE_32__(mem_0,reg3+12,7);
                        (__LONG_INT__(1,0)):store(mem_0,reg3+44);
                        __MEMORY_WRITE_32__(mem_0,reg3+40,1049592);
                        __MEMORY_WRITE_32__(mem_0,reg3+8,(bit_tobit(reg3 + 24)));
                        __MEMORY_WRITE_32__(mem_0,reg3+56,(bit_tobit(reg3 + 8)));
                        reg2 = __FUNCS__.func_87(reg1,(bit_tobit(reg3 + 40)));
                        reg0 = reg2;
                        goto block_8_fin;
                    ::block_10_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                    reg0 = reg2;
                    reg2 = __MEMORY_READ_32__(mem_0,reg0);
                    reg4 = __MEMORY_READ_32__(mem_0,reg0+4);
                    reg5 = __FUNCS__.func_171(reg2,reg4,reg1);
                    reg0 = reg5;
                    goto block_8_fin;
                ::block_9_fin::
                reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                reg0 = reg2;
                reg2 = __MEMORY_READ_32__(mem_0,reg0);
                reg4 = __MEMORY_READ_32__(mem_0,reg0+4);
                reg5 = __MEMORY_READ_32__(mem_0,reg4+16);
                reg4 = __TABLE_FUNCS_0__[reg5+1](reg2,reg1);
                reg0 = reg4;
            ::block_8_fin::
            __GLOBALS__[0] = (bit_tobit(reg3 - -64));
            do return reg0 end
        ::block_7_fin::
        __FUNCS__.func_170(20,1);
        error('unreachable');
    end
    function __FUNCS__.func_21(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6,reg7;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 32));
        __GLOBALS__[0] = reg2;
        reg1 = (bit_bor((bit_tobit(reg2 + 8)),2));
        reg3 = __MEMORY_READ_32__(mem_0,1059104);
        reg4 = reg3;
        
            
                
                    
                        
                        while true do ::loop_20_start::
                            
                                
                                    reg3 = reg4;
                                    
                                    if reg3 == 0 then goto block_21_fin;
                                    elseif reg3 == 1 then goto block_21_fin;
                                    elseif reg3 == 2 then goto block_22_fin;
                                    elseif reg3 == 3 then goto block_19_fin;
                                    else goto block_22_fin;
                                    end
                                ::block_22_fin::
                                if (((bit_band(reg3,3)) ~= 2) and 1 or 0)~=0 then goto block_16_fin; end;
                                
                                    
                                    while true do ::loop_34_start::
                                        reg5 = __MEMORY_READ_32__(mem_0,1059184);
                                        if ((reg5 ~= 1) and 1 or 0)==0 then goto if_39_fin end 
                                            (__LONG_INT__(1,0)):store(mem_0,1059184);
                                            __MEMORY_WRITE_32__(mem_0,1059192,0);
                                        ::if_39_fin::
                                        reg4 = reg3;
                                        reg5 = __FUNCS__.func_60();
                                        reg6 = reg5;
                                        reg5 = __MEMORY_READ_32__(mem_0,1059104);
                                        reg3 = reg5;
                                        reg5 = ((reg4 == reg3) and 1 or 0);
                                        
                                        __MEMORY_WRITE_32__(mem_0,1059104,((reg5 == 0) and reg3 or reg1));
                                        __MEMORY_WRITE_8__(mem_0,reg2+16,0);
                                        __MEMORY_WRITE_32__(mem_0,reg2+8,reg6);
                                        __MEMORY_WRITE_32__(mem_0,reg2+12,(bit_band(reg4,-4)));
                                        if ((reg5 == 0) and 1 or 0)==0 then goto if_75_fin end 
                                            
                                                reg5 = __MEMORY_READ_32__(mem_0,reg2+8);
                                                reg4 = reg5;
                                                if ((reg4 == 0) and 1 or 0)~=0 then goto block_76_fin; end;
                                                reg5 = __MEMORY_READ_32__(mem_0,reg4);
                                                reg7 = reg4;
                                                reg4 = reg5;
                                                __MEMORY_WRITE_32__(mem_0,reg7,(bit_tobit(reg4 + -1)));
                                                if ((reg4 ~= 1) and 1 or 0)~=0 then goto block_76_fin; end;
                                                reg5 = __MEMORY_READ_32__(mem_0,reg2+8);
                                                __FUNCS__.func_100(reg5);
                                            ::block_76_fin::
                                            if (((bit_band(reg3,3)) == 2) and 1 or 0)~=0 then goto loop_34_start; end;
                                            goto block_33_fin;
                                        ::if_75_fin::
                                        break
                                    end
                                    
                                    reg5 = __MEMORY_READ_8__(mem_0,reg2+16);
                                    if ((reg5 == 0) and 1 or 0)==0 then goto if_109_fin end 
                                        
                                        while true do ::loop_110_start::
                                            __FUNCS__.func_36();
                                            reg5 = __MEMORY_READ_8__(mem_0,reg2+16);
                                            if ((reg5 == 0) and 1 or 0)~=0 then goto loop_110_start; end;
                                            break
                                        end
                                        
                                    ::if_109_fin::
                                    reg5 = __MEMORY_READ_32__(mem_0,reg2+8);
                                    reg3 = reg5;
                                    if ((reg3 == 0) and 1 or 0)~=0 then goto block_33_fin; end;
                                    reg5 = __MEMORY_READ_32__(mem_0,reg3);
                                    reg7 = reg3;
                                    reg3 = reg5;
                                    __MEMORY_WRITE_32__(mem_0,reg7,(bit_tobit(reg3 + -1)));
                                    if ((reg3 ~= 1) and 1 or 0)~=0 then goto block_33_fin; end;
                                    reg5 = __MEMORY_READ_32__(mem_0,reg2+8);
                                    __FUNCS__.func_100(reg5);
                                ::block_33_fin::
                                reg5 = __MEMORY_READ_32__(mem_0,1059104);
                                reg4 = reg5;
                                goto loop_20_start;
                            ::block_21_fin::
                            reg5 = __MEMORY_READ_32__(mem_0,1059104);
                            reg4 = reg5;
                            reg6 = ((reg4 == reg3) and 1 or 0);
                            
                            __MEMORY_WRITE_32__(mem_0,1059104,((reg6 == 0) and reg4 or 2));
                            if ((reg6 == 0) and 1 or 0)~=0 then goto loop_20_start; end;
                            break
                        end
                        
                        __MEMORY_WRITE_8__(mem_0,reg2+12,((reg3 == 1) and 1 or 0));
                        __MEMORY_WRITE_32__(mem_0,reg2+8,3);
                        reg5 = __MEMORY_READ_32__(mem_0,1050612);
                        __TABLE_FUNCS_0__[reg5+1](reg0,(bit_tobit(reg2 + 8)));
                        reg5 = __MEMORY_READ_32__(mem_0,1059104);
                        reg0 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,reg2+8);
                        __MEMORY_WRITE_32__(mem_0,1059104,reg5);
                        reg3 = (bit_band(reg0,3));
                        __MEMORY_WRITE_32__(mem_0,reg2+4,reg3);
                        if ((reg3 ~= 2) and 1 or 0)~=0 then goto block_18_fin; end;
                        reg3 = bit_band(reg0,-4);
                        reg0 = reg3;
                        if ((reg0 == 0) and 1 or 0)~=0 then goto block_19_fin; end;
                        
                        while true do ::loop_196_start::
                            reg3 = __MEMORY_READ_32__(mem_0,reg0);
                            reg4 = reg3;
                            __MEMORY_WRITE_32__(mem_0,reg0,0);
                            if ((reg4 == 0) and 1 or 0)~=0 then goto block_17_fin; end;
                            reg3 = __MEMORY_READ_32__(mem_0,reg0+4);
                            __MEMORY_WRITE_8__(mem_0,reg0+8,1);
                            __FUNCS__.func_58((bit_tobit(reg4 + 24)));
                            reg5 = __MEMORY_READ_32__(mem_0,reg4);
                            reg0 = reg5;
                            __MEMORY_WRITE_32__(mem_0,reg4,(bit_tobit(reg0 + -1)));
                            if ((reg0 == 1) and 1 or 0)==0 then goto if_225_fin end 
                                __FUNCS__.func_100(reg4);
                            ::if_225_fin::
                            reg0 = reg3;
                            if reg0~=0 then goto loop_196_start; end;
                            break
                        end
                        
                    ::block_19_fin::
                    __GLOBALS__[0] = (bit_tobit(reg2 + 32));
                    do return  end
                ::block_18_fin::
                __MEMORY_WRITE_32__(mem_0,reg2+8,0);
                __FUNCS__.func_89((bit_tobit(reg2 + 4)),(bit_tobit(reg2 + 8)),1050772);
                error('unreachable');
            ::block_17_fin::
            __FUNCS__.func_110(1049216,43,1050788);
            error('unreachable');
        ::block_16_fin::
        __FUNCS__.func_110(1050632,57,1050692);
        error('unreachable');
    end
    function __FUNCS__.func_22(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6,reg7,reg8;
        
            
                
                    
                        
                            
                                
                                    
                                        if ((__UNSIGNED__(reg0) >= __UNSIGNED__(65536)) and 1 or 0)==0 then goto if_13_fin end 
                                            if ((__UNSIGNED__(reg0) < __UNSIGNED__(131072)) and 1 or 0)~=0 then goto block_9_fin; end;
                                            reg1 = (bit_band((bit_band((bit_band((bit_band((bit_band((bit_band((bit_band(((__UNSIGNED__((bit_tobit(reg0 + -173790))) > __UNSIGNED__(33)) and 1 or 0),((__UNSIGNED__((bit_tobit(reg0 + -177973))) > __UNSIGNED__(10)) and 1 or 0))),(((bit_band(reg0,2097150)) ~= 178206) and 1 or 0))),((__UNSIGNED__((bit_tobit(reg0 + -183970))) > __UNSIGNED__(13)) and 1 or 0))),((__UNSIGNED__((bit_tobit(reg0 + -191457))) > __UNSIGNED__(3102)) and 1 or 0))),((__UNSIGNED__((bit_tobit(reg0 + -195102))) > __UNSIGNED__(1505)) and 1 or 0))),((__UNSIGNED__((bit_tobit(reg0 + -201547))) > __UNSIGNED__(716212)) and 1 or 0))),((__UNSIGNED__(reg0) < __UNSIGNED__(918000)) and 1 or 0)));
                                            goto block_8_fin;
                                        ::if_13_fin::
                                        reg2 = 1056676;
                                        reg3 = (bit_band((bit_rshift(reg0,8)),255));
                                        -- FORCE INIT VAR | i32
                                        reg4 = 0;
                                        
                                        while true do ::loop_74_start::
                                            
                                                reg5 = (bit_tobit(reg2 + 2));
                                                reg6 = __MEMORY_READ_8__(mem_0,reg2+1);
                                                reg1 = reg6;
                                                reg6 = (bit_tobit(reg4 + reg1));
                                                reg7 = __MEMORY_READ_8__(mem_0,reg2);
                                                reg2 = reg7;
                                                if ((reg3 ~= reg2) and 1 or 0)==0 then goto if_91_fin end 
                                                    if ((__UNSIGNED__(reg2) > __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_75_fin; end;
                                                    reg4 = reg6;
                                                    reg2 = reg5;
                                                    if ((reg2 ~= 1056758) and 1 or 0)~=0 then goto loop_74_start; end;
                                                    goto block_75_fin;
                                                ::if_91_fin::
                                                if ((__UNSIGNED__(reg6) < __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_7_fin; end;
                                                if ((__UNSIGNED__(reg6) > __UNSIGNED__(290)) and 1 or 0)~=0 then goto block_6_fin; end;
                                                reg2 = (bit_tobit(reg4 + 1056758));
                                                
                                                    
                                                    while true do ::loop_118_start::
                                                        if ((reg1 == 0) and 1 or 0)~=0 then goto block_117_fin; end;
                                                        reg7 = bit_tobit(reg1 + -1);
                                                        reg1 = reg7;
                                                        reg7 = __MEMORY_READ_8__(mem_0,reg2);
                                                        reg8 = bit_tobit(reg2 + 1);
                                                        reg2 = reg8;
                                                        if ((reg7 ~= (bit_band(reg0,255))) and 1 or 0)~=0 then goto loop_118_start; end;
                                                        break
                                                    end
                                                    
                                                    reg1 = 0;
                                                    goto block_8_fin;
                                                ::block_117_fin::
                                                reg4 = reg6;
                                                reg2 = reg5;
                                                if ((reg2 ~= 1056758) and 1 or 0)~=0 then goto loop_74_start; end;
                                            ::block_75_fin::
                                            break
                                        end
                                        
                                        reg7 = bit_band(reg0,65535);
                                        reg0 = reg7;
                                        reg2 = 1057048;
                                        reg1 = 1;
                                        
                                        while true do ::loop_159_start::
                                            reg6 = (bit_tobit(reg2 + 1));
                                            
                                                reg8 = __MEMORY_READ_8__(mem_0,reg2);
                                                reg4 = reg8;
                                                reg5 = (bit_arshift((bit_lshift(reg4,24)),24));
                                                if ((reg5 >= 0) and 1 or 0)~=0 then reg7 = reg6; goto block_164_fin; end;
                                                if ((reg6 == 1057357) and 1 or 0)~=0 then goto block_5_fin; end;
                                                reg8 = __MEMORY_READ_8__(mem_0,reg2+1);
                                                reg4 = (bit_bor(reg8,(bit_lshift((bit_band(reg5,127)),8))));
                                                reg7 = (bit_tobit(reg2 + 2))
                                                -- BLOCK RET (block):
                                            ::block_164_fin::
                                            reg2 = reg7;
                                            reg7 = bit_tobit(reg0 - reg4);
                                            reg0 = reg7;
                                            if ((reg0 < 0) and 1 or 0)~=0 then goto block_8_fin; end;
                                            reg7 = bit_bxor(reg1,1);
                                            reg1 = reg7;
                                            if ((reg2 ~= 1057357) and 1 or 0)~=0 then goto loop_159_start; end;
                                            break
                                        end
                                        
                                        goto block_8_fin;
                                    ::block_9_fin::
                                    reg2 = 1057357;
                                    reg3 = (bit_band((bit_rshift(reg0,8)),255));
                                    
                                    while true do ::loop_222_start::
                                        
                                            reg5 = (bit_tobit(reg2 + 2));
                                            reg7 = __MEMORY_READ_8__(mem_0,reg2+1);
                                            reg1 = reg7;
                                            reg6 = (bit_tobit(reg4 + reg1));
                                            reg7 = __MEMORY_READ_8__(mem_0,reg2);
                                            reg2 = reg7;
                                            if ((reg3 ~= reg2) and 1 or 0)==0 then goto if_239_fin end 
                                                if ((__UNSIGNED__(reg2) > __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_223_fin; end;
                                                reg4 = reg6;
                                                reg2 = reg5;
                                                if ((reg2 ~= 1057433) and 1 or 0)~=0 then goto loop_222_start; end;
                                                goto block_223_fin;
                                            ::if_239_fin::
                                            if ((__UNSIGNED__(reg6) < __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_4_fin; end;
                                            if ((__UNSIGNED__(reg6) > __UNSIGNED__(175)) and 1 or 0)~=0 then goto block_3_fin; end;
                                            reg2 = (bit_tobit(reg4 + 1057433));
                                            
                                                
                                                while true do ::loop_266_start::
                                                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_265_fin; end;
                                                    reg7 = bit_tobit(reg1 + -1);
                                                    reg1 = reg7;
                                                    reg7 = __MEMORY_READ_8__(mem_0,reg2);
                                                    reg8 = bit_tobit(reg2 + 1);
                                                    reg2 = reg8;
                                                    if ((reg7 ~= (bit_band(reg0,255))) and 1 or 0)~=0 then goto loop_266_start; end;
                                                    break
                                                end
                                                
                                                reg1 = 0;
                                                goto block_8_fin;
                                            ::block_265_fin::
                                            reg4 = reg6;
                                            reg2 = reg5;
                                            if ((reg2 ~= 1057433) and 1 or 0)~=0 then goto loop_222_start; end;
                                        ::block_223_fin::
                                        break
                                    end
                                    
                                    reg7 = bit_band(reg0,65535);
                                    reg0 = reg7;
                                    reg2 = 1057608;
                                    reg1 = 1;
                                    
                                    while true do ::loop_307_start::
                                        reg6 = (bit_tobit(reg2 + 1));
                                        
                                            reg8 = __MEMORY_READ_8__(mem_0,reg2);
                                            reg4 = reg8;
                                            reg5 = (bit_arshift((bit_lshift(reg4,24)),24));
                                            if ((reg5 >= 0) and 1 or 0)~=0 then reg7 = reg6; goto block_312_fin; end;
                                            if ((reg6 == 1058027) and 1 or 0)~=0 then goto block_2_fin; end;
                                            reg8 = __MEMORY_READ_8__(mem_0,reg2+1);
                                            reg4 = (bit_bor(reg8,(bit_lshift((bit_band(reg5,127)),8))));
                                            reg7 = (bit_tobit(reg2 + 2))
                                            -- BLOCK RET (block):
                                        ::block_312_fin::
                                        reg2 = reg7;
                                        reg7 = bit_tobit(reg0 - reg4);
                                        reg0 = reg7;
                                        if ((reg0 < 0) and 1 or 0)~=0 then goto block_8_fin; end;
                                        reg7 = bit_bxor(reg1,1);
                                        reg1 = reg7;
                                        if ((reg2 ~= 1058027) and 1 or 0)~=0 then goto loop_307_start; end;
                                        break
                                    end
                                    
                                ::block_8_fin::
                                do return (bit_band(reg1,1)) end
                            ::block_7_fin::
                            __FUNCS__.func_85(reg4,reg6,1056644);
                            error('unreachable');
                        ::block_6_fin::
                        __FUNCS__.func_84(reg6,290,1056644);
                        error('unreachable');
                    ::block_5_fin::
                    __FUNCS__.func_110(1055017,43,1056660);
                    error('unreachable');
                ::block_4_fin::
                __FUNCS__.func_85(reg4,reg6,1056644);
                error('unreachable');
            ::block_3_fin::
            __FUNCS__.func_84(reg6,175,1056644);
            error('unreachable');
        ::block_2_fin::
        __FUNCS__.func_110(1055017,43,1056660);
        error('unreachable');
    end
    function __FUNCS__.func_23(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 128));
        __GLOBALS__[0] = reg4;
        
            reg5 = (FloatToUInt32(reg1));
            if (((bit_band(reg5,2147483647)) == 0) and 1 or 0)~=0 then reg3 = 4; goto block_8_fin; end;
            reg1 = (bit_band(reg5,8388607));
            reg6 = (bit_band((bit_rshift(reg5,23)),255));
            
            reg7 = ((reg6 == 0) and (bit_band((bit_lshift(reg5,1)),16777214)) or (bit_bor(reg1,8388608)));
            reg8 = (__LONG_INT__(reg7,0));
            reg9 = ((reg8):_and(__LONG_INT__(1,0)));
            
                reg10 = (bit_band(reg5,2139095040));
                if reg10==0 then goto if_47_fin end 
                    if ((reg10 ~= 2139095040) and 1 or 0)~=0 then goto block_42_fin; end;
                    
                    reg3 = ((reg1 == 0) and 3 or 2); goto block_8_fin;
                ::if_47_fin::
                reg10 = bit_tobit(reg6 + -150);
                reg6 = reg10;
                reg10 = __LONG_INT__(1,0);
                reg3 = (bit_bxor(((reg9)[1]),1)); goto block_8_fin;
            ::block_42_fin::
            reg1 = ((reg7 == 8388608) and 1 or 0);
            
            reg7 = (reg1 == 0) and ((reg8):_shl(__LONG_INT__(1,0))) or __LONG_INT__(33554432,0);
            reg8 = reg7;
            
            reg10 = ((reg1 == 0) and __LONG_INT__(1,0) or __LONG_INT__(2,0));
            
            reg7 = bit_tobit(((reg1 == 0) and -151 or -152) + reg6);
            reg6 = reg7;
            reg3 = (bit_bxor(((reg9)[1]),1))
            -- BLOCK RET (block):
        ::block_8_fin::
        reg1 = reg3;
        __MEMORY_WRITE_16__(mem_0,reg4+120,reg6);
        (reg10):store(mem_0,reg4+112);
        (__LONG_INT__(1,0)):store(mem_0,reg4+104);
        (reg8):store(mem_0,reg4+96);
        __MEMORY_WRITE_8__(mem_0,reg4+122,reg1);
        
            if ((reg1 == 2) and 1 or 0)==0 then goto if_117_fin end 
                reg6 = 1054920;
                reg3 = 0; goto block_113_fin;
            ::if_117_fin::
            reg7 = bit_band((bit_rshift(reg5,24)),128);
            reg5 = reg7;
            if ((reg2 == 0) and 1 or 0)==0 then goto if_131_fin end 
                
                reg6 = ((reg5 == 0) and 1054920 or 1054915);
                reg3 = (bit_rshift(reg5,7)); goto block_113_fin;
            ::if_131_fin::
            
            reg6 = ((reg5 == 0) and 1054916 or 1054915);
            reg3 = 1
            -- BLOCK RET (block):
        ::block_113_fin::
        reg2 = reg3;
        
            
                
                    
                        
                            reg5 = (bit_tobit(reg1 + -2));
                            
                            
                            if (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg5,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg5),255)) - 1)) == 0 then goto block_156_fin;
                            elseif (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg5,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg5),255)) - 1)) == 1 then goto block_154_fin;
                            elseif (bit_tobit((bit_band(((((__UNSIGNED__((bit_band(reg5,255))) < __UNSIGNED__(3)) and 1 or 0) == 0) and 3 or reg5),255)) - 1)) == 2 then goto block_155_fin;
                            else goto block_157_fin;
                            end
                        ::block_157_fin::
                        __MEMORY_WRITE_32__(mem_0,reg4+40,3);
                        __MEMORY_WRITE_32__(mem_0,reg4+36,1054924);
                        __MEMORY_WRITE_16__(mem_0,reg4+32,2);
                        __MEMORY_WRITE_32__(mem_0,reg4+84,reg2);
                        __MEMORY_WRITE_32__(mem_0,reg4+80,reg6);
                        __MEMORY_WRITE_32__(mem_0,reg4+88,(bit_tobit(reg4 + 32)));
                        reg3 = 1; goto block_153_fin;
                    ::block_156_fin::
                    __MEMORY_WRITE_32__(mem_0,reg4+40,3);
                    __MEMORY_WRITE_32__(mem_0,reg4+36,1054921);
                    __MEMORY_WRITE_16__(mem_0,reg4+32,2);
                    __MEMORY_WRITE_32__(mem_0,reg4+84,reg2);
                    __MEMORY_WRITE_32__(mem_0,reg4+80,reg6);
                    __MEMORY_WRITE_32__(mem_0,reg4+88,(bit_tobit(reg4 + 32)));
                    reg3 = 1; goto block_153_fin;
                ::block_155_fin::
                __FUNCS__.func_4((bit_tobit(reg4 + 32)),(bit_tobit(reg4 + 96)),(bit_tobit(reg4 + 15)));
                
                    reg1 = __MEMORY_READ_32__(mem_0,reg4+32);
                    if ((reg1 == 0) and 1 or 0)==0 then goto if_235_fin end 
                        __FUNCS__.func_0((bit_tobit(reg4 + 80)),(bit_tobit(reg4 + 96)),(bit_tobit(reg4 + 15)));
                        goto block_231_fin;
                    ::if_235_fin::
                    reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 40)));
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 88)),reg1);
                    reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg4+32);
                    (reg1):store(mem_0,reg4+80);
                ::block_231_fin::
                reg1 = __MEMORY_READ_32__(mem_0,reg4+80);
                reg5 = __MEMORY_READ_32__(mem_0,reg4+84);
                reg7 = __MEMORY_READ_16__(mem_0,reg4+88);
                __FUNCS__.func_42(reg4,reg1,reg5,reg7,1,(bit_tobit(reg4 + 32)));
                __MEMORY_WRITE_32__(mem_0,reg4+84,reg2);
                __MEMORY_WRITE_32__(mem_0,reg4+80,reg6);
                reg1 = __MEMORY_READ_32__(mem_0,reg4);
                __MEMORY_WRITE_32__(mem_0,reg4+88,reg1);
                reg1 = __MEMORY_READ_32__(mem_0,reg4+4);
                reg3 = reg1; goto block_153_fin;
            ::block_154_fin::
            __MEMORY_WRITE_16__(mem_0,reg4+32,2);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 48)),1);
            __MEMORY_WRITE_16__(mem_0,reg4+44,0);
            __MEMORY_WRITE_32__(mem_0,reg4+40,2);
            __MEMORY_WRITE_32__(mem_0,reg4+36,1054912);
            __MEMORY_WRITE_32__(mem_0,reg4+84,reg2);
            __MEMORY_WRITE_32__(mem_0,reg4+80,reg6);
            __MEMORY_WRITE_32__(mem_0,reg4+88,(bit_tobit(reg4 + 32)));
            reg3 = 2
            -- BLOCK RET (block):
        ::block_153_fin::
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 92)),reg3);
        reg1 = __FUNCS__.func_28(reg0,(bit_tobit(reg4 + 80)));
        __GLOBALS__[0] = (bit_tobit(reg4 + 128));
        do return reg1; end;
    end
    function __FUNCS__.func_24(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+56);
        __MEMORY_WRITE_32__(mem_0,reg1+56,(bit_tobit(reg2 + 4)));
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __MEMORY_WRITE_32__(mem_0,reg3+12,reg0);
        
            
                
                    
                        reg4 = __MEMORY_READ_32__(mem_0,reg1+60);
                        reg5 = reg4;
                        if ((reg5 == 0) and 1 or 0)==0 then goto if_24_fin end 
                            goto block_19_fin;
                        ::if_24_fin::
                        reg4 = (bit_tobit(8 - reg5));
                        
                        reg6 = ((((__UNSIGNED__(reg4) < __UNSIGNED__(4)) and 1 or 0) == 0) and 4 or reg4);
                        reg7 = reg0;
                        reg0 = ((__UNSIGNED__(reg6) > __UNSIGNED__(3)) and 1 or 0);
                        
                        reg8 = (__LONG_INT__(((reg0 == 0) and 0 or reg7),0));
                        reg7 = __LONG_INT__(0,0); reg7:load(mem_0,reg1+48);
                        
                            reg10 = (bit_lshift(reg0,2));
                            if ((__UNSIGNED__((bit_bor(reg10,1))) >= __UNSIGNED__(reg6)) and 1 or 0)==0 then goto if_57_fin end 
                                reg9 = reg10; goto block_48_fin;
                            ::if_57_fin::
                            reg11 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + reg10)));reg11=__LONG_INT__(reg11,0);
                            reg12 = (((reg11):_shl((__LONG_INT__((bit_lshift(reg10,3)),0))))):_or(reg8);
                            reg8 = reg12;
                            reg9 = (bit_bor(reg10,2))
                            -- BLOCK RET (block):
                        ::block_48_fin::
                        reg0 = reg9;
                        if ((__UNSIGNED__(reg0) < __UNSIGNED__(reg6)) and 1 or 0)==0 then goto if_82_else end 
                            reg9 = __MEMORY_READ_8__(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + reg0)));reg9=__LONG_INT__(reg9,0);
                            reg6 = ((((reg9):_shl((__LONG_INT__((bit_lshift(reg0,3)),0))))):_or(reg8))
                        goto if_82_fin
                        ::if_82_else::
                            reg6 = reg8
                            -- BLOCK RET (if):
                        ::if_82_fin::
                        reg8 = ((reg7):_or(((reg6):_shl((__LONG_INT__((bit_band((bit_lshift(reg5,3)),56)),0))))));
                        (reg8):store(mem_0,reg1+48);
                        if ((__UNSIGNED__(reg4) > __UNSIGNED__(4)) and 1 or 0)~=0 then goto block_18_fin; end;
                        reg0 = (bit_tobit(reg1 + 32));
                        reg10 = (bit_tobit(reg1 + 40));
                        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,reg10);
                        reg7 = ((reg6):_xor(reg8));
                        reg5 = (bit_tobit(reg1 + 24));
                        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,reg5);
                        reg9 = (reg7 + reg6);
                        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,reg0);
                        reg11 = reg6;
                        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,reg1+16);
                        reg12 = reg11 + reg6;
                        reg6 = (reg11):_rotl(__LONG_INT__(13,0));
                        reg11 = reg12;
                        reg12 = ((reg6):_xor(reg11));
                        reg6 = (reg9 + reg12);
                        (((reg6):_xor(((reg12):_rotl(__LONG_INT__(17,0)))))):store(mem_0,reg0);
                        (((reg6):_rotl(__LONG_INT__(32,0)))):store(mem_0,reg5);
                        reg13 = (reg9):_xor(((reg7):_rotl(__LONG_INT__(16,0))));
                        reg7 = reg13;
                        reg13 = reg7 + ((reg11):_rotl(__LONG_INT__(32,0)));
                        reg14 = (reg7):_rotl(__LONG_INT__(21,0));
                        reg7 = reg13;
                        (((reg14):_xor(reg7))):store(mem_0,reg10);
                        (((reg8):_xor(reg7))):store(mem_0,reg1+16);
                    ::block_19_fin::
                    reg0 = reg4;
                    reg10 = (bit_tobit(4 - reg4));
                    if ((__UNSIGNED__(reg4) < __UNSIGNED__((bit_band(reg10,-8)))) and 1 or 0)==0 then goto if_188_fin end 
                        reg13 = __LONG_INT__(0,0); reg13:load(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + reg4)));
                        reg8 = reg13;
                        reg13 = __LONG_INT__(0,0); reg13:load(mem_0,reg1+40);
                        reg7 = ((reg8):_xor(reg13));
                        reg13 = __LONG_INT__(0,0); reg13:load(mem_0,reg1+24);
                        reg9 = (reg7 + reg13);
                        reg13 = __LONG_INT__(0,0); reg13:load(mem_0,reg1+32);
                        reg11 = reg13;
                        reg13 = __LONG_INT__(0,0); reg13:load(mem_0,reg1+16);
                        reg12 = (reg11 + reg13);
                        reg13 = (reg12):_xor(((reg11):_rotl(__LONG_INT__(13,0))));
                        reg11 = reg13;
                        reg6 = (reg9 + reg11);
                        (((reg6):_xor(((reg11):_rotl(__LONG_INT__(17,0)))))):store(mem_0,reg1+32);
                        (((reg6):_rotl(__LONG_INT__(32,0)))):store(mem_0,reg1+24);
                        reg6 = (((reg7):_rotl(__LONG_INT__(16,0)))):_xor(reg9);
                        reg7 = reg6;
                        reg6 = reg7 + ((reg12):_rotl(__LONG_INT__(32,0)));
                        reg9 = (reg7):_rotl(__LONG_INT__(21,0));
                        reg7 = reg6;
                        (((reg9):_xor(reg7))):store(mem_0,reg1+40);
                        (((reg8):_xor(reg7))):store(mem_0,reg1+16);
                        reg0 = (bit_tobit(reg4 + 8));
                    ::if_188_fin::
                    if ((reg4 == 0) and 1 or 0)~=0 then goto block_17_fin; end;
                    reg8 = __LONG_INT__(0,0);
                    reg2 = 0; goto block_16_fin;
                ::block_18_fin::
                __MEMORY_WRITE_32__(mem_0,reg1+60,(bit_tobit(reg5 + 4)));
                do return  end
            ::block_17_fin::
            reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + reg0)));reg5=__LONG_INT__(reg5,0);
            reg8 = reg5;
            reg2 = 4
            -- BLOCK RET (block):
        ::block_16_fin::
        reg4 = reg2;
        if ((__UNSIGNED__((bit_bor(reg4,1))) < __UNSIGNED__(reg10)) and 1 or 0)==0 then goto if_285_fin end 
            reg2 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + (bit_tobit(reg0 + reg4)))));reg2=__LONG_INT__(reg2,0);
            reg5 = (((reg2):_shl((__LONG_INT__((bit_lshift(reg4,3)),0))))):_or(reg8);
            reg8 = reg5;
            reg2 = bit_bor(reg4,2);
            reg4 = reg2;
        ::if_285_fin::
        if ((__UNSIGNED__(reg4) < __UNSIGNED__(reg10)) and 1 or 0)==0 then goto if_310_else end 
            reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit((bit_tobit(reg3 + 12)) + (bit_tobit(reg0 + reg4)))));reg5=__LONG_INT__(reg5,0);
            reg2 = ((((reg5):_shl((__LONG_INT__((bit_lshift(reg4,3)),0))))):_or(reg8))
        goto if_310_fin
        ::if_310_else::
            reg2 = reg8
            -- BLOCK RET (if):
        ::if_310_fin::
        (reg2):store(mem_0,reg1+48);
        __MEMORY_WRITE_32__(mem_0,reg1+60,reg10);
    end
    function __FUNCS__.func_25(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        
            
                reg4 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg5 = reg4;
                if ((reg5 == 0) and 1 or 0)==0 then goto if_13_fin end 
                    reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg6 = reg4;
                    reg4 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg7 = reg4;
                    goto block_8_fin;
                ::if_13_fin::
                reg4 = __MEMORY_READ_32__(mem_0,reg0+24);
                reg7 = reg4;
                reg4 = __MEMORY_READ_32__(mem_0,reg1);
                reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                reg6 = reg8;
                reg8 = __MEMORY_READ_32__(mem_0,reg6+12);
                reg8 = __TABLE_FUNCS_0__[reg8+1](reg7,reg4,reg5);
                if reg8~=0 then reg2 = 1; goto block_7_fin; end;
            ::block_8_fin::
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 12)));
            reg0 = reg4;
            if ((reg0 == 0) and 1 or 0)~=0 then reg2 = 0; goto block_7_fin; end;
            reg4 = __MEMORY_READ_32__(mem_0,reg1+8);
            reg5 = reg4;
            reg4 = (bit_tobit(reg5 + (__IMUL__(reg0,12))));
            reg8 = (bit_tobit(reg3 + 12));
            
            while true do ::loop_62_start::
                
                    
                        
                            
                                reg9 = __MEMORY_READ_16__(mem_0,reg5);
                                
                                if (bit_tobit(reg9 - 1)) == 0 then goto block_64_fin;
                                elseif (bit_tobit(reg9 - 1)) == 1 then goto block_65_fin;
                                else goto block_66_fin;
                                end
                            ::block_66_fin::
                            
                                reg9 = __MEMORY_READ_32__(mem_0,reg5+4);
                                reg1 = reg9;
                                if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65)) and 1 or 0)==0 then goto if_79_fin end 
                                    reg9 = __MEMORY_READ_32__(mem_0,reg6+12);
                                    reg0 = reg9;
                                    
                                    while true do ::loop_83_start::
                                        reg9 = __TABLE_FUNCS_0__[reg0+1](reg7,1055764,64);
                                        if reg9~=0 then reg2 = 1; goto block_7_fin; end;
                                        reg9 = bit_tobit(reg1 + -64);
                                        reg1 = reg9;
                                        if ((__UNSIGNED__(reg1) > __UNSIGNED__(64)) and 1 or 0)~=0 then goto loop_83_start; end;
                                        break
                                    end
                                    
                                    goto block_73_fin;
                                ::if_79_fin::
                                if ((reg1 == 0) and 1 or 0)~=0 then goto block_63_fin; end;
                            ::block_73_fin::
                            
                                if ((__UNSIGNED__(reg1) <= __UNSIGNED__(63)) and 1 or 0)==0 then goto if_110_fin end 
                                    reg9 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 1055764)));reg9=bit_arshift(bit_lshift(reg9,24),24);
                                    if ((reg9 <= -65) and 1 or 0)~=0 then goto block_106_fin; end;
                                ::if_110_fin::
                                reg9 = __MEMORY_READ_32__(mem_0,reg6+12);
                                reg9 = __TABLE_FUNCS_0__[reg9+1](reg7,1055764,reg1);
                                if ((reg9 == 0) and 1 or 0)~=0 then goto block_63_fin; end;
                                reg2 = 1; goto block_7_fin;
                            ::block_106_fin::
                            __FUNCS__.func_7(1055764,64,0,reg1,1055828);
                            error('unreachable');
                        ::block_65_fin::
                        reg9 = __MEMORY_READ_32__(mem_0,reg5+4);
                        reg10 = __MEMORY_READ_32__(mem_0,reg5+8);
                        reg11 = __MEMORY_READ_32__(mem_0,reg6+12);
                        reg11 = __TABLE_FUNCS_0__[reg11+1](reg7,reg9,reg10);
                        if ((reg11 == 0) and 1 or 0)~=0 then goto block_63_fin; end;
                        reg2 = 1; goto block_7_fin;
                    ::block_64_fin::
                    reg9 = __MEMORY_READ_16__(mem_0,reg5+2);
                    reg1 = reg9;
                    __MEMORY_WRITE_8__(mem_0,reg8,0);
                    __MEMORY_WRITE_32__(mem_0,reg3+8,0);
                    reg0 = 1;
                    
                        
                            
                                
                                    
                                        reg9 = __MEMORY_READ_16__(mem_0,reg5);
                                        
                                        if (bit_tobit(reg9 - 1)) == 0 then goto block_166_fin;
                                        elseif (bit_tobit(reg9 - 1)) == 1 then goto block_165_fin;
                                        else goto block_164_fin;
                                        end
                                    ::block_166_fin::
                                    reg9 = __MEMORY_READ_16__(mem_0,reg5+2);
                                    reg0 = reg9;
                                    if ((__UNSIGNED__(reg0) >= __UNSIGNED__(1000)) and 1 or 0)==0 then goto if_178_fin end 
                                        
                                        reg9 = ((((__UNSIGNED__(reg0) < __UNSIGNED__(10000)) and 1 or 0) == 0) and 5 or 4);
                                        goto block_163_fin;
                                    ::if_178_fin::
                                    reg9 = 1;
                                    if ((__UNSIGNED__(reg0) < __UNSIGNED__(10)) and 1 or 0)~=0 then goto block_163_fin; end;
                                    
                                    reg9 = ((((__UNSIGNED__(reg0) < __UNSIGNED__(100)) and 1 or 0) == 0) and 3 or 2);
                                    goto block_163_fin;
                                ::block_165_fin::
                                reg0 = 2;
                            ::block_164_fin::
                            reg10 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + (bit_lshift(reg0,2)))));
                            reg9 = reg10;
                            if ((__UNSIGNED__(reg9) < __UNSIGNED__(6)) and 1 or 0)==0 then goto if_215_fin end 
                                if reg9~=0 then goto block_163_fin; end;
                                reg9 = 0;
                                goto block_162_fin;
                            ::if_215_fin::
                            __FUNCS__.func_84(reg9,5,1055748);
                            error('unreachable');
                        ::block_163_fin::
                        reg10 = (bit_tobit((bit_tobit(reg3 + 8)) + reg9));
                        
                            if (((bit_band(reg9,1)) == 0) and 1 or 0)==0 then goto if_239_fin end 
                                reg0 = reg1;
                                goto block_234_fin;
                            ::if_239_fin::
                            reg11 = bit_tobit(reg10 + -1);
                            reg10 = reg11;
                            reg0 = (__IDIV_U__(reg1,10));
                            __MEMORY_WRITE_8__(mem_0,reg10,(bit_bor((bit_tobit(reg1 - (__IMUL__(reg0,10)))),48)));
                        ::block_234_fin::
                        if ((reg9 == 1) and 1 or 0)~=0 then goto block_162_fin; end;
                        reg1 = (bit_tobit(reg10 + -2));
                        
                        while true do ::loop_268_start::
                            reg10 = (bit_band(reg0,65535));
                            reg11 = (__IDIV_U__(reg10,10));
                            __MEMORY_WRITE_8__(mem_0,reg1,(bit_bor((__IMOD_U__(reg11,10)),48)));
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + 1)),(bit_bor((bit_tobit(reg0 - (__IMUL__(reg11,10)))),48)));
                            reg0 = (__IDIV_U__(reg10,100));
                            reg11 = bit_tobit(reg1 + -2);
                            reg12 = (reg1 == (bit_tobit(reg3 + 8))) and 1 or 0;
                            reg1 = reg11;
                            if ((reg12 == 0) and 1 or 0)~=0 then goto loop_268_start; end;
                            break
                        end
                        
                    ::block_162_fin::
                    reg11 = __MEMORY_READ_32__(mem_0,reg6+12);
                    reg11 = __TABLE_FUNCS_0__[reg11+1](reg7,(bit_tobit(reg3 + 8)),reg9);
                    if ((reg11 == 0) and 1 or 0)~=0 then goto block_63_fin; end;
                    reg2 = 1; goto block_7_fin;
                ::block_63_fin::
                reg11 = bit_tobit(reg5 + 12);
                reg5 = reg11;
                if ((reg4 ~= reg5) and 1 or 0)~=0 then goto loop_62_start; end;
                break
            end
            
            reg2 = 0
            -- BLOCK RET (block):
        ::block_7_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg2; end;
    end
    function __FUNCS__.func_26(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11;
        reg3 = (bit_tobit((bit_band((bit_tobit(reg1 + 3)),-4)) - reg1));
        reg4 = ((__UNSIGNED__(reg2) < __UNSIGNED__(reg3)) and 1 or 0);
        
        reg5 = ((reg4 == 0) and (bit_band((bit_tobit(reg2 - reg3)),7)) or 0);
        reg6 = (bit_tobit(reg2 - reg5));
        
            
                
                    
                        if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg5)) and 1 or 0)==0 then goto if_31_fin end 
                            if ((reg5 == 0) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg8 = (bit_tobit(reg1 + reg2));
                            reg9 = (bit_tobit(reg1 + reg6));
                            reg10 = (bit_tobit(reg8 - reg9));
                            reg5 = (bit_tobit(reg8 + -1));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_52_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -1)) + reg6));
                                goto block_26_fin;
                            ::if_52_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -2));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_72_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -2)) + reg6));
                                goto block_26_fin;
                            ::if_72_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -3));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_92_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -3)) + reg6));
                                goto block_26_fin;
                            ::if_92_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -4));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_112_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -4)) + reg6));
                                goto block_26_fin;
                            ::if_112_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -5));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_132_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -5)) + reg6));
                                goto block_26_fin;
                            ::if_132_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -6));
                            reg11 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg11 == 10) and 1 or 0)==0 then goto if_152_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -6)) + reg6));
                                goto block_26_fin;
                            ::if_152_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit(reg8 + -7));
                            reg8 = __MEMORY_READ_8__(mem_0,reg5);
                            if ((reg8 == 10) and 1 or 0)==0 then goto if_172_fin end 
                                reg5 = (bit_tobit((bit_tobit(reg10 + -7)) + reg6));
                                goto block_26_fin;
                            ::if_172_fin::
                            if ((reg5 == reg9) and 1 or 0)~=0 then goto block_27_fin; end;
                            reg5 = (bit_tobit((bit_tobit(reg10 + -8)) + reg6));
                            goto block_26_fin;
                        ::if_31_fin::
                        __FUNCS__.func_83(reg6,reg2,1055904);
                        error('unreachable');
                    ::block_27_fin::
                    
                    reg9 = ((reg4 == 0) and reg3 or reg2);
                    
                    while true do ::loop_204_start::
                        reg5 = reg6;
                        if ((__UNSIGNED__(reg5) > __UNSIGNED__(reg9)) and 1 or 0)==0 then goto if_209_fin end 
                            reg6 = (bit_tobit(reg5 + -8));
                            reg3 = (bit_tobit(reg1 + reg5));
                            reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + -8)));
                            reg4 = (bit_bxor(reg8,168430090));
                            reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + -4)));
                            reg10 = bit_band((bit_bxor(reg4,-1)),(bit_tobit(reg4 + -16843009)));
                            reg4 = (bit_bxor(reg8,168430090));
                            if (((bit_band((bit_bor(reg10,(bit_band((bit_bxor(reg4,-1)),(bit_tobit(reg4 + -16843009)))))),-2139062144)) == 0) and 1 or 0)~=0 then goto loop_204_start; end;
                        ::if_209_fin::
                        break
                    end
                    
                    if ((__UNSIGNED__(reg5) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_24_fin; end;
                    reg2 = (bit_tobit(reg1 + -1));
                    
                    while true do ::loop_258_start::
                        if ((reg5 == 0) and 1 or 0)~=0 then reg7 = 0; goto block_25_fin; end;
                        reg8 = bit_tobit(reg5 + -1);
                        reg10 = bit_tobit(reg2 + reg5);
                        reg5 = reg8;
                        reg8 = __MEMORY_READ_8__(mem_0,reg10);
                        if ((reg8 ~= 10) and 1 or 0)~=0 then goto loop_258_start; end;
                        break
                    end
                    
                ::block_26_fin::
                reg7 = 1
                -- BLOCK RET (block):
            ::block_25_fin::
            reg1 = reg7;
            __MEMORY_WRITE_32__(mem_0,reg0+4,reg5);
            __MEMORY_WRITE_32__(mem_0,reg0,reg1);
            do return  end
        ::block_24_fin::
        __FUNCS__.func_84(reg5,reg2,1055920);
        error('unreachable');
    end
    function __FUNCS__.func_27(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 36)),reg1);
        __MEMORY_WRITE_8__(mem_0,reg4+40,3);
        (__LONG_INT__(0,32)):store(mem_0,reg4+8);
        __MEMORY_WRITE_32__(mem_0,reg4+32,reg0);
        __MEMORY_WRITE_32__(mem_0,reg4+24,0);
        __MEMORY_WRITE_32__(mem_0,reg4+16,0);
        
            
                
                    reg3 = __MEMORY_READ_32__(mem_0,reg2+8);
                    reg5 = reg3;
                    if ((reg5 == 0) and 1 or 0)==0 then goto if_34_fin end 
                        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 20)));
                        reg6 = reg3;
                        if ((reg6 == 0) and 1 or 0)~=0 then goto block_29_fin; end;
                        reg3 = __MEMORY_READ_32__(mem_0,reg2);
                        reg1 = reg3;
                        reg3 = __MEMORY_READ_32__(mem_0,reg2+16);
                        reg0 = reg3;
                        reg3 = (bit_tobit((bit_rshift((bit_tobit((bit_lshift(reg6,3)) + -8)),3)) + 1));
                        reg6 = reg3;
                        
                        while true do ::loop_59_start::
                            reg7 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                            reg8 = reg7;
                            if reg8==0 then goto if_65_fin end 
                                reg7 = __MEMORY_READ_32__(mem_0,reg4+32);
                                reg9 = __MEMORY_READ_32__(mem_0,reg1);
                                reg10 = __MEMORY_READ_32__(mem_0,reg4+36);
                                reg11 = __MEMORY_READ_32__(mem_0,reg10+12);
                                reg10 = __TABLE_FUNCS_0__[reg11+1](reg7,reg9,reg8);
                                if reg10~=0 then goto block_28_fin; end;
                            ::if_65_fin::
                            reg7 = __MEMORY_READ_32__(mem_0,reg0);
                            reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                            reg9 = __TABLE_FUNCS_0__[reg9+1](reg7,(bit_tobit(reg4 + 8)));
                            if reg9~=0 then goto block_28_fin; end;
                            reg7 = bit_tobit(reg0 + 8);
                            reg0 = reg7;
                            reg7 = bit_tobit(reg1 + 8);
                            reg1 = reg7;
                            reg7 = bit_tobit(reg6 + -1);
                            reg6 = reg7;
                            if reg6~=0 then goto loop_59_start; end;
                            break
                        end
                        
                        goto block_29_fin;
                    ::if_34_fin::
                    reg7 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 12)));
                    reg0 = reg7;
                    if ((reg0 == 0) and 1 or 0)~=0 then goto block_29_fin; end;
                    reg7 = (bit_lshift(reg0,5));
                    reg3 = (bit_tobit((bit_rshift((bit_tobit(reg7 + -32)),5)) + 1));
                    reg9 = __MEMORY_READ_32__(mem_0,reg2);
                    reg1 = reg9;
                    
                    while true do ::loop_125_start::
                        reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                        reg0 = reg9;
                        if reg0==0 then goto if_131_fin end 
                            reg9 = __MEMORY_READ_32__(mem_0,reg4+32);
                            reg10 = __MEMORY_READ_32__(mem_0,reg1);
                            reg11 = __MEMORY_READ_32__(mem_0,reg4+36);
                            reg12 = __MEMORY_READ_32__(mem_0,reg11+12);
                            reg11 = __TABLE_FUNCS_0__[reg12+1](reg9,reg10,reg0);
                            if reg11~=0 then goto block_28_fin; end;
                        ::if_131_fin::
                        reg8 = (bit_tobit(reg6 + reg5));
                        reg9 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg8 + 28)));
                        __MEMORY_WRITE_8__(mem_0,reg4+40,reg9);
                        reg9 = __LONG_INT__(0,0); reg9:load(mem_0,(bit_tobit(reg8 + 4)));
                        (((reg9):_rotl(__LONG_INT__(32,0)))):store(mem_0,reg4+8);
                        reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + 24)));
                        reg10 = reg9;
                        reg9 = __MEMORY_READ_32__(mem_0,reg2+16);
                        reg11 = reg9;
                        reg9 = 0;
                        reg0 = 0;
                        
                            
                                
                                    reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + 20)));
                                    
                                    if (bit_tobit(reg12 - 1)) == 0 then goto block_174_fin;
                                    elseif (bit_tobit(reg12 - 1)) == 1 then goto block_172_fin;
                                    else goto block_173_fin;
                                    end
                                ::block_174_fin::
                                reg12 = (bit_tobit((bit_lshift(reg10,3)) + reg11));
                                reg13 = __MEMORY_READ_32__(mem_0,reg12+4);
                                if ((reg13 ~= 50) and 1 or 0)~=0 then goto block_172_fin; end;
                                reg13 = __MEMORY_READ_32__(mem_0,reg12);
                                reg14 = __MEMORY_READ_32__(mem_0,reg13);
                                reg10 = reg14;
                            ::block_173_fin::
                            reg0 = 1;
                        ::block_172_fin::
                        __MEMORY_WRITE_32__(mem_0,reg4+20,reg10);
                        __MEMORY_WRITE_32__(mem_0,reg4+16,reg0);
                        reg13 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + 16)));
                        reg0 = reg13;
                        
                            
                                
                                    reg13 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg8 + 12)));
                                    
                                    if (bit_tobit(reg13 - 1)) == 0 then goto block_214_fin;
                                    elseif (bit_tobit(reg13 - 1)) == 1 then goto block_212_fin;
                                    else goto block_213_fin;
                                    end
                                ::block_214_fin::
                                reg10 = (bit_tobit((bit_lshift(reg0,3)) + reg11));
                                reg13 = __MEMORY_READ_32__(mem_0,reg10+4);
                                if ((reg13 ~= 50) and 1 or 0)~=0 then goto block_212_fin; end;
                                reg13 = __MEMORY_READ_32__(mem_0,reg10);
                                reg14 = __MEMORY_READ_32__(mem_0,reg13);
                                reg0 = reg14;
                            ::block_213_fin::
                            reg9 = 1;
                        ::block_212_fin::
                        __MEMORY_WRITE_32__(mem_0,reg4+28,reg0);
                        __MEMORY_WRITE_32__(mem_0,reg4+24,reg9);
                        reg13 = __MEMORY_READ_32__(mem_0,reg8);
                        reg0 = (bit_tobit(reg11 + (bit_lshift(reg13,3))));
                        reg8 = __MEMORY_READ_32__(mem_0,reg0);
                        reg11 = __MEMORY_READ_32__(mem_0,reg0+4);
                        reg11 = __TABLE_FUNCS_0__[reg11+1](reg8,(bit_tobit(reg4 + 8)));
                        if reg11~=0 then goto block_28_fin; end;
                        reg8 = bit_tobit(reg1 + 8);
                        reg1 = reg8;
                        reg8 = bit_tobit(reg6 + 32);
                        reg6 = reg8;
                        if ((reg7 ~= reg6) and 1 or 0)~=0 then goto loop_125_start; end;
                        break
                    end
                    
                ::block_29_fin::
                reg0 = 0;
                reg8 = __MEMORY_READ_32__(mem_0,reg2+4);
                reg1 = ((__UNSIGNED__(reg3) < __UNSIGNED__(reg8)) and 1 or 0);
                if ((reg1 == 0) and 1 or 0)~=0 then goto block_27_fin; end;
                reg8 = __MEMORY_READ_32__(mem_0,reg4+32);
                reg11 = __MEMORY_READ_32__(mem_0,reg2);
                
                reg2 = (reg1 == 0) and 0 or (bit_tobit(reg11 + (bit_lshift(reg3,3))));
                reg1 = reg2;
                reg2 = __MEMORY_READ_32__(mem_0,reg1);
                reg3 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg1 = __MEMORY_READ_32__(mem_0,reg4+36);
                reg11 = __MEMORY_READ_32__(mem_0,reg1+12);
                reg1 = __TABLE_FUNCS_0__[reg11+1](reg8,reg2,reg3);
                if ((reg1 == 0) and 1 or 0)~=0 then goto block_27_fin; end;
            ::block_28_fin::
            reg0 = 1;
        ::block_27_fin::
        __GLOBALS__[0] = (bit_tobit(reg4 + 48));
        do return reg0; end;
    end
    function __FUNCS__.func_28(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13,reg14;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        
            
                
                    
                        reg4 = __MEMORY_READ_32__(mem_0,reg0+8);
                        if ((reg4 == 1) and 1 or 0)==0 then goto if_15_fin end 
                            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                            reg5 = reg4;
                            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 12)));
                            reg6 = reg4;
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 12)),reg6);
                            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 8)));
                            reg7 = reg4;
                            __MEMORY_WRITE_32__(mem_0,reg3+8,reg7);
                            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                            reg8 = reg4;
                            __MEMORY_WRITE_32__(mem_0,reg3+4,reg8);
                            reg4 = __MEMORY_READ_32__(mem_0,reg1);
                            reg1 = reg4;
                            __MEMORY_WRITE_32__(mem_0,reg3,reg1);
                            reg4 = __MEMORY_READ_8__(mem_0,reg0+32);
                            reg9 = reg4;
                            reg4 = __MEMORY_READ_32__(mem_0,reg0+4);
                            reg10 = reg4;
                            reg4 = __MEMORY_READ_8__(mem_0,reg0);
                            if (bit_band(reg4,8))~=0 then goto block_10_fin; end;
                            reg4 = reg10;
                            reg11 = reg9;
                            reg2 = reg8; goto block_9_fin;
                        ::if_15_fin::
                        reg12 = __FUNCS__.func_25(reg0,reg1);
                        reg7 = reg12;
                        goto block_7_fin;
                    ::block_10_fin::
                    reg12 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg13 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg14 = __MEMORY_READ_32__(mem_0,reg13+12);
                    reg13 = __TABLE_FUNCS_0__[reg14+1](reg12,reg1,reg8);
                    if reg13~=0 then goto block_8_fin; end;
                    reg11 = 1;
                    __MEMORY_WRITE_8__(mem_0,reg0+32,1);
                    reg4 = 48;
                    __MEMORY_WRITE_32__(mem_0,reg0+4,48);
                    __MEMORY_WRITE_32__(mem_0,reg3+4,0);
                    __MEMORY_WRITE_32__(mem_0,reg3,1054920);
                    reg12 = bit_tobit(reg5 - reg8);
                    reg8 = reg12;
                    
                    reg12 = (((__UNSIGNED__(reg8) > __UNSIGNED__(reg5)) and 1 or 0) == 0) and reg8 or 0;
                    reg5 = reg12;
                    reg2 = 0
                    -- BLOCK RET (block):
                ::block_9_fin::
                reg1 = reg2;
                if reg6==0 then goto if_114_fin end 
                    reg8 = (__IMUL__(reg6,12));
                    
                    while true do ::loop_119_start::
                        
                            
                                
                                    
                                        reg12 = __MEMORY_READ_16__(mem_0,reg7);
                                        
                                        if (bit_tobit(reg12 - 1)) == 0 then goto block_121_fin;
                                        elseif (bit_tobit(reg12 - 1)) == 1 then goto block_122_fin;
                                        else goto block_123_fin;
                                        end
                                    ::block_123_fin::
                                    reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + 4)));
                                    reg2 = reg12; goto block_120_fin;
                                ::block_122_fin::
                                reg12 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + 8)));
                                reg2 = reg12; goto block_120_fin;
                            ::block_121_fin::
                            reg12 = __MEMORY_READ_16__(mem_0,(bit_tobit(reg7 + 2)));
                            reg6 = reg12;
                            if ((__UNSIGNED__(reg6) >= __UNSIGNED__(1000)) and 1 or 0)==0 then goto if_149_fin end 
                                
                                reg2 = ((((__UNSIGNED__(reg6) < __UNSIGNED__(10000)) and 1 or 0) == 0) and 5 or 4); goto block_120_fin;
                            ::if_149_fin::
                            if ((__UNSIGNED__(reg6) < __UNSIGNED__(10)) and 1 or 0)~=0 then reg2 = 1; goto block_120_fin; end;
                            
                            reg2 = ((((__UNSIGNED__(reg6) < __UNSIGNED__(100)) and 1 or 0) == 0) and 3 or 2)
                            -- BLOCK RET (block):
                        ::block_120_fin::
                        reg6 = reg2;
                        reg2 = bit_tobit(reg7 + 12);
                        reg7 = reg2;
                        reg2 = bit_tobit(reg1 + reg6);
                        reg1 = reg2;
                        reg2 = bit_tobit(reg8 + -12);
                        reg8 = reg2;
                        if reg8~=0 then goto loop_119_start; end;
                        break
                    end
                    
                ::if_114_fin::
                
                    
                        if ((__UNSIGNED__(reg5) > __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_192_fin end 
                            reg7 = 0;
                            reg12 = bit_tobit(reg5 - reg1);
                            reg1 = reg12;
                            reg8 = reg1;
                            
                                
                                    
                                        
                                        if (bit_tobit((bit_band(reg11,3)) - 1)) == 0 then goto block_202_fin;
                                        elseif (bit_tobit((bit_band(reg11,3)) - 1)) == 1 then goto block_201_fin;
                                        elseif (bit_tobit((bit_band(reg11,3)) - 1)) == 2 then goto block_202_fin;
                                        else goto block_200_fin;
                                        end
                                    ::block_202_fin::
                                    reg8 = 0;
                                    reg7 = reg1;
                                    goto block_200_fin;
                                ::block_201_fin::
                                reg7 = (bit_rshift(reg1,1));
                                reg8 = (bit_rshift((bit_tobit(reg1 + 1)),1));
                            ::block_200_fin::
                            reg5 = bit_tobit(reg7 + 1);
                            reg7 = reg5;
                            reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                            reg1 = reg5;
                            reg5 = __MEMORY_READ_32__(mem_0,reg0+24);
                            reg11 = reg5;
                            
                            while true do ::loop_239_start::
                                reg5 = bit_tobit(reg7 + -1);
                                reg7 = reg5;
                                if ((reg7 == 0) and 1 or 0)~=0 then goto block_188_fin; end;
                                reg5 = __MEMORY_READ_32__(mem_0,reg1+16);
                                reg5 = __TABLE_FUNCS_0__[reg5+1](reg11,reg4);
                                if ((reg5 == 0) and 1 or 0)~=0 then goto loop_239_start; end;
                                break
                            end
                            
                            goto block_8_fin;
                        ::if_192_fin::
                        reg5 = __FUNCS__.func_25(reg0,reg3);
                        reg2 = reg5; goto block_187_fin;
                    ::block_188_fin::
                    reg5 = __FUNCS__.func_25(reg0,reg3);
                    if reg5~=0 then goto block_8_fin; end;
                    reg7 = 0;
                    
                    while true do ::loop_267_start::
                        if ((reg7 == reg8) and 1 or 0)~=0 then reg2 = 0; goto block_187_fin; end;
                        reg5 = bit_tobit(reg7 + 1);
                        reg7 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,reg1+16);
                        reg5 = __TABLE_FUNCS_0__[reg5+1](reg11,reg4);
                        if ((reg5 == 0) and 1 or 0)~=0 then goto loop_267_start; end;
                        break
                    end
                    
                    reg2 = ((__UNSIGNED__((bit_tobit(reg7 + -1))) < __UNSIGNED__(reg8)) and 1 or 0)
                    -- BLOCK RET (block):
                ::block_187_fin::
                reg7 = reg2;
                __MEMORY_WRITE_8__(mem_0,reg0+32,reg9);
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg10);
                goto block_7_fin;
            ::block_8_fin::
            reg7 = 1;
        ::block_7_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg7; end;
    end
    function __FUNCS__.func_29(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 + -64));
        __GLOBALS__[0] = reg2;
        
            
                
                    
                        reg3 = __MEMORY_READ_32__(mem_0,reg0);
                        reg4 = reg3;
                        if ((reg4 == 0) and 1 or 0)~=0 then reg1 = 0; goto block_11_fin; end;
                        reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg0+4);
                        (reg3):store(mem_0,reg2+44);
                        __MEMORY_WRITE_32__(mem_0,reg2+40,reg4);
                        reg0 = (bit_tobit(reg2 + 24));
                        reg3 = (bit_tobit(reg2 + 40));
                        reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg3);
                        (reg5):store(mem_0,reg0);
                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 8)));
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),reg5);
                        reg5 = __MEMORY_READ_32__(mem_0,reg2+24);
                        reg3 = reg5;
                        
                            reg5 = __MEMORY_READ_32__(mem_0,reg2+32);
                            reg0 = reg5;
                            if ((__UNSIGNED__(reg0) >= __UNSIGNED__(8)) and 1 or 0)==0 then goto if_53_fin end 
                                __FUNCS__.func_45((bit_tobit(reg2 + 16)),0,reg3,reg0);
                                reg5 = __MEMORY_READ_32__(mem_0,reg2+20);
                                reg0 = reg5;
                                reg5 = __MEMORY_READ_32__(mem_0,reg2+16);
                                reg4 = reg5;
                                goto block_47_fin;
                            ::if_53_fin::
                            if ((reg0 == 0) and 1 or 0)==0 then goto if_71_fin end 
                                reg0 = 0;
                                reg4 = 0;
                                goto block_47_fin;
                            ::if_71_fin::
                            
                                reg5 = __MEMORY_READ_8__(mem_0,reg3);
                                if ((reg5 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 1;
                                reg4 = 0;
                                if ((reg0 == 1) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+1);
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 2;
                                if ((reg0 == 2) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+2);
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 3;
                                if ((reg0 == 3) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+3);
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 4;
                                if ((reg0 == 4) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+4);
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 5;
                                if ((reg0 == 5) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+5);
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_78_fin; end;
                                reg5 = 6;
                                if ((reg0 == 6) and 1 or 0)~=0 then goto block_47_fin; end;
                                reg6 = __MEMORY_READ_8__(mem_0,reg3+6);
                                if reg6~=0 then goto block_47_fin; end;
                            ::block_78_fin::
                            reg4 = 1;
                            reg0 = reg5;
                        ::block_47_fin::
                        if reg4~=0 then goto block_10_fin; end;
                        reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 32)));
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 48)),reg6);
                        reg6 = __LONG_INT__(0,0); reg6:load(mem_0,reg2+24);
                        (reg6):store(mem_0,reg2+40);
                        __FUNCS__.func_47((bit_tobit(reg2 + 8)),(bit_tobit(reg2 + 40)));
                        reg6 = __MEMORY_READ_32__(mem_0,reg2+12);
                        reg4 = reg6;
                        reg6 = __MEMORY_READ_32__(mem_0,reg2+8);
                        reg1 = reg6
                        -- BLOCK RET (block):
                    ::block_11_fin::
                    reg5 = reg1;
                    reg1 = __MEMORY_READ_8__(mem_0,1059656);
                    reg0 = reg1;
                    __MEMORY_WRITE_8__(mem_0,1059656,1);
                    __MEMORY_WRITE_8__(mem_0,reg2+24,reg0);
                    if reg0~=0 then goto block_9_fin; end;
                    
                        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,1059064);
                        reg6 = reg1;
                        if ((reg6 ~= __LONG_INT__(-1,-1)) and 1 or 0)==0 then goto if_195_fin end 
                            ((reg6 + __LONG_INT__(1,0))):store(mem_0,1059064);
                            if ((reg6 ~= __LONG_INT__(0,0)) and 1 or 0)~=0 then goto block_189_fin; end;
                            __FUNCS__.func_110(1049216,43,1049508);
                            error('unreachable');
                        ::if_195_fin::
                        __MEMORY_WRITE_8__(mem_0,1059656,0);
                        __FUNCS__.func_126(1049437,55,1049492);
                        error('unreachable');
                    ::block_189_fin::
                    __MEMORY_WRITE_8__(mem_0,1059656,0);
                    reg1 = __FUNCS__.func_148(32,8);
                    reg0 = reg1;
                    if ((reg0 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                    (__LONG_INT__(0,0)):store(mem_0,reg0+24);
                    __MEMORY_WRITE_32__(mem_0,reg0+20,reg4);
                    __MEMORY_WRITE_32__(mem_0,reg0+16,reg5);
                    (reg6):store(mem_0,reg0+8);
                    (__LONG_INT__(1,1)):store(mem_0,reg0);
                    __GLOBALS__[0] = (bit_tobit(reg2 - -64));
                    do return reg0 end
                ::block_10_fin::
                reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg2+28);
                (reg1):store(mem_0,(bit_tobit(reg2 + 48)));
                __MEMORY_WRITE_32__(mem_0,reg2+44,reg3);
                __MEMORY_WRITE_32__(mem_0,reg2+40,reg0);
                __FUNCS__.func_79(1049524,47,(bit_tobit(reg2 + 40)),1049276,1049572);
                error('unreachable');
            ::block_9_fin::
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 60)),0);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 56)),1049032);
            (__LONG_INT__(1,0)):store(mem_0,reg2+44);
            __MEMORY_WRITE_32__(mem_0,reg2+40,1051628);
            __FUNCS__.func_88((bit_tobit(reg2 + 24)),(bit_tobit(reg2 + 40)));
            error('unreachable');
        ::block_8_fin::
        __FUNCS__.func_170(32,8);
        error('unreachable');
    end
    function __FUNCS__.func_30(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg4;
        
            
                
                    if reg2==0 then goto if_11_fin end 
                        reg5 = __MEMORY_READ_32__(mem_0,reg0+4);
                        reg6 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,reg0);
                        reg7 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,reg0+8);
                        reg8 = reg5;
                        
                        while true do ::loop_21_start::
                            
                                reg5 = __MEMORY_READ_8__(mem_0,reg8);
                                if ((reg5 == 0) and 1 or 0)~=0 then goto block_22_fin; end;
                                reg5 = __MEMORY_READ_32__(mem_0,reg6+12);
                                reg5 = __TABLE_FUNCS_0__[reg5+1](reg7,1055352,4);
                                if ((reg5 == 0) and 1 or 0)~=0 then goto block_22_fin; end;
                                reg3 = 1; goto block_9_fin;
                            ::block_22_fin::
                            reg0 = 0;
                            reg5 = reg2;
                            
                                
                                while true do ::loop_43_start::
                                    reg9 = (bit_tobit(reg0 + reg1));
                                    
                                        if ((__UNSIGNED__(reg5) >= __UNSIGNED__(8)) and 1 or 0)==0 then goto if_52_fin end 
                                            __FUNCS__.func_45((bit_tobit(reg4 + 8)),10,reg9,reg5);
                                            reg10 = __MEMORY_READ_32__(mem_0,reg4+12);
                                            reg5 = reg10;
                                            reg10 = __MEMORY_READ_32__(mem_0,reg4+8);
                                            reg11 = reg10;
                                            goto block_48_fin;
                                        ::if_52_fin::
                                        if ((reg5 == 0) and 1 or 0)==0 then goto if_70_fin end 
                                            reg5 = 0;
                                            reg11 = 0;
                                            goto block_48_fin;
                                        ::if_70_fin::
                                        reg10 = 0;
                                        
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            reg11 = 0;
                                            if ((reg5 == 1) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 1;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+1);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            if ((reg5 == 2) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 2;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+2);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            if ((reg5 == 3) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 3;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+3);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            if ((reg5 == 4) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 4;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+4);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            if ((reg5 == 5) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 5;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+5);
                                            if ((reg12 == 10) and 1 or 0)~=0 then goto block_79_fin; end;
                                            if ((reg5 == 6) and 1 or 0)~=0 then goto block_48_fin; end;
                                            reg10 = 6;
                                            reg12 = __MEMORY_READ_8__(mem_0,reg9+6);
                                            if ((reg12 ~= 10) and 1 or 0)~=0 then goto block_48_fin; end;
                                        ::block_79_fin::
                                        reg11 = 1;
                                        reg5 = reg10;
                                    ::block_48_fin::
                                    reg10 = 0;
                                    if ((reg11 ~= 1) and 1 or 0)==0 then goto if_164_fin end 
                                        reg0 = reg2;
                                        goto block_42_fin;
                                    ::if_164_fin::
                                    
                                        reg9 = bit_tobit(reg0 + reg5);
                                        reg5 = reg9;
                                        reg0 = (bit_tobit(reg5 + 1));
                                        if (bit_bor(((__UNSIGNED__(reg0) < __UNSIGNED__(reg5)) and 1 or 0),((__UNSIGNED__(reg2) < __UNSIGNED__(reg0)) and 1 or 0)))~=0 then goto block_169_fin; end;
                                        reg9 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + reg5)));
                                        if ((reg9 ~= 10) and 1 or 0)~=0 then goto block_169_fin; end;
                                        reg10 = 1;
                                        goto block_42_fin;
                                    ::block_169_fin::
                                    reg5 = (bit_tobit(reg2 - reg0));
                                    if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg0)) and 1 or 0)~=0 then goto loop_43_start; end;
                                    break
                                end
                                
                                reg0 = reg2;
                            ::block_42_fin::
                            __MEMORY_WRITE_8__(mem_0,reg8,reg10);
                            
                                if ((__UNSIGNED__(reg2) <= __UNSIGNED__(reg0)) and 1 or 0)==0 then goto if_214_fin end 
                                    if ((reg0 ~= reg2) and 1 or 0)~=0 then goto block_8_fin; end;
                                    reg9 = __MEMORY_READ_32__(mem_0,reg6+12);
                                    reg9 = __TABLE_FUNCS_0__[reg9+1](reg7,reg1,reg0);
                                    if ((reg9 == 0) and 1 or 0)~=0 then goto block_210_fin; end;
                                    reg3 = 1; goto block_9_fin;
                                ::if_214_fin::
                                reg5 = (bit_tobit(reg0 + reg1));
                                reg9 = __MEMORY_READ_8__(mem_0,reg5);reg9=bit_arshift(bit_lshift(reg9,24),24);
                                if ((reg9 <= -65) and 1 or 0)~=0 then goto block_8_fin; end;
                                reg9 = __MEMORY_READ_32__(mem_0,reg6+12);
                                reg9 = __TABLE_FUNCS_0__[reg9+1](reg7,reg1,reg0);
                                if reg9~=0 then reg3 = 1; goto block_9_fin; end;
                                reg9 = __MEMORY_READ_8__(mem_0,reg5);reg9=bit_arshift(bit_lshift(reg9,24),24);
                                if ((reg9 <= -65) and 1 or 0)~=0 then goto block_7_fin; end;
                            ::block_210_fin::
                            reg9 = bit_tobit(reg0 + reg1);
                            reg1 = reg9;
                            reg9 = bit_tobit(reg2 - reg0);
                            reg2 = reg9;
                            if reg2~=0 then goto loop_21_start; end;
                            break
                        end
                        
                    ::if_11_fin::
                    reg3 = 0
                    -- BLOCK RET (block):
                ::block_9_fin::
                __GLOBALS__[0] = (bit_tobit(reg4 + 16));
                do return reg3 end
            ::block_8_fin::
            __FUNCS__.func_7(reg1,reg2,0,reg0,1055388);
            error('unreachable');
        ::block_7_fin::
        __FUNCS__.func_7(reg1,reg2,reg0,reg2,1055404);
        error('unreachable');
    end
    function __FUNCS__.func_31(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __FUNCS__.func_172(reg0,reg1);
        reg3 = reg2;
        
            
                
                    reg2 = __FUNCS__.func_167(reg0);
                    if reg2~=0 then goto block_8_fin; end;
                    reg2 = __MEMORY_READ_32__(mem_0,reg0);
                    reg4 = reg2;
                    
                        reg2 = __FUNCS__.func_156(reg0);
                        if ((reg2 == 0) and 1 or 0)==0 then goto if_19_fin end 
                            reg2 = bit_tobit(reg1 + reg4);
                            reg1 = reg2;
                            reg2 = __FUNCS__.func_173(reg0,reg4);
                            reg0 = reg2;
                            reg2 = __MEMORY_READ_32__(mem_0,1059604);
                            if ((reg0 ~= reg2) and 1 or 0)~=0 then goto block_15_fin; end;
                            reg2 = __MEMORY_READ_32__(mem_0,reg3+4);
                            if (((bit_band(reg2,3)) ~= 3) and 1 or 0)~=0 then goto block_8_fin; end;
                            __MEMORY_WRITE_32__(mem_0,1059596,reg1);
                            __FUNCS__.func_131(reg0,reg1,reg3);
                            do return  end
                        ::if_19_fin::
                        reg0 = (bit_tobit((bit_tobit(reg1 + reg4)) + 16));
                        goto block_7_fin;
                    ::block_15_fin::
                    if ((__UNSIGNED__(reg4) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_59_fin end 
                        __FUNCS__.func_54(reg0);
                        goto block_8_fin;
                    ::if_59_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                    reg5 = reg2;
                    reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                    reg6 = reg2;
                    if ((reg5 ~= reg6) and 1 or 0)==0 then goto if_75_fin end 
                        __MEMORY_WRITE_32__(mem_0,reg6+12,reg5);
                        __MEMORY_WRITE_32__(mem_0,reg5+8,reg6);
                        goto block_8_fin;
                    ::if_75_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,1059196);
                    __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg2,(bit_rol(-2,(bit_rshift(reg4,3)))))));
                ::block_8_fin::
                reg2 = __FUNCS__.func_151(reg3);
                if reg2==0 then goto if_97_fin end 
                    __FUNCS__.func_131(reg0,reg1,reg3);
                    goto block_6_fin;
                ::if_97_fin::
                
                    reg2 = __MEMORY_READ_32__(mem_0,1059608);
                    if ((reg2 ~= reg3) and 1 or 0)==0 then goto if_109_fin end 
                        reg2 = __MEMORY_READ_32__(mem_0,1059604);
                        if ((reg3 ~= reg2) and 1 or 0)~=0 then goto block_104_fin; end;
                        __MEMORY_WRITE_32__(mem_0,1059604,reg0);
                        reg2 = __MEMORY_READ_32__(mem_0,1059596);
                        reg6 = bit_tobit(reg2 + reg1);
                        reg1 = reg6;
                        __MEMORY_WRITE_32__(mem_0,1059596,reg1);
                        __FUNCS__.func_140(reg0,reg1);
                        do return  end
                    ::if_109_fin::
                    __MEMORY_WRITE_32__(mem_0,1059608,reg0);
                    reg2 = __MEMORY_READ_32__(mem_0,1059600);
                    reg6 = bit_tobit(reg2 + reg1);
                    reg1 = reg6;
                    __MEMORY_WRITE_32__(mem_0,1059600,reg1);
                    __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg1,1)));
                    reg2 = __MEMORY_READ_32__(mem_0,1059604);
                    if ((reg0 ~= reg2) and 1 or 0)~=0 then goto block_7_fin; end;
                    __MEMORY_WRITE_32__(mem_0,1059596,0);
                    __MEMORY_WRITE_32__(mem_0,1059604,0);
                    do return  end
                ::block_104_fin::
                reg2 = __FUNCS__.func_166(reg3);
                reg4 = reg2;
                reg2 = bit_tobit(reg4 + reg1);
                reg1 = reg2;
                
                    if ((__UNSIGNED__(reg4) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_168_fin end 
                        __FUNCS__.func_54(reg3);
                        goto block_164_fin;
                    ::if_168_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 12)));
                    reg5 = reg2;
                    reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 8)));
                    reg3 = reg2;
                    if ((reg5 ~= reg3) and 1 or 0)==0 then goto if_184_fin end 
                        __MEMORY_WRITE_32__(mem_0,reg3+12,reg5);
                        __MEMORY_WRITE_32__(mem_0,reg5+8,reg3);
                        goto block_164_fin;
                    ::if_184_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,1059196);
                    __MEMORY_WRITE_32__(mem_0,1059196,(bit_band(reg2,(bit_rol(-2,(bit_rshift(reg4,3)))))));
                ::block_164_fin::
                __FUNCS__.func_140(reg0,reg1);
                reg2 = __MEMORY_READ_32__(mem_0,1059604);
                if ((reg0 ~= reg2) and 1 or 0)~=0 then goto block_6_fin; end;
                __MEMORY_WRITE_32__(mem_0,1059596,reg1);
            ::block_7_fin::
            do return  end
        ::block_6_fin::
        if ((__UNSIGNED__(reg1) >= __UNSIGNED__(256)) and 1 or 0)==0 then goto if_221_fin end 
            __FUNCS__.func_52(reg0,reg1);
            do return  end
        ::if_221_fin::
        reg3 = (bit_rshift(reg1,3));
        reg1 = (bit_tobit((bit_lshift(reg3,3)) + 1059204));
        
            reg5 = __MEMORY_READ_32__(mem_0,1059196);
            reg4 = reg5;
            reg5 = bit_lshift(1,reg3);
            reg3 = reg5;
            if (bit_band(reg4,reg3))==0 then goto if_245_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,reg1+8);
                reg2 = reg5; goto block_236_fin;
            ::if_245_fin::
            __MEMORY_WRITE_32__(mem_0,1059196,(bit_bor(reg3,reg4)));
            reg2 = reg1
            -- BLOCK RET (block):
        ::block_236_fin::
        reg3 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg1+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+12,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg0+8,reg3);
    end
    function __FUNCS__.func_32(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg4;
        
            
                
                    reg3 = __MEMORY_READ_32__(mem_0,reg0);
                    reg0 = reg3;
                    reg3 = __MEMORY_READ_32__(mem_0,reg0);
                    if ((reg3 == 0) and 1 or 0)==0 then goto if_16_fin end 
                        __MEMORY_WRITE_32__(mem_0,reg0,-1);
                        __FUNCS__.func_26(reg4,reg1,reg2);
                        
                            
                                reg5 = __MEMORY_READ_32__(mem_0,reg4);
                                if ((reg5 == 0) and 1 or 0)==0 then goto if_29_fin end 
                                    
                                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                                        reg6 = reg5;
                                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                                        reg7 = reg5;
                                        if (bit_bor(((reg6 == 0) and 1 or 0),((reg7 == 0) and 1 or 0)))~=0 then goto block_30_fin; end;
                                        reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit((bit_tobit(reg6 + reg7)) + -1)));
                                        if ((reg5 ~= 10) and 1 or 0)~=0 then goto block_30_fin; end;
                                        reg6 = 0;
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),0);
                                        __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg0 + 16)),0);
                                    ::block_30_fin::
                                    reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                                    if ((__UNSIGNED__((bit_tobit(reg5 - reg6))) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_25_fin; end;
                                    reg5 = __FUNCS__.func_78((bit_tobit(reg0 + 4)),reg1,reg2);
                                    reg8 = reg5;
                                    reg5 = ((reg8):_and(__LONG_INT__(255,0)));
                                    reg3 = ((reg8):_and(__LONG_INT__(-256,-1))); goto block_24_fin;
                                ::if_29_fin::
                                reg8 = __MEMORY_READ_32__(mem_0,reg4+4);
                                reg6 = (bit_tobit(reg8 + 1));
                                if ((__UNSIGNED__(reg6) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_10_fin; end;
                                reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                                reg7 = reg8;
                                if ((reg7 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                
                                    reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                                    if ((__UNSIGNED__((bit_tobit(reg8 - reg7))) > __UNSIGNED__(reg6)) and 1 or 0)==0 then goto if_115_fin end 
                                        reg8 = __MEMORY_READ_32__(mem_0,reg0+4);
                                        reg9 = __FUNCS__.func_64((bit_tobit(reg8 + reg7)),reg1,reg6);
                                        reg8 = bit_tobit(reg6 + reg7);
                                        reg7 = reg8;
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),reg7);
                                        goto block_106_fin;
                                    ::if_115_fin::
                                    reg8 = __FUNCS__.func_78((bit_tobit(reg0 + 4)),reg1,reg6);
                                    reg5 = reg8;
                                    if ((((reg5):_and(__LONG_INT__(255,0))) ~= __LONG_INT__(4,0)) and 1 or 0)~=0 then goto block_8_fin; end;
                                    reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 12)));
                                    reg7 = reg8;
                                ::block_106_fin::
                                if ((reg7 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),0);
                                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg0 + 16)),0);
                                goto block_9_fin;
                            ::block_25_fin::
                            reg8 = __FUNCS__.func_64((bit_tobit(reg6 + reg7)),reg1,reg2);
                            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),(bit_tobit(reg2 + reg6)));
                            reg5 = __LONG_INT__(4,0);
                            reg3 = __LONG_INT__(0,0)
                            -- BLOCK RET (block):
                        ::block_24_fin::
                        reg8 = (reg3):_or(reg5);
                        reg5 = reg8;
                        goto block_8_fin;
                    ::if_16_fin::
                    __FUNCS__.func_79(1049032,16,(bit_tobit(reg4 + 8)),1049260,1050416);
                    error('unreachable');
                ::block_10_fin::
                __FUNCS__.func_110(1049088,35,1049200);
                error('unreachable');
            ::block_9_fin::
            reg7 = (bit_tobit(reg1 + reg6));
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
            reg1 = (bit_tobit(reg2 - reg6));
            if ((__UNSIGNED__(reg3) <= __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_219_fin end 
                reg2 = __FUNCS__.func_78((bit_tobit(reg0 + 4)),reg7,reg1);
                reg5 = reg2;
                reg2 = (((reg5):_and(__LONG_INT__(255,0)))):_or(((reg5):_and(__LONG_INT__(-256,-1))));
                reg5 = reg2;
                goto block_8_fin;
            ::if_219_fin::
            reg2 = __MEMORY_READ_32__(mem_0,reg0+4);
            reg3 = __FUNCS__.func_64(reg2,reg7,reg1);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 12)),reg1);
            reg5 = __LONG_INT__(4,0);
        ::block_8_fin::
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0,(bit_tobit(reg1 + 1)));
        __GLOBALS__[0] = (bit_tobit(reg4 + 16));
        do return reg5; end;
    end
    function __FUNCS__.func_33(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        
            
                
                    
                        
                            reg4 = __MEMORY_READ_32__(mem_0,reg1);
                            reg5 = reg4;
                            if (((bit_band(reg5,16)) == 0) and 1 or 0)==0 then goto if_22_fin end 
                                if (bit_band(reg5,32))~=0 then goto block_15_fin; end;
                                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg0);
                                reg6 = __FUNCS__.func_46(reg4,1,reg1);
                                reg2 = reg6; goto block_12_fin;
                            ::if_22_fin::
                            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg0);
                            reg6 = reg4;
                            reg0 = 128;
                            reg5 = (bit_tobit(reg3 + 128));
                            
                            while true do ::loop_43_start::
                                if ((reg0 == 0) and 1 or 0)==0 then goto if_46_fin end 
                                    reg0 = 0;
                                    goto block_13_fin;
                                ::if_46_fin::
                                reg4 = (bit_band(((reg6)[1]),15));
                                
                                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg5 + -1)),(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg4)));
                                if ((reg6):_le_u(__LONG_INT__(15,0)) and 1 or 0)==0 then goto if_70_fin end 
                                    reg7 = bit_tobit(reg0 + -1);
                                    reg0 = reg7;
                                    goto block_14_fin;
                                ::if_70_fin::
                                reg7 = bit_tobit(reg5 + -2);
                                reg5 = reg7;
                                reg4 = (bit_band(((((reg6):_shr_u(__LONG_INT__(4,0))))[1]),15));
                                
                                __MEMORY_WRITE_8__(mem_0,reg5,(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg4)));
                                reg7 = bit_tobit(reg0 + -2);
                                reg0 = reg7;
                                reg7 = (reg6):_shr_u(__LONG_INT__(8,0));
                                reg8 = (reg6):_lt_u(__LONG_INT__(256,0)) and 1 or 0;
                                reg6 = reg7;
                                if ((reg8 == 0) and 1 or 0)~=0 then goto loop_43_start; end;
                                break
                            end
                            
                            goto block_14_fin;
                        ::block_15_fin::
                        reg7 = __LONG_INT__(0,0); reg7:load(mem_0,reg0);
                        reg6 = reg7;
                        reg0 = 128;
                        reg5 = (bit_tobit(reg3 + 128));
                        
                            
                                
                                while true do ::loop_123_start::
                                    if ((reg0 == 0) and 1 or 0)==0 then goto if_126_fin end 
                                        reg0 = 0;
                                        goto block_122_fin;
                                    ::if_126_fin::
                                    reg4 = (bit_band(((reg6)[1]),15));
                                    
                                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg5 + -1)),(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 55 or 48) + reg4)));
                                    
                                        if ((reg6):_le_u(__LONG_INT__(15,0)) and 1 or 0)==0 then goto if_151_fin end 
                                            reg7 = bit_tobit(reg0 + -1);
                                            reg0 = reg7;
                                            goto block_147_fin;
                                        ::if_151_fin::
                                        reg7 = bit_tobit(reg5 + -2);
                                        reg5 = reg7;
                                        reg4 = (bit_band(((((reg6):_shr_u(__LONG_INT__(4,0))))[1]),15));
                                        
                                        __MEMORY_WRITE_8__(mem_0,reg5,(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 55 or 48) + reg4)));
                                        reg7 = bit_tobit(reg0 + -2);
                                        reg0 = reg7;
                                        reg7 = (reg6):_shr_u(__LONG_INT__(8,0));
                                        reg8 = (reg6):_lt_u(__LONG_INT__(256,0)) and 1 or 0;
                                        reg6 = reg7;
                                        if ((reg8 == 0) and 1 or 0)~=0 then goto loop_123_start; end;
                                    ::block_147_fin::
                                    break
                                end
                                
                                if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)~=0 then goto block_121_fin; end;
                            ::block_122_fin::
                            reg7 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit(reg0 + reg3)),(bit_tobit(128 - reg0)));
                            reg2 = reg7; goto block_12_fin;
                        ::block_121_fin::
                        __FUNCS__.func_83(reg0,128,1055476);
                        error('unreachable');
                    ::block_14_fin::
                    if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)~=0 then goto block_11_fin; end;
                ::block_13_fin::
                reg7 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit(reg0 + reg3)),(bit_tobit(128 - reg0)));
                reg2 = reg7
                -- BLOCK RET (block):
            ::block_12_fin::
            __GLOBALS__[0] = (bit_tobit(reg3 + 128));
            do return reg2 end
        ::block_11_fin::
        __FUNCS__.func_83(reg0,128,1055476);
        error('unreachable');
    end
    function __FUNCS__.func_34(reg0, reg1, reg2, reg3, reg4, reg5, reg6, reg7, reg8)
        local reg9,reg10;
        
            
                
                    
                        
                            
                                
                                    if ((reg7):_gt_u(reg8) and 1 or 0)==0 then goto if_12_fin end 
                                        if (((reg7 - reg8)):_le_u(reg8) and 1 or 0)~=0 then goto block_3_fin; end;
                                        
                                        if (((((reg7 - ((reg6):_shl(__LONG_INT__(1,0))))):_ge_u(((reg8):_shl(__LONG_INT__(1,0)))) and 1 or 0) == 0) and 0 or (((reg7 - reg6)):_gt_u(reg6) and 1 or 0))~=0 then goto block_8_fin; end;
                                        if ((reg6):_gt_u(reg8) and 1 or 0)==0 then goto if_39_fin end 
                                            reg9 = reg6 - reg8;
                                            reg6 = reg9;
                                            if (((reg7 - reg6)):_le_u(reg6) and 1 or 0)~=0 then goto block_7_fin; end;
                                        ::if_39_fin::
                                        goto block_3_fin;
                                    ::if_12_fin::
                                    goto block_3_fin;
                                ::block_8_fin::
                                if ((__UNSIGNED__(reg3) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_6_fin; end;
                                goto block_2_fin;
                            ::block_7_fin::
                            if ((__UNSIGNED__(reg3) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_5_fin; end;
                            reg6 = reg1;
                            
                                -- FORCE INIT VAR | i32
                                reg7 = 0;
                                -- FORCE INIT VAR | i32
                                reg7 = 0;
                                
                                while true do ::loop_70_start::
                                    if ((reg3 == reg7) and 1 or 0)~=0 then goto block_69_fin; end;
                                    reg8 = bit_tobit(reg7 + 1);
                                    reg7 = reg8;
                                    reg8 = (bit_tobit(reg6 + -1));
                                    reg9 = bit_tobit(reg3 + reg6);
                                    reg6 = reg8;
                                    reg10 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg9 + -1)));
                                    if ((reg10 == 57) and 1 or 0)~=0 then goto loop_70_start; end;
                                    break
                                end
                                
                                reg5 = (bit_tobit(reg3 + reg8));
                                reg8 = __MEMORY_READ_8__(mem_0,reg5);
                                __MEMORY_WRITE_8__(mem_0,reg5,(bit_tobit(reg8 + 1)));
                                if ((__UNSIGNED__((bit_tobit((bit_tobit(reg3 - reg7)) + 1))) >= __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_4_fin; end;
                                reg8 = __FUNCS__.func_65((bit_tobit(reg5 + 1)),48,(bit_tobit(reg7 + -1)));
                                goto block_4_fin;
                            ::block_69_fin::
                            
                                if ((reg3 == 0) and 1 or 0)~=0 then reg7 = 49; goto block_122_fin; end;
                                __MEMORY_WRITE_8__(mem_0,reg1,49);
                                if ((reg3 == 1) and 1 or 0)~=0 then reg7 = 48; goto block_122_fin; end;
                                reg8 = __FUNCS__.func_65((bit_tobit(reg1 + 1)),48,(bit_tobit(reg3 + -1)));
                                reg7 = 48
                                -- BLOCK RET (block):
                            ::block_122_fin::
                            reg8 = bit_arshift((bit_tobit((bit_lshift(reg4,16)) + 65536)),16);
                            reg4 = reg8;
                            if (bit_bor(((reg4 <= (bit_arshift((bit_lshift(reg5,16)),16))) and 1 or 0),((__UNSIGNED__(reg3) >= __UNSIGNED__(reg2)) and 1 or 0)))~=0 then goto block_4_fin; end;
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + reg3)),reg7);
                            reg5 = bit_tobit(reg3 + 1);
                            reg3 = reg5;
                            goto block_4_fin;
                        ::block_6_fin::
                        __FUNCS__.func_84(reg3,reg2,1054708);
                        error('unreachable');
                    ::block_5_fin::
                    __FUNCS__.func_84(reg3,reg2,1054724);
                    error('unreachable');
                ::block_4_fin::
                if ((__UNSIGNED__(reg3) <= __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_189_fin end 
                    goto block_2_fin;
                ::if_189_fin::
                __FUNCS__.func_84(reg3,reg2,1054740);
                error('unreachable');
            ::block_3_fin::
            __MEMORY_WRITE_32__(mem_0,reg0,0);
            do return  end
        ::block_2_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+4,reg3);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
        __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg0 + 8)),reg4);
    end
    function __FUNCS__.func_35(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7;
        reg2 = 1;
        
            reg3 = __MEMORY_READ_32__(mem_0,reg1+24);
            reg4 = reg3;
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
            reg5 = __MEMORY_READ_32__(mem_0,reg3+16);
            reg3 = reg5;
            reg5 = __TABLE_FUNCS_0__[reg3+1](reg4,39);
            if reg5~=0 then goto block_5_fin; end;
            reg5 = 116;
            reg1 = 2;
            
                
                    
                        
                            
                                
                                    
                                        
                                            
                                                reg7 = __MEMORY_READ_32__(mem_0,reg0);
                                                reg0 = reg7;
                                                
                                                if (bit_tobit(reg0 + -9)) == 0 then goto block_22_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 1 then goto block_27_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 2 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 3 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 4 then goto block_28_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 5 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 6 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 7 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 8 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 9 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 10 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 11 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 12 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 13 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 14 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 15 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 16 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 17 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 18 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 19 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 20 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 21 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 22 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 23 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 24 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 25 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 26 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 27 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 28 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 29 then goto block_29_fin;
                                                elseif (bit_tobit(reg0 + -9)) == 30 then goto block_26_fin;
                                                else goto block_30_fin;
                                                end
                                            ::block_30_fin::
                                            if ((reg0 == 92) and 1 or 0)~=0 then goto block_26_fin; end;
                                        ::block_29_fin::
                                        reg7 = __FUNCS__.func_43(reg0);
                                        if reg7~=0 then goto block_25_fin; end;
                                        reg7 = __FUNCS__.func_22(reg0);
                                        if ((reg7 == 0) and 1 or 0)~=0 then goto block_24_fin; end;
                                        reg1 = 1;
                                        reg5 = reg0;
                                        goto block_22_fin;
                                    ::block_28_fin::
                                    reg5 = 114;
                                    goto block_22_fin;
                                ::block_27_fin::
                                reg5 = 110;
                                goto block_22_fin;
                            ::block_26_fin::
                            reg5 = reg0;
                            goto block_22_fin;
                        ::block_25_fin::
                        reg6 = (((__LONG_INT__((bit_bxor((bit_rshift((__CLZ__((bit_bor(reg0,1)))),2)),7)),0))):_or(__LONG_INT__(0,5))); goto block_23_fin;
                    ::block_24_fin::
                    reg6 = (((__LONG_INT__((bit_bxor((bit_rshift((__CLZ__((bit_bor(reg0,1)))),2)),7)),0))):_or(__LONG_INT__(0,5)))
                    -- BLOCK RET (block):
                ::block_23_fin::
                reg7 = reg6;
                reg1 = 3;
                reg5 = reg0;
            ::block_22_fin::
            
            while true do ::loop_99_start::
                reg6 = reg1;
                reg1 = 0;
                reg0 = reg5;
                
                    
                        
                            
                                
                                    
                                    if (bit_tobit(reg6 - 1)) == 0 then goto block_106_fin;
                                    elseif (bit_tobit(reg6 - 1)) == 1 then goto block_108_fin;
                                    elseif (bit_tobit(reg6 - 1)) == 2 then goto block_110_fin;
                                    else goto block_109_fin;
                                    end
                                ::block_110_fin::
                                
                                    
                                        
                                            
                                                
                                                    
                                                    if (bit_tobit((bit_band(((((reg7):_shr_u(__LONG_INT__(32,0))))[1]),255)) - 1)) == 0 then goto block_120_fin;
                                                    elseif (bit_tobit((bit_band(((((reg7):_shr_u(__LONG_INT__(32,0))))[1]),255)) - 1)) == 1 then goto block_116_fin;
                                                    elseif (bit_tobit((bit_band(((((reg7):_shr_u(__LONG_INT__(32,0))))[1]),255)) - 1)) == 2 then goto block_119_fin;
                                                    elseif (bit_tobit((bit_band(((((reg7):_shr_u(__LONG_INT__(32,0))))[1]),255)) - 1)) == 3 then goto block_118_fin;
                                                    elseif (bit_tobit((bit_band(((((reg7):_shr_u(__LONG_INT__(32,0))))[1]),255)) - 1)) == 4 then goto block_117_fin;
                                                    else goto block_109_fin;
                                                    end
                                                ::block_120_fin::
                                                reg6 = (reg7):_and(__LONG_INT__(-1,-256));
                                                reg7 = reg6;
                                                reg0 = 125;
                                                reg1 = 3;
                                                goto block_106_fin;
                                            ::block_119_fin::
                                            reg6 = (((reg7):_and(__LONG_INT__(-1,-256)))):_or(__LONG_INT__(0,2));
                                            reg7 = reg6;
                                            reg0 = 123;
                                            reg1 = 3;
                                            goto block_106_fin;
                                        ::block_118_fin::
                                        reg6 = (((reg7):_and(__LONG_INT__(-1,-256)))):_or(__LONG_INT__(0,3));
                                        reg7 = reg6;
                                        reg0 = 117;
                                        reg1 = 3;
                                        goto block_106_fin;
                                    ::block_117_fin::
                                    reg6 = (((reg7):_and(__LONG_INT__(-1,-256)))):_or(__LONG_INT__(0,4));
                                    reg7 = reg6;
                                    reg0 = 92;
                                    reg1 = 3;
                                    goto block_106_fin;
                                ::block_116_fin::
                                reg1 = ((reg7)[1]);
                                reg0 = (bit_band((bit_rshift(reg5,(bit_lshift(reg1,2)))),15));
                                
                                reg6 = bit_tobit(((((__UNSIGNED__(reg0) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg0);
                                reg0 = reg6;
                                if ((reg1 == 0) and 1 or 0)~=0 then goto block_107_fin; end;
                                reg6 = ((((reg7 + __LONG_INT__(-1,-1))):_and(__LONG_INT__(-1,0)))):_or(((reg7):_and(__LONG_INT__(0,-1))));
                                reg7 = reg6;
                                reg1 = 3;
                                goto block_106_fin;
                            ::block_109_fin::
                            reg6 = __TABLE_FUNCS_0__[reg3+1](reg4,39);
                            reg2 = reg6;
                            goto block_5_fin;
                        ::block_108_fin::
                        reg0 = 92;
                        reg1 = 1;
                        goto block_106_fin;
                    ::block_107_fin::
                    reg6 = (((reg7):_and(__LONG_INT__(-1,-256)))):_or(__LONG_INT__(0,1));
                    reg7 = reg6;
                    reg1 = 3;
                ::block_106_fin::
                reg6 = __TABLE_FUNCS_0__[reg3+1](reg4,reg0);
                if ((reg6 == 0) and 1 or 0)~=0 then goto loop_99_start; end;
                break
            end
            
        ::block_5_fin::
        do return reg2; end;
    end
    function __FUNCS__.func_36()
        local reg0,reg1,reg2,reg3,reg4,reg5,reg6;
        reg0 = __GLOBALS__[0];
        reg1 = (bit_tobit(reg0 - 32));
        __GLOBALS__[0] = reg1;
        reg0 = __MEMORY_READ_32__(mem_0,1059184);
        if ((reg0 ~= 1) and 1 or 0)==0 then goto if_11_fin end 
            (__LONG_INT__(1,0)):store(mem_0,1059184);
            __MEMORY_WRITE_32__(mem_0,1059192,0);
        ::if_11_fin::
        reg0 = __FUNCS__.func_60();
        reg2 = reg0;
        reg0 = __MEMORY_READ_32__(mem_0,reg2+24);
        reg3 = reg0;
        reg0 = (reg3 == 2) and 1 or 0;
        reg4 = reg3;
        reg3 = reg0;
        
        __MEMORY_WRITE_32__(mem_0,reg2+24,((reg3 == 0) and reg4 or 0));
        
            
                
                    
                        
                            if ((reg3 == 0) and 1 or 0)==0 then goto if_38_fin end 
                                reg3 = (bit_tobit(reg2 + 24));
                                reg0 = __MEMORY_READ_8__(mem_0,reg3+4);
                                reg4 = reg0;
                                __MEMORY_WRITE_8__(mem_0,reg3+4,1);
                                reg0 = bit_band(reg4,1);
                                reg4 = reg0;
                                __MEMORY_WRITE_8__(mem_0,reg1+4,reg4);
                                if reg4~=0 then goto block_35_fin; end;
                                reg4 = 0;
                                reg0 = __MEMORY_READ_32__(mem_0,1059144);
                                if (bit_band(reg0,2147483647))==0 then goto if_62_fin end 
                                    reg0 = __FUNCS__.func_134();
                                    reg4 = (bit_bxor(reg0,1));
                                ::if_62_fin::
                                reg0 = (bit_tobit(reg3 + 4));
                                reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg3 + 5)));
                                if reg5~=0 then goto block_34_fin; end;
                                reg5 = __MEMORY_READ_32__(mem_0,reg3);
                                reg6 = reg5;
                                
                                __MEMORY_WRITE_32__(mem_0,reg3,((reg6 == 0) and 1 or reg6));
                                if ((reg6 == 0) and 1 or 0)~=0 then goto block_31_fin; end;
                                if ((reg6 ~= 2) and 1 or 0)~=0 then goto block_33_fin; end;
                                reg5 = __MEMORY_READ_32__(mem_0,reg3);
                                reg6 = reg5;
                                __MEMORY_WRITE_32__(mem_0,reg3,0);
                                __MEMORY_WRITE_32__(mem_0,reg1+4,reg6);
                                if ((reg6 ~= 2) and 1 or 0)~=0 then goto block_32_fin; end;
                                
                                    if reg4~=0 then goto block_105_fin; end;
                                    reg5 = __MEMORY_READ_32__(mem_0,1059144);
                                    if (((bit_band(reg5,2147483647)) == 0) and 1 or 0)~=0 then goto block_105_fin; end;
                                    reg5 = __FUNCS__.func_134();
                                    if reg5~=0 then goto block_105_fin; end;
                                    __MEMORY_WRITE_8__(mem_0,reg3+5,1);
                                ::block_105_fin::
                                __MEMORY_WRITE_8__(mem_0,reg0,0);
                            ::if_38_fin::
                            reg5 = __MEMORY_READ_32__(mem_0,reg2);
                            reg3 = reg5;
                            __MEMORY_WRITE_32__(mem_0,reg2,(bit_tobit(reg3 + -1)));
                            if ((reg3 == 1) and 1 or 0)==0 then goto if_134_fin end 
                                __FUNCS__.func_100(reg2);
                            ::if_134_fin::
                            __GLOBALS__[0] = (bit_tobit(reg1 + 32));
                            do return  end
                        ::block_35_fin::
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 28)),0);
                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 24)),1049032);
                        (__LONG_INT__(1,0)):store(mem_0,reg1+12);
                        __MEMORY_WRITE_32__(mem_0,reg1+8,1051628);
                        __FUNCS__.func_88((bit_tobit(reg1 + 4)),(bit_tobit(reg1 + 8)));
                        error('unreachable');
                    ::block_34_fin::
                    __MEMORY_WRITE_8__(mem_0,reg1+12,reg4);
                    __MEMORY_WRITE_32__(mem_0,reg1+8,reg0);
                    __FUNCS__.func_79(1049308,43,(bit_tobit(reg1 + 8)),1049352,1051212);
                    error('unreachable');
                ::block_33_fin::
                __FUNCS__.func_126(1051228,23,1051252);
                error('unreachable');
            ::block_32_fin::
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 28)),0);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 24)),1049032);
            (__LONG_INT__(1,0)):store(mem_0,reg1+12);
            __MEMORY_WRITE_32__(mem_0,reg1+8,1051300);
            __FUNCS__.func_89((bit_tobit(reg1 + 4)),(bit_tobit(reg1 + 8)),1051308);
            error('unreachable');
        ::block_31_fin::
        __FUNCS__.func_126(1051504,26,1051580);
        error('unreachable');
    end
    function __FUNCS__.func_37(reg0, reg1, reg2, reg3, reg4)
        local reg5,reg6,reg7,reg8,reg9,reg10,reg11,reg12,reg13;
        reg5 = __GLOBALS__[0];
        reg6 = (bit_tobit(reg5 - 16));
        __GLOBALS__[0] = reg6;
        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
        reg7 = reg5;
        reg5 = __MEMORY_READ_32__(mem_0,reg0);
        reg8 = reg5;
        reg5 = ((reg1)[1]);
        reg1 = (bit_band(reg8,reg5));
        reg9 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + reg1)));
        reg10 = (bit_band(reg9,-2139062144));
        if ((reg10 == 0) and 1 or 0)==0 then goto if_26_fin end 
            reg9 = 4;
            
            while true do ::loop_29_start::
                reg10 = (bit_tobit(reg9 + reg1));
                reg11 = bit_tobit(reg9 + 4);
                reg9 = reg11;
                reg1 = (bit_band(reg10,reg8));
                reg11 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + reg1)));
                reg10 = (bit_band(reg11,-2139062144));
                if ((reg10 == 0) and 1 or 0)~=0 then goto loop_29_start; end;
                break
            end
            
        ::if_26_fin::
        
            reg11 = __MEMORY_READ_32__(mem_0,reg0+8);
            reg9 = (bit_band((bit_tobit((bit_rshift((__CTZ__(reg10)),3)) + reg1)),reg8));
            reg12 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg7 + reg9)));reg12=bit_arshift(bit_lshift(reg12,24),24);
            reg10 = reg12;
            if ((reg10 > -1) and 1 or 0)==0 then goto if_70_else end 
                reg13 = __MEMORY_READ_32__(mem_0,reg7);
                reg9 = (bit_rshift((__CTZ__((bit_band(reg13,-2139062144)))),3));
                reg13 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg7 + reg9)));
                reg12 = reg13
            goto if_70_fin
            ::if_70_else::
                reg12 = reg10
                -- BLOCK RET (if):
            ::if_70_fin::
            reg1 = (bit_band(reg12,1));
            if (bit_bor(reg11,((reg1 == 0) and 1 or 0)))~=0 then goto block_52_fin; end;
            __FUNCS__.func_3(reg6,reg0,1,reg4);
            reg11 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            reg7 = reg11;
            reg11 = __MEMORY_READ_32__(mem_0,reg0);
            reg8 = reg11;
            reg10 = (bit_band(reg8,reg5));
            reg11 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + reg10)));
            reg4 = (bit_band(reg11,-2139062144));
            if ((reg4 == 0) and 1 or 0)==0 then goto if_112_fin end 
                reg9 = 4;
                
                while true do ::loop_115_start::
                    reg4 = (bit_tobit(reg9 + reg10));
                    reg11 = bit_tobit(reg9 + 4);
                    reg9 = reg11;
                    reg10 = (bit_band(reg4,reg8));
                    reg11 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + reg10)));
                    reg4 = (bit_band(reg11,-2139062144));
                    if ((reg4 == 0) and 1 or 0)~=0 then goto loop_115_start; end;
                    break
                end
                
            ::if_112_fin::
            reg9 = (bit_band((bit_tobit((bit_rshift((__CTZ__(reg4)),3)) + reg10)),reg8));
            reg10 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg7 + reg9)));reg10=bit_arshift(bit_lshift(reg10,24),24);
            if ((reg10 <= -1) and 1 or 0)~=0 then goto block_52_fin; end;
            reg10 = __MEMORY_READ_32__(mem_0,reg7);
            reg9 = (bit_rshift((__CTZ__((bit_band(reg10,-2139062144)))),3));
        ::block_52_fin::
        reg4 = (bit_rshift(reg5,25));
        __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg9 + reg7)),reg4);
        __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit((bit_band((bit_tobit(reg9 + -4)),reg8)) + reg7)) + 4)),reg4);
        reg4 = __MEMORY_READ_32__(mem_0,reg0+8);
        __MEMORY_WRITE_32__(mem_0,reg0+8,(bit_tobit(reg4 - reg1)));
        reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
        __MEMORY_WRITE_32__(mem_0,reg0+12,(bit_tobit(reg1 + 1)));
        reg0 = (bit_tobit(reg7 - (bit_lshift(reg9,3))));
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + -8)),reg2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + -4)),reg3);
        __GLOBALS__[0] = (bit_tobit(reg6 + 16));
    end
    function __FUNCS__.func_38(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7;
        
            
                
                    
                        if ((__UNSIGNED__(reg1) >= __UNSIGNED__(9)) and 1 or 0)==0 then goto if_9_fin end 
                            reg2 = __FUNCS__.func_143(16,8);
                            if ((__UNSIGNED__(reg2) > __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_5_fin; end;
                            goto block_4_fin;
                        ::if_9_fin::
                        reg2 = __FUNCS__.func_2(reg0);
                        reg3 = reg2;
                        goto block_3_fin;
                    ::block_5_fin::
                    reg2 = __FUNCS__.func_143(16,8);
                    reg1 = reg2;
                ::block_4_fin::
                reg2 = __FUNCS__.func_174(0);
                reg4 = reg2;
                reg2 = __FUNCS__.func_143(reg4,8);
                reg5 = __FUNCS__.func_143(20,8);
                reg6 = __FUNCS__.func_143(16,8);
                reg7 = bit_tobit((bit_band((bit_tobit((bit_tobit(reg4 - (bit_tobit((bit_tobit(reg2 + reg5)) + reg6)))) + -65544)),-9)) + -3);
                reg4 = reg7;
                reg2 = __FUNCS__.func_143(16,8);
                reg5 = (bit_tobit(0 - (bit_lshift(reg2,2))));
                
                if ((__UNSIGNED__((bit_tobit(((((__UNSIGNED__(reg5) > __UNSIGNED__(reg4)) and 1 or 0) == 0) and reg5 or reg4) - reg1))) <= __UNSIGNED__(reg0)) and 1 or 0)~=0 then goto block_3_fin; end;
                reg2 = __FUNCS__.func_143(16,8);
                
                reg6 = __FUNCS__.func_143(((((__UNSIGNED__((bit_tobit(reg2 + -5))) > __UNSIGNED__(reg0)) and 1 or 0) == 0) and (bit_tobit(reg0 + 4)) or 16),8);
                reg4 = reg6;
                reg2 = __FUNCS__.func_143(16,8);
                reg6 = __FUNCS__.func_2((bit_tobit((bit_tobit((bit_tobit(reg1 + reg4)) + reg2)) + -4)));
                reg5 = reg6;
                if ((reg5 == 0) and 1 or 0)~=0 then goto block_3_fin; end;
                reg2 = __FUNCS__.func_175(reg5);
                reg0 = reg2;
                
                    reg3 = (bit_tobit(reg1 + -1));
                    if (((bit_band(reg3,reg5)) == 0) and 1 or 0)==0 then goto if_105_fin end 
                        reg1 = reg0;
                        goto block_97_fin;
                    ::if_105_fin::
                    reg2 = __FUNCS__.func_175((bit_band((bit_tobit(reg5 + reg3)),(bit_tobit(0 - reg1)))));
                    reg5 = reg2;
                    reg2 = __FUNCS__.func_143(16,8);
                    reg3 = reg2;
                    reg2 = __FUNCS__.func_166(reg0);
                    
                    reg6 = bit_tobit(reg5 + ((((__UNSIGNED__((bit_tobit(reg5 - reg0))) > __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg1 or 0));
                    reg1 = reg6;
                    reg5 = (bit_tobit(reg1 - reg0));
                    reg3 = (bit_tobit(reg2 - reg5));
                    reg2 = __FUNCS__.func_156(reg0);
                    if ((reg2 == 0) and 1 or 0)==0 then goto if_144_fin end 
                        __FUNCS__.func_121(reg1,reg3);
                        __FUNCS__.func_121(reg0,reg5);
                        __FUNCS__.func_31(reg0,reg5);
                        goto block_97_fin;
                    ::if_144_fin::
                    reg2 = __MEMORY_READ_32__(mem_0,reg0);
                    reg0 = reg2;
                    __MEMORY_WRITE_32__(mem_0,reg1+4,reg3);
                    __MEMORY_WRITE_32__(mem_0,reg1,(bit_tobit(reg0 + reg5)));
                ::block_97_fin::
                reg2 = __FUNCS__.func_156(reg1);
                if reg2~=0 then goto block_2_fin; end;
                reg2 = __FUNCS__.func_166(reg1);
                reg5 = reg2;
                reg2 = __FUNCS__.func_143(16,8);
                if ((__UNSIGNED__(reg5) <= __UNSIGNED__((bit_tobit(reg2 + reg4)))) and 1 or 0)~=0 then goto block_2_fin; end;
                reg2 = __FUNCS__.func_172(reg1,reg4);
                reg0 = reg2;
                __FUNCS__.func_121(reg1,reg4);
                reg2 = bit_tobit(reg5 - reg4);
                reg4 = reg2;
                __FUNCS__.func_121(reg0,reg4);
                __FUNCS__.func_31(reg0,reg4);
                goto block_2_fin;
            ::block_3_fin::
            do return reg3 end
        ::block_2_fin::
        reg0 = __FUNCS__.func_174(reg1);
        reg2 = __FUNCS__.func_156(reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_39(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7;
        
            if ((__UNSIGNED__((bit_tobit(reg0 - reg1))) < __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_8_fin end 
                reg3 = (bit_band(reg2,3));
                if reg3==0 then goto if_16_fin end 
                    reg4 = (bit_tobit(reg1 + -1));
                    reg5 = (bit_tobit(reg0 + -1));
                    
                    while true do ::loop_25_start::
                        reg6 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg2 + reg4)));
                        __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg5)),reg6);
                        reg6 = bit_tobit(reg2 + -1);
                        reg7 = bit_tobit(reg2 + -1);
                        reg2 = reg6;
                        reg6 = bit_tobit(reg3 + -1);
                        reg3 = reg6;
                        if reg3~=0 then goto loop_25_start; end;
                        break
                    end
                    
                ::if_16_fin::
                if ((__UNSIGNED__(reg7) < __UNSIGNED__(3)) and 1 or 0)~=0 then goto block_2_fin; end;
                reg3 = (bit_tobit(reg1 + -4));
                reg6 = (bit_tobit(reg0 + -4));
                
                while true do ::loop_56_start::
                    reg0 = (bit_tobit(reg2 + reg6));
                    reg1 = (bit_tobit(reg2 + reg3));
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 3)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg0 + 3)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 2)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg0 + 2)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg1 + 1)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg0 + 1)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,reg1);
                    __MEMORY_WRITE_8__(mem_0,reg0,reg7);
                    reg7 = bit_tobit(reg2 + -4);
                    reg2 = reg7;
                    if reg2~=0 then goto loop_56_start; end;
                    break
                end
                
                goto block_2_fin;
            ::if_8_fin::
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg6 = (bit_band(reg2,3));
            if ((__UNSIGNED__((bit_tobit(reg2 + -1))) >= __UNSIGNED__(3)) and 1 or 0)==0 then goto if_111_fin end 
                reg5 = (bit_band(reg2,-4));
                
                while true do ::loop_116_start::
                    reg2 = (bit_tobit(reg0 + reg3));
                    reg4 = (bit_tobit(reg1 + reg3));
                    reg7 = __MEMORY_READ_8__(mem_0,reg4);
                    __MEMORY_WRITE_8__(mem_0,reg2,reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 1)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 1)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 2)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 2)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 3)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 3)),reg7);
                    reg4 = bit_tobit(reg3 + 4);
                    reg3 = reg4;
                    if ((reg5 ~= reg3) and 1 or 0)~=0 then goto loop_116_start; end;
                    break
                end
                
            ::if_111_fin::
            if ((reg6 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg2 = (bit_tobit(reg1 + reg3));
            reg1 = bit_tobit(reg0 + reg3);
            reg3 = reg1;
            
            while true do ::loop_171_start::
                reg0 = __MEMORY_READ_8__(mem_0,reg2);
                __MEMORY_WRITE_8__(mem_0,reg3,reg0);
                reg0 = bit_tobit(reg2 + 1);
                reg2 = reg0;
                reg0 = bit_tobit(reg3 + 1);
                reg3 = reg0;
                reg0 = bit_tobit(reg6 + -1);
                reg6 = reg0;
                if reg6~=0 then goto loop_171_start; end;
                break
            end
            
        ::block_2_fin::
    end
    function __FUNCS__.func_40(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+12,0);
        
            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(128)) and 1 or 0)==0 then goto if_15_fin end 
                if ((__UNSIGNED__(reg1) >= __UNSIGNED__(2048)) and 1 or 0)==0 then goto if_19_fin end 
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)==0 then goto if_23_fin end 
                        __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
                        reg2 = 4; goto block_11_fin;
                    ::if_23_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                    __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                    __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                    reg2 = 3; goto block_11_fin;
                ::if_19_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg2 = 2; goto block_11_fin;
            ::if_15_fin::
            __MEMORY_WRITE_8__(mem_0,reg3+12,reg1);
            reg2 = 1
            -- BLOCK RET (block):
        ::block_11_fin::
        reg1 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = __FUNCS__.func_32(reg2,(bit_tobit(reg3 + 12)),reg1);
        reg2 = reg4;
        reg4 = ((reg2)[1]);
        reg5 = (bit_band(reg4,255));
        if ((reg5 ~= 4) and 1 or 0)==0 then goto if_123_fin end 
            reg6 = __MEMORY_READ_8__(mem_0,reg0+4);
            if ((reg6 == 3) and 1 or 0)==0 then goto if_128_fin end 
                reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                reg1 = reg6;
                reg6 = __MEMORY_READ_32__(mem_0,reg1);
                reg7 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg8 = __MEMORY_READ_32__(mem_0,reg7);
                __TABLE_FUNCS_0__[reg8+1](reg6);
                reg6 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg7 = reg6;
                reg6 = __MEMORY_READ_32__(mem_0,reg7+4);
                if reg6==0 then goto if_143_fin end 
                    reg6 = __MEMORY_READ_32__(mem_0,reg7+8);
                    reg6 = __MEMORY_READ_32__(mem_0,reg1);
                    __FUNCS__.func_10(reg6);
                ::if_143_fin::
                __FUNCS__.func_10(reg1);
            ::if_128_fin::
            __MEMORY_WRITE_8__(mem_0,reg0+4,reg4);
            reg1 = (reg2):_shr_u(__LONG_INT__(8,0));
            reg2 = reg1;
            (((reg2):_shr_u(__LONG_INT__(48,0)))):store8(mem_0,(bit_tobit(reg0 + 11)));
            (((reg2):_shr_u(__LONG_INT__(32,0)))):store16(mem_0,(bit_tobit(reg0 + 9)));
            (reg2):store32(mem_0,(bit_tobit(reg0 + 5)));
        ::if_123_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return ((reg5 ~= 4) and 1 or 0); end;
    end
    function __FUNCS__.func_41(reg0, reg1, reg2, reg3, reg4, reg5)
        local reg6,reg7;
        reg6 = __GLOBALS__[0];
        reg7 = (bit_tobit(reg6 - 112));
        __GLOBALS__[0] = reg7;
        __MEMORY_WRITE_32__(mem_0,reg7+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg7+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg7+20,reg3);
        __MEMORY_WRITE_32__(mem_0,reg7+16,reg2);
        __MEMORY_WRITE_32__(mem_0,reg7+24,1055177);
        __MEMORY_WRITE_32__(mem_0,reg7+28,2);
        
            reg0 = __MEMORY_READ_32__(mem_0,reg4);
            if ((reg0 == 0) and 1 or 0)==0 then goto if_29_fin end 
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 76)),52);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 68)),52);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 108)),3);
                (__LONG_INT__(4,0)):store(mem_0,reg7+92);
                __MEMORY_WRITE_32__(mem_0,reg7+88,1055276);
                __MEMORY_WRITE_32__(mem_0,reg7+60,51);
                __MEMORY_WRITE_32__(mem_0,reg7+104,(bit_tobit(reg7 + 56)));
                goto block_25_fin;
            ::if_29_fin::
            reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg4 + 16)));
            (reg0):store(mem_0,(bit_tobit(reg7 + 48)));
            reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg4 + 8)));
            (reg0):store(mem_0,(bit_tobit(reg7 + 40)));
            reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg4);
            (reg0):store(mem_0,reg7+32);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 108)),4);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 84)),53);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 76)),52);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg7 + 68)),52);
            (__LONG_INT__(4,0)):store(mem_0,reg7+92);
            __MEMORY_WRITE_32__(mem_0,reg7+88,1055240);
            __MEMORY_WRITE_32__(mem_0,reg7+60,51);
            __MEMORY_WRITE_32__(mem_0,reg7+104,(bit_tobit(reg7 + 56)));
            __MEMORY_WRITE_32__(mem_0,reg7+80,(bit_tobit(reg7 + 32)));
        ::block_25_fin::
        __MEMORY_WRITE_32__(mem_0,reg7+72,(bit_tobit(reg7 + 16)));
        __MEMORY_WRITE_32__(mem_0,reg7+64,(bit_tobit(reg7 + 8)));
        __MEMORY_WRITE_32__(mem_0,reg7+56,(bit_tobit(reg7 + 24)));
        __FUNCS__.func_122((bit_tobit(reg7 + 88)),reg5);
        error('unreachable');
    end
    function __FUNCS__.func_42(reg0, reg1, reg2, reg3, reg4, reg5)
        local reg6,reg7,reg8;
        
            
                
                    if reg2==0 then goto if_6_fin end 
                        reg6 = __MEMORY_READ_8__(mem_0,reg1);
                        if ((__UNSIGNED__(reg6) < __UNSIGNED__(49)) and 1 or 0)~=0 then goto block_4_fin; end;
                        
                            reg6 = (bit_arshift((bit_lshift(reg3,16)),16));
                            if ((reg6 >= 1) and 1 or 0)==0 then goto if_21_fin end 
                                __MEMORY_WRITE_32__(mem_0,reg5+4,reg1);
                                reg7 = 2;
                                __MEMORY_WRITE_16__(mem_0,reg5,2);
                                reg8 = bit_band(reg3,65535);
                                reg3 = reg8;
                                if ((__UNSIGNED__(reg3) >= __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_12_fin; end;
                                __MEMORY_WRITE_16__(mem_0,reg5+24,2);
                                __MEMORY_WRITE_32__(mem_0,reg5+20,1);
                                __MEMORY_WRITE_32__(mem_0,reg5+16,1054914);
                                __MEMORY_WRITE_16__(mem_0,reg5+12,2);
                                __MEMORY_WRITE_32__(mem_0,reg5+8,reg3);
                                reg8 = bit_tobit(reg2 - reg3);
                                reg2 = reg8;
                                __MEMORY_WRITE_32__(mem_0,reg5+32,reg2);
                                __MEMORY_WRITE_32__(mem_0,reg5+28,(bit_tobit(reg1 + reg3)));
                                reg7 = 3;
                                if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto block_2_fin; end;
                                reg8 = bit_tobit(reg4 - reg2);
                                reg4 = reg8;
                                goto block_3_fin;
                            ::if_21_fin::
                            __MEMORY_WRITE_32__(mem_0,reg5+32,reg2);
                            __MEMORY_WRITE_32__(mem_0,reg5+28,reg1);
                            __MEMORY_WRITE_16__(mem_0,reg5+24,2);
                            __MEMORY_WRITE_16__(mem_0,reg5+12,0);
                            __MEMORY_WRITE_32__(mem_0,reg5+8,2);
                            __MEMORY_WRITE_32__(mem_0,reg5+4,1054912);
                            __MEMORY_WRITE_16__(mem_0,reg5,2);
                            reg1 = (bit_tobit(0 - reg6));
                            __MEMORY_WRITE_32__(mem_0,reg5+16,reg1);
                            reg7 = 3;
                            if ((__UNSIGNED__(reg4) <= __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_2_fin; end;
                            reg8 = bit_tobit(reg4 - reg2);
                            reg2 = reg8;
                            if ((__UNSIGNED__(reg2) <= __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_2_fin; end;
                            reg4 = (bit_tobit(reg2 + reg6));
                            goto block_3_fin;
                        ::block_12_fin::
                        __MEMORY_WRITE_16__(mem_0,reg5+12,0);
                        __MEMORY_WRITE_32__(mem_0,reg5+8,reg2);
                        __MEMORY_WRITE_32__(mem_0,reg5+16,(bit_tobit(reg3 - reg2)));
                        if ((reg4 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
                        __MEMORY_WRITE_32__(mem_0,reg5+32,1);
                        __MEMORY_WRITE_32__(mem_0,reg5+28,1054914);
                        __MEMORY_WRITE_16__(mem_0,reg5+24,2);
                        goto block_3_fin;
                    ::if_6_fin::
                    __FUNCS__.func_110(1054540,33,1054792);
                    error('unreachable');
                ::block_4_fin::
                __FUNCS__.func_110(1054808,33,1054844);
                error('unreachable');
            ::block_3_fin::
            __MEMORY_WRITE_32__(mem_0,reg5+40,reg4);
            __MEMORY_WRITE_16__(mem_0,reg5+36,0);
            reg7 = 4;
        ::block_2_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+4,reg7);
        __MEMORY_WRITE_32__(mem_0,reg0,reg5);
    end
    function __FUNCS__.func_43(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6;
        reg1 = (bit_lshift(reg0,11));
        reg2 = 31;
        reg3 = 31;
        
            -- FORCE INIT VAR | i32
            reg4 = 0;
            
            while true do ::loop_11_start::
                
                    
                        reg5 = bit_tobit((bit_rshift(reg2,1)) + reg4);
                        reg2 = reg5;
                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift(reg2,2)) + 1058248)));
                        reg6 = (bit_lshift(reg5,11));
                        if ((__UNSIGNED__(reg6) >= __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_30_fin end 
                            if ((reg1 == reg6) and 1 or 0)~=0 then goto block_12_fin; end;
                            reg3 = reg2;
                            goto block_13_fin;
                        ::if_30_fin::
                        reg4 = (bit_tobit(reg2 + 1));
                    ::block_13_fin::
                    reg2 = (bit_tobit(reg3 - reg4));
                    if ((__UNSIGNED__(reg3) > __UNSIGNED__(reg4)) and 1 or 0)~=0 then goto loop_11_start; end;
                    goto block_10_fin;
                ::block_12_fin::
                break
            end
            
            reg4 = (bit_tobit(reg2 + 1));
        ::block_10_fin::
        
            
                if ((__UNSIGNED__(reg4) <= __UNSIGNED__(30)) and 1 or 0)==0 then goto if_65_fin end 
                    reg1 = (bit_lshift(reg4,2));
                    reg3 = 689;
                    if ((reg4 ~= 30) and 1 or 0)==0 then goto if_75_fin end 
                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 1058252)));
                        reg3 = (bit_rshift(reg5,21));
                    ::if_75_fin::
                    reg6 = 0;
                    reg2 = (bit_tobit(reg4 + -1));
                    if ((__UNSIGNED__(reg2) <= __UNSIGNED__(reg4)) and 1 or 0)==0 then goto if_92_fin end 
                        if ((__UNSIGNED__(reg2) >= __UNSIGNED__(31)) and 1 or 0)~=0 then goto block_61_fin; end;
                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit((bit_lshift(reg2,2)) + 1058248)));
                        reg6 = (bit_band(reg5,2097151));
                    ::if_92_fin::
                    
                        reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 1058248)));
                        reg4 = (bit_rshift(reg5,21));
                        if ((reg3 == (bit_tobit(reg4 + 1))) and 1 or 0)~=0 then goto block_107_fin; end;
                        reg1 = (bit_tobit(reg0 - reg6));
                        
                        reg2 = ((((__UNSIGNED__(reg4) > __UNSIGNED__(689)) and 1 or 0) == 0) and 689 or reg4);
                        reg0 = (bit_tobit(reg3 + -1));
                        reg3 = 0;
                        
                        while true do ::loop_137_start::
                            if ((reg4 == reg2) and 1 or 0)~=0 then goto block_60_fin; end;
                            reg5 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg4 + 1058372)));
                            reg6 = bit_tobit(reg3 + reg5);
                            reg3 = reg6;
                            if ((__UNSIGNED__(reg3) > __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_107_fin; end;
                            reg5 = bit_tobit(reg4 + 1);
                            reg4 = reg5;
                            if ((reg0 ~= reg4) and 1 or 0)~=0 then goto loop_137_start; end;
                            break
                        end
                        
                        reg4 = reg0;
                    ::block_107_fin::
                    do return (bit_band(reg4,1)) end
                ::if_65_fin::
                __FUNCS__.func_82(reg4,31,1058068);
                error('unreachable');
            ::block_61_fin::
            __FUNCS__.func_82(reg2,31,1058100);
            error('unreachable');
        ::block_60_fin::
        __FUNCS__.func_82(reg2,689,1058084);
        error('unreachable');
    end
    function __FUNCS__.func_44(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        
            if ((__UNSIGNED__(reg1) <= __UNSIGNED__(127)) and 1 or 0)==0 then goto if_14_fin end 
                reg2 = __MEMORY_READ_32__(mem_0,reg0+8);
                reg4 = reg2;
                reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                if ((reg4 == reg2) and 1 or 0)==0 then goto if_23_fin end 
                    __FUNCS__.func_66(reg0,reg4,1);
                    reg2 = __MEMORY_READ_32__(mem_0,reg0+8);
                    reg4 = reg2;
                ::if_23_fin::
                __MEMORY_WRITE_32__(mem_0,reg0+8,(bit_tobit(reg4 + 1)));
                reg2 = __MEMORY_READ_32__(mem_0,reg0);
                __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + reg4)),reg1);
                goto block_10_fin;
            ::if_14_fin::
            __MEMORY_WRITE_32__(mem_0,reg3+12,0);
            
                if ((__UNSIGNED__(reg1) >= __UNSIGNED__(2048)) and 1 or 0)==0 then goto if_52_fin end 
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)==0 then goto if_56_fin end 
                        __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
                        reg2 = 4; goto block_48_fin;
                    ::if_56_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                    __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                    __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                    reg2 = 3; goto block_48_fin;
                ::if_52_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg2 = 2
                -- BLOCK RET (block):
            ::block_48_fin::
            reg1 = reg2;
            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            reg5 = (bit_tobit(reg0 + 8));
            reg6 = __MEMORY_READ_32__(mem_0,reg5);
            reg4 = reg6;
            if ((__UNSIGNED__((bit_tobit(reg2 - reg4))) < __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_148_fin end 
                __FUNCS__.func_66(reg0,reg4,reg1);
                reg2 = __MEMORY_READ_32__(mem_0,reg5);
                reg4 = reg2;
            ::if_148_fin::
            reg2 = __MEMORY_READ_32__(mem_0,reg0);
            reg0 = __FUNCS__.func_64((bit_tobit(reg2 + reg4)),(bit_tobit(reg3 + 12)),reg1);
            __MEMORY_WRITE_32__(mem_0,reg5,(bit_tobit(reg1 + reg4)));
        ::block_10_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return 0; end;
    end
    function __FUNCS__.func_45(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8,reg9;
        
            
                
                    
                        reg4 = (bit_tobit((bit_band((bit_tobit(reg2 + 3)),-4)) - reg2));
                        if ((reg4 == 0) and 1 or 0)~=0 then goto block_5_fin; end;
                        
                        reg5 = ((((__UNSIGNED__(reg4) > __UNSIGNED__(reg3)) and 1 or 0) == 0) and reg4 or reg3);
                        if ((reg5 == 0) and 1 or 0)~=0 then goto block_5_fin; end;
                        reg4 = 0;
                        reg6 = (bit_band(reg1,255));
                        reg7 = 1;
                        
                        while true do ::loop_33_start::
                            reg8 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg2 + reg4)));
                            if ((reg8 == reg6) and 1 or 0)~=0 then goto block_2_fin; end;
                            reg8 = bit_tobit(reg4 + 1);
                            reg4 = reg8;
                            if ((reg5 ~= reg4) and 1 or 0)~=0 then goto loop_33_start; end;
                            break
                        end
                        
                        reg7 = (bit_tobit(reg3 + -8));
                        if ((__UNSIGNED__(reg5) > __UNSIGNED__(reg7)) and 1 or 0)~=0 then goto block_3_fin; end;
                        goto block_4_fin;
                    ::block_5_fin::
                    reg7 = (bit_tobit(reg3 + -8));
                    reg5 = 0;
                ::block_4_fin::
                reg4 = (__IMUL__((bit_band(reg1,255)),16843009));
                
                while true do ::loop_71_start::
                    reg6 = (bit_tobit(reg2 + reg5));
                    reg8 = __MEMORY_READ_32__(mem_0,reg6);
                    reg9 = (bit_bxor(reg8,reg4));
                    reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg6 + 4)));
                    reg6 = (bit_bxor(reg8,reg4));
                    if (((bit_band((bit_bor((bit_band((bit_bxor(reg9,-1)),(bit_tobit(reg9 + -16843009)))),(bit_band((bit_bxor(reg6,-1)),(bit_tobit(reg6 + -16843009)))))),-2139062144)) == 0) and 1 or 0)==0 then goto if_103_fin end 
                        reg6 = bit_tobit(reg5 + 8);
                        reg5 = reg6;
                        if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg7)) and 1 or 0)~=0 then goto loop_71_start; end;
                    ::if_103_fin::
                    break
                end
                
                if ((__UNSIGNED__(reg5) <= __UNSIGNED__(reg3)) and 1 or 0)~=0 then goto block_3_fin; end;
                __FUNCS__.func_83(reg5,reg3,1055888);
                error('unreachable');
            ::block_3_fin::
            
                if ((reg3 == reg5) and 1 or 0)~=0 then goto block_123_fin; end;
                reg6 = bit_tobit(reg3 - reg5);
                reg3 = reg6;
                reg6 = bit_tobit(reg2 + reg5);
                reg2 = reg6;
                reg4 = 0;
                reg6 = bit_band(reg1,255);
                reg1 = reg6;
                
                while true do ::loop_142_start::
                    reg6 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg2 + reg4)));
                    if ((reg1 ~= reg6) and 1 or 0)==0 then goto if_149_fin end 
                        reg6 = bit_tobit(reg4 + 1);
                        reg4 = reg6;
                        if ((reg4 ~= reg3) and 1 or 0)~=0 then goto loop_142_start; end;
                        goto block_123_fin;
                    ::if_149_fin::
                    break
                end
                
                reg6 = bit_tobit(reg4 + reg5);
                reg4 = reg6;
                reg7 = 1;
                goto block_2_fin;
            ::block_123_fin::
            reg7 = 0;
        ::block_2_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+4,reg4);
        __MEMORY_WRITE_32__(mem_0,reg0,reg7);
    end
    function __FUNCS__.func_46(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        reg3 = 39;
        
            if ((reg0):_lt_u(__LONG_INT__(10000,0)) and 1 or 0)==0 then goto if_14_fin end 
                reg5 = reg0;
                goto block_10_fin;
            ::if_14_fin::
            
            while true do ::loop_19_start::
                reg6 = (bit_tobit((bit_tobit(reg4 + 9)) + reg3));
                reg5 = ((reg0):_div_u(__LONG_INT__(10000,0)));
                reg7 = (((reg0 - (reg5 * __LONG_INT__(10000,0))))[1]);
                reg8 = (__IDIV_U__((bit_band(reg7,65535)),100));
                reg9 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_lshift(reg8,1)) + 1055494)));
                __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg6 + -4)),reg9);
                reg9 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_lshift((bit_band((bit_tobit(reg7 - (__IMUL__(reg8,100)))),65535)),1)) + 1055494)));
                __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg6 + -2)),reg9);
                reg7 = bit_tobit(reg3 + -4);
                reg3 = reg7;
                reg7 = (reg0):_gt_u(__LONG_INT__(99999999,0)) and 1 or 0;
                reg0 = reg5;
                if reg7~=0 then goto loop_19_start; end;
                break
            end
            
        ::block_10_fin::
        reg6 = ((reg5)[1]);
        if ((reg6 > 99) and 1 or 0)==0 then goto if_82_fin end 
            reg7 = bit_tobit(reg3 + -2);
            reg3 = reg7;
            reg6 = ((reg5)[1]);
            reg5 = __IDIV_U__((bit_band(reg6,65535)),100);
            reg7 = reg6;
            reg6 = reg5;
            reg5 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_lshift((bit_band((bit_tobit(reg7 - (__IMUL__(reg6,100)))),65535)),1)) + 1055494)));
            __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg3 + (bit_tobit(reg4 + 9)))),reg5);
        ::if_82_fin::
        
            if ((reg6 >= 10) and 1 or 0)==0 then goto if_116_fin end 
                reg5 = bit_tobit(reg3 + -2);
                reg3 = reg5;
                reg5 = __MEMORY_READ_16__(mem_0,(bit_tobit((bit_lshift(reg6,1)) + 1055494)));
                __MEMORY_WRITE_16__(mem_0,(bit_tobit(reg3 + (bit_tobit(reg4 + 9)))),reg5);
                goto block_112_fin;
            ::if_116_fin::
            reg5 = bit_tobit(reg3 + -1);
            reg3 = reg5;
            __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg3 + (bit_tobit(reg4 + 9)))),(bit_tobit(reg6 + 48)));
        ::block_112_fin::
        reg5 = __FUNCS__.func_13(reg2,reg1,1054920,0,(bit_tobit((bit_tobit(reg4 + 9)) + reg3)),(bit_tobit(39 - reg3)));
        __GLOBALS__[0] = (bit_tobit(reg4 + 48));
        do return reg5; end;
    end
    function __FUNCS__.func_47(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        
            
                
                    
                        
                            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                            reg4 = reg2;
                            reg2 = __MEMORY_READ_32__(mem_0,reg1+8);
                            reg5 = reg2;
                            if ((reg4 == reg5) and 1 or 0)==0 then goto if_21_fin end 
                                reg2 = (bit_tobit(reg5 + 1));
                                if ((__UNSIGNED__(reg2) < __UNSIGNED__(reg5)) and 1 or 0)~=0 then goto block_8_fin; end;
                                
                                    if reg5==0 then goto if_31_fin end 
                                        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 24)),1);
                                        __MEMORY_WRITE_32__(mem_0,reg3+20,reg5);
                                        reg6 = __MEMORY_READ_32__(mem_0,reg1);
                                        __MEMORY_WRITE_32__(mem_0,reg3+16,reg6);
                                        goto block_29_fin;
                                    ::if_31_fin::
                                    __MEMORY_WRITE_32__(mem_0,reg3+16,0);
                                ::block_29_fin::
                                __FUNCS__.func_71(reg3,reg2,(bit_tobit(reg3 + 16)));
                                reg6 = __MEMORY_READ_32__(mem_0,reg3);
                                if ((reg6 == 1) and 1 or 0)~=0 then goto block_11_fin; end;
                                reg6 = __MEMORY_READ_32__(mem_0,reg3+4);
                                reg2 = reg6;
                                reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 8)));
                                reg4 = reg6;
                                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 4)),reg4);
                                __MEMORY_WRITE_32__(mem_0,reg1,reg2);
                            ::if_21_fin::
                            if ((reg5 == reg4) and 1 or 0)==0 then goto if_80_fin end 
                                __FUNCS__.func_66(reg1,reg5,1);
                                reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
                                reg4 = reg6;
                                reg6 = __MEMORY_READ_32__(mem_0,reg1+8);
                                reg5 = reg6;
                            ::if_80_fin::
                            reg2 = (bit_tobit(reg5 + 1));
                            __MEMORY_WRITE_32__(mem_0,reg1+8,reg2);
                            reg6 = __MEMORY_READ_32__(mem_0,reg1);
                            reg1 = reg6;
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg1 + reg5)),0);
                            if ((__UNSIGNED__(reg4) > __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_10_fin; end;
                            reg5 = reg1;
                            goto block_9_fin;
                        ::block_11_fin::
                        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 8)));
                        reg0 = reg4;
                        if ((reg0 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                        reg4 = __MEMORY_READ_32__(mem_0,reg3+4);
                        __FUNCS__.func_170(reg4,reg0);
                        error('unreachable');
                    ::block_10_fin::
                    if ((reg2 == 0) and 1 or 0)==0 then goto if_130_fin end 
                        reg5 = 1;
                        __FUNCS__.func_10(reg1);
                        goto block_9_fin;
                    ::if_130_fin::
                    reg4 = __FUNCS__.func_144(reg1,reg2);
                    reg5 = reg4;
                    if ((reg5 == 0) and 1 or 0)~=0 then goto block_7_fin; end;
                ::block_9_fin::
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg2);
                __MEMORY_WRITE_32__(mem_0,reg0,reg5);
                __GLOBALS__[0] = (bit_tobit(reg3 + 32));
                do return  end
            ::block_8_fin::
            __FUNCS__.func_159();
            error('unreachable');
        ::block_7_fin::
        __FUNCS__.func_170(reg2,1);
        error('unreachable');
    end
    function __FUNCS__.func_48(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        
            
                
                    
                        reg2 = __MEMORY_READ_32__(mem_0,reg1);
                        reg4 = reg2;
                        if (((bit_band(reg4,16)) == 0) and 1 or 0)==0 then goto if_17_fin end 
                            if (bit_band(reg4,32))~=0 then goto block_10_fin; end;
                            reg2 = __MEMORY_READ_32__(mem_0,reg0);reg2=__LONG_INT__(reg2,0);
                            reg5 = __FUNCS__.func_46(reg2,1,reg1);
                            reg0 = reg5;
                            goto block_7_fin;
                        ::if_17_fin::
                        reg2 = __MEMORY_READ_32__(mem_0,reg0);
                        reg0 = reg2;
                        reg4 = 0;
                        
                        while true do ::loop_35_start::
                            reg2 = (bit_band(reg0,15));
                            
                            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg4 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg2) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg2)));
                            reg5 = bit_tobit(reg4 + -1);
                            reg4 = reg5;
                            reg5 = bit_rshift(reg0,4);
                            reg6 = (__UNSIGNED__(reg0) > __UNSIGNED__(15)) and 1 or 0;
                            reg0 = reg5;
                            if reg6~=0 then goto loop_35_start; end;
                            break
                        end
                        
                        reg0 = (bit_tobit(reg4 + 128));
                        if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)~=0 then goto block_9_fin; end;
                        reg5 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg4 + reg3)) + 128)),(bit_tobit(0 - reg4)));
                        reg0 = reg5;
                        goto block_7_fin;
                    ::block_10_fin::
                    reg5 = __MEMORY_READ_32__(mem_0,reg0);
                    reg0 = reg5;
                    reg4 = 0;
                    
                    while true do ::loop_94_start::
                        reg2 = (bit_band(reg0,15));
                        
                        __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg4 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg2) < __UNSIGNED__(10)) and 1 or 0) == 0) and 55 or 48) + reg2)));
                        reg2 = bit_tobit(reg4 + -1);
                        reg4 = reg2;
                        reg2 = bit_rshift(reg0,4);
                        reg5 = (__UNSIGNED__(reg0) > __UNSIGNED__(15)) and 1 or 0;
                        reg0 = reg2;
                        if reg5~=0 then goto loop_94_start; end;
                        break
                    end
                    
                    reg0 = (bit_tobit(reg4 + 128));
                    if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)~=0 then goto block_8_fin; end;
                    reg2 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg4 + reg3)) + 128)),(bit_tobit(0 - reg4)));
                    reg0 = reg2;
                    goto block_7_fin;
                ::block_9_fin::
                __FUNCS__.func_83(reg0,128,1055476);
                error('unreachable');
            ::block_8_fin::
            __FUNCS__.func_83(reg0,128,1055476);
            error('unreachable');
        ::block_7_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 128));
        do return reg0; end;
    end
    function __FUNCS__.func_49(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7,reg8;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = 1;
        
            reg4 = __MEMORY_READ_8__(mem_0,reg1);
            if (bit_band(reg4,1))==0 then goto if_15_fin end 
                reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
                reg5 = reg4;
                reg4 = __MEMORY_READ_32__(mem_0,reg1+24);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 28)),0);
                __MEMORY_WRITE_32__(mem_0,reg3+24,1054920);
                (__LONG_INT__(1,0)):store(mem_0,reg3+12);
                __MEMORY_WRITE_32__(mem_0,reg3+8,1056460);
                reg6 = __FUNCS__.func_27(reg4,reg5,(bit_tobit(reg3 + 8)));
                if reg6~=0 then goto block_10_fin; end;
            ::if_15_fin::
            reg4 = __MEMORY_READ_32__(mem_0,reg0+8);
            reg5 = reg4;
            
                
                    reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg0);
                    reg6 = reg4;
                    if (((reg6)[1] == 0) and ((reg6)[2] == 0) and 1 or 0)==0 then goto if_53_fin end 
                        if ((__UNSIGNED__(reg5) > __UNSIGNED__(999999)) and 1 or 0)~=0 then goto block_48_fin; end;
                        if ((__UNSIGNED__(reg5) > __UNSIGNED__(999)) and 1 or 0)~=0 then goto block_47_fin; end;
                        reg4 = __FUNCS__.func_9(reg1,(__LONG_INT__(reg5,0)),0,1);
                        if reg4~=0 then goto block_10_fin; end;
                        reg4 = __MEMORY_READ_32__(mem_0,reg1+24);
                        reg7 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
                        reg8 = __MEMORY_READ_32__(mem_0,reg7+12);
                        reg7 = __TABLE_FUNCS_0__[reg8+1](reg4,1056474,2);
                        reg2 = reg7;
                        goto block_10_fin;
                    ::if_53_fin::
                    reg4 = __FUNCS__.func_9(reg1,reg6,reg5,100000000);
                    if reg4~=0 then goto block_10_fin; end;
                    reg4 = __MEMORY_READ_32__(mem_0,reg1+24);
                    reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
                    reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                    reg6 = __TABLE_FUNCS_0__[reg7+1](reg4,1056468,1);
                    reg2 = reg6;
                    goto block_10_fin;
                ::block_48_fin::
                reg0 = (__IDIV_U__(reg5,1000000));
                reg4 = __FUNCS__.func_9(reg1,(__LONG_INT__(reg0,0)),(bit_tobit(reg5 - (__IMUL__(reg0,1000000)))),100000);
                if reg4~=0 then goto block_10_fin; end;
                reg4 = __MEMORY_READ_32__(mem_0,reg1+24);
                reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
                reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                reg6 = __TABLE_FUNCS_0__[reg7+1](reg4,1056469,2);
                reg2 = reg6;
                goto block_10_fin;
            ::block_47_fin::
            reg0 = (__IDIV_U__(reg5,1000));
            reg4 = __FUNCS__.func_9(reg1,(__LONG_INT__(reg0,0)),(bit_tobit(reg5 - (__IMUL__(reg0,1000)))),100);
            if reg4~=0 then goto block_10_fin; end;
            reg0 = __MEMORY_READ_32__(mem_0,reg1+24);
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
            reg1 = __MEMORY_READ_32__(mem_0,reg4+12);
            reg1 = __TABLE_FUNCS_0__[reg1+1](reg0,1056471,3);
            reg2 = reg1;
        ::block_10_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg2; end;
    end
    function __FUNCS__.func_50(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg3+12,0);
        
            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(128)) and 1 or 0)==0 then goto if_17_fin end 
                if ((__UNSIGNED__(reg1) >= __UNSIGNED__(2048)) and 1 or 0)==0 then goto if_21_fin end 
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)==0 then goto if_25_fin end 
                        __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
                        reg2 = 4; goto block_13_fin;
                    ::if_25_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                    __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                    __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                    reg2 = 3; goto block_13_fin;
                ::if_21_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg2 = 2; goto block_13_fin;
            ::if_17_fin::
            __MEMORY_WRITE_8__(mem_0,reg3+12,reg1);
            reg2 = 1
            -- BLOCK RET (block):
        ::block_13_fin::
        reg1 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 4)));
        reg5 = (bit_tobit(reg4 + 8));
        reg6 = __MEMORY_READ_32__(mem_0,reg5);
        reg0 = reg6;
        if ((__UNSIGNED__((bit_tobit(reg2 - reg0))) < __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_125_fin end 
            __FUNCS__.func_66(reg4,reg0,reg1);
            reg2 = __MEMORY_READ_32__(mem_0,reg5);
            reg0 = reg2;
        ::if_125_fin::
        reg2 = __MEMORY_READ_32__(mem_0,reg4);
        reg4 = __FUNCS__.func_64((bit_tobit(reg2 + reg0)),(bit_tobit(reg3 + 12)),reg1);
        __MEMORY_WRITE_32__(mem_0,reg5,(bit_tobit(reg0 + reg1)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return 0; end;
    end
    function __FUNCS__.func_51(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+12,0);
        
            if ((__UNSIGNED__(reg1) >= __UNSIGNED__(128)) and 1 or 0)==0 then goto if_14_fin end 
                if ((__UNSIGNED__(reg1) >= __UNSIGNED__(2048)) and 1 or 0)==0 then goto if_18_fin end 
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)==0 then goto if_22_fin end 
                        __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
                        reg2 = 4; goto block_10_fin;
                    ::if_22_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                    __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                    __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                    reg2 = 3; goto block_10_fin;
                ::if_18_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg2 = 2; goto block_10_fin;
            ::if_14_fin::
            __MEMORY_WRITE_8__(mem_0,reg3+12,reg1);
            reg2 = 1
            -- BLOCK RET (block):
        ::block_10_fin::
        reg1 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 4)));
        reg5 = (bit_tobit(reg4 + 8));
        reg6 = __MEMORY_READ_32__(mem_0,reg5);
        reg0 = reg6;
        if ((__UNSIGNED__((bit_tobit(reg2 - reg0))) < __UNSIGNED__(reg1)) and 1 or 0)==0 then goto if_122_fin end 
            __FUNCS__.func_66(reg4,reg0,reg1);
            reg2 = __MEMORY_READ_32__(mem_0,reg5);
            reg0 = reg2;
        ::if_122_fin::
        reg2 = __MEMORY_READ_32__(mem_0,reg4);
        reg4 = __FUNCS__.func_64((bit_tobit(reg2 + reg0)),(bit_tobit(reg3 + 12)),reg1);
        __MEMORY_WRITE_32__(mem_0,reg5,(bit_tobit(reg0 + reg1)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return 0; end;
    end
    function __FUNCS__.func_52(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7;
        (__LONG_INT__(0,0)):store(mem_0,reg0+16);
        
            if ((__UNSIGNED__(reg1) < __UNSIGNED__(256)) and 1 or 0)~=0 then reg2 = 0; goto block_6_fin; end;
            if ((__UNSIGNED__(reg1) > __UNSIGNED__(16777215)) and 1 or 0)~=0 then reg2 = 31; goto block_6_fin; end;
            reg3 = (__CLZ__((bit_rshift(reg1,8))));
            reg2 = (bit_tobit((bit_tobit((bit_band((bit_rshift(reg1,(bit_tobit(6 - reg3)))),1)) - (bit_lshift(reg3,1)))) + 62))
            -- BLOCK RET (block):
        ::block_6_fin::
        reg3 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg0+28,reg3);
        reg2 = (bit_tobit((bit_lshift(reg3,2)) + 1059468));
        reg4 = reg0;
        
            
                
                    
                        reg5 = __MEMORY_READ_32__(mem_0,1059200);
                        reg6 = reg5;
                        reg5 = (bit_lshift(1,reg3));
                        if (bit_band(reg6,reg5))==0 then goto if_59_fin end 
                            reg7 = __MEMORY_READ_32__(mem_0,reg2);
                            reg2 = reg7;
                            reg7 = __FUNCS__.func_139(reg3);
                            reg3 = reg7;
                            reg7 = __FUNCS__.func_166(reg2);
                            if ((reg7 ~= reg1) and 1 or 0)~=0 then goto block_50_fin; end;
                            reg3 = reg2;
                            goto block_49_fin;
                        ::if_59_fin::
                        __MEMORY_WRITE_32__(mem_0,1059200,(bit_bor(reg6,reg5)));
                        __MEMORY_WRITE_32__(mem_0,reg2,reg0);
                        goto block_47_fin;
                    ::block_50_fin::
                    reg6 = (bit_lshift(reg1,reg3));
                    
                    while true do ::loop_89_start::
                        reg5 = (bit_tobit((bit_tobit(reg2 + (bit_band((bit_rshift(reg6,29)),4)))) + 16));
                        reg7 = __MEMORY_READ_32__(mem_0,reg5);
                        reg3 = reg7;
                        if ((reg3 == 0) and 1 or 0)~=0 then goto block_48_fin; end;
                        reg7 = bit_lshift(reg6,1);
                        reg6 = reg7;
                        reg2 = reg3;
                        reg7 = __FUNCS__.func_166(reg2);
                        if ((reg7 ~= reg1) and 1 or 0)~=0 then goto loop_89_start; end;
                        break
                    end
                    
                ::block_49_fin::
                reg7 = __MEMORY_READ_32__(mem_0,reg3+8);
                reg1 = reg7;
                __MEMORY_WRITE_32__(mem_0,reg1+12,reg4);
                __MEMORY_WRITE_32__(mem_0,reg3+8,reg4);
                __MEMORY_WRITE_32__(mem_0,reg4+12,reg3);
                __MEMORY_WRITE_32__(mem_0,reg4+8,reg1);
                __MEMORY_WRITE_32__(mem_0,reg0+24,0);
                do return  end
            ::block_48_fin::
            __MEMORY_WRITE_32__(mem_0,reg5,reg0);
        ::block_47_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+24,reg2);
        __MEMORY_WRITE_32__(mem_0,reg4+8,reg4);
        __MEMORY_WRITE_32__(mem_0,reg4+12,reg4);
    end
    function __FUNCS__.func_53(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7,reg8,reg9;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 + -64));
        __GLOBALS__[0] = reg4;
        
            reg5 = __MEMORY_READ_8__(mem_0,reg0+8);
            if reg5==0 then goto if_12_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,reg0+4);
                reg6 = reg5;
                reg3 = 1; goto block_9_fin;
            ::if_12_fin::
            reg5 = __MEMORY_READ_32__(mem_0,reg0+4);
            reg6 = reg5;
            reg5 = __MEMORY_READ_32__(mem_0,reg0);
            reg7 = reg5;
            reg5 = __MEMORY_READ_8__(mem_0,reg7);
            if (((bit_band(reg5,4)) == 0) and 1 or 0)==0 then goto if_29_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,reg7+24);
                
                
                reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + 28)));
                reg9 = __MEMORY_READ_32__(mem_0,reg8+12);
                reg8 = __TABLE_FUNCS_0__[reg9+1](reg5,((reg6 == 0) and 1055443 or 1055422),((reg6 == 0) and 1 or 2));
                if reg8~=0 then reg3 = 1; goto block_9_fin; end;
                reg5 = __MEMORY_READ_32__(mem_0,reg2+12);
                reg5 = __TABLE_FUNCS_0__[reg5+1](reg1,reg7);
                reg3 = reg5; goto block_9_fin;
            ::if_29_fin::
            
                if reg6~=0 then goto block_56_fin; end;
                reg5 = __MEMORY_READ_32__(mem_0,reg7+24);
                reg8 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg7 + 28)));
                reg9 = __MEMORY_READ_32__(mem_0,reg8+12);
                reg8 = __TABLE_FUNCS_0__[reg9+1](reg5,1055441,2);
                if ((reg8 == 0) and 1 or 0)~=0 then goto block_56_fin; end;
                reg6 = 0;
                reg3 = 1; goto block_9_fin;
            ::block_56_fin::
            __MEMORY_WRITE_8__(mem_0,reg4+23,1);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 52)),1055328);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 16)),(bit_tobit(reg4 + 23)));
            reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg7+24);
            (reg5):store(mem_0,reg4+8);
            reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg7+8);
            reg8 = reg5;
            reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg7+16);
            reg9 = reg5;
            reg5 = __MEMORY_READ_8__(mem_0,reg7+32);
            __MEMORY_WRITE_8__(mem_0,reg4+56,reg5);
            (reg9):store(mem_0,reg4+40);
            (reg8):store(mem_0,reg4+32);
            reg5 = __LONG_INT__(0,0); reg5:load(mem_0,reg7);
            (reg5):store(mem_0,reg4+24);
            __MEMORY_WRITE_32__(mem_0,reg4+48,(bit_tobit(reg4 + 8)));
            reg5 = __MEMORY_READ_32__(mem_0,reg2+12);
            reg2 = __TABLE_FUNCS_0__[reg5+1](reg1,(bit_tobit(reg4 + 24)));
            if reg2~=0 then reg3 = 1; goto block_9_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg4+48);
            reg2 = __MEMORY_READ_32__(mem_0,reg4+52);
            reg5 = __MEMORY_READ_32__(mem_0,reg2+12);
            reg2 = __TABLE_FUNCS_0__[reg5+1](reg1,1055420,2);
            reg3 = reg2
            -- BLOCK RET (block):
        ::block_9_fin::
        __MEMORY_WRITE_8__(mem_0,reg0+8,reg3);
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_tobit(reg6 + 1)));
        __GLOBALS__[0] = (bit_tobit(reg4 - -64));
    end
    function __FUNCS__.func_54(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg2 = reg1;
        
            
                reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
                if ((reg0 == reg1) and 1 or 0)==0 then goto if_11_fin end 
                    reg1 = (bit_tobit(reg0 + 20));
                    reg3 = __MEMORY_READ_32__(mem_0,reg1);
                    reg4 = reg3;
                    
                    reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + ((reg4 == 0) and 16 or 20))));
                    reg5 = reg3;
                    if reg5~=0 then goto block_6_fin; end;
                    reg1 = 0;
                    goto block_5_fin;
                ::if_11_fin::
                reg3 = __MEMORY_READ_32__(mem_0,reg0+8);
                reg5 = reg3;
                reg3 = __MEMORY_READ_32__(mem_0,reg0+12);
                reg1 = reg3;
                __MEMORY_WRITE_32__(mem_0,reg5+12,reg1);
                __MEMORY_WRITE_32__(mem_0,reg1+8,reg5);
                goto block_5_fin;
            ::block_6_fin::
            
            reg3 = (reg4 == 0) and (bit_tobit(reg0 + 16)) or reg1;
            reg4 = reg3;
            
            while true do ::loop_49_start::
                reg3 = reg4;
                reg1 = reg5;
                reg4 = (bit_tobit(reg1 + 20));
                reg6 = __MEMORY_READ_32__(mem_0,reg4);
                reg5 = reg6;
                if ((reg5 == 0) and 1 or 0)==0 then goto if_60_fin end 
                    reg4 = (bit_tobit(reg1 + 16));
                    reg6 = __MEMORY_READ_32__(mem_0,reg1+16);
                    reg5 = reg6;
                ::if_60_fin::
                if reg5~=0 then goto loop_49_start; end;
                break
            end
            
            __MEMORY_WRITE_32__(mem_0,reg3,0);
        ::block_5_fin::
        
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_76_fin; end;
            
                reg3 = __MEMORY_READ_32__(mem_0,reg0+28);
                reg5 = (bit_tobit((bit_lshift(reg3,2)) + 1059468));
                reg3 = __MEMORY_READ_32__(mem_0,reg5);
                if ((reg0 ~= reg3) and 1 or 0)==0 then goto if_91_fin end 
                    reg3 = __MEMORY_READ_32__(mem_0,reg2+16);
                    
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + ((((reg3 == reg0) and 1 or 0) == 0) and 20 or 16))),reg1);
                    if reg1~=0 then goto block_80_fin; end;
                    goto block_76_fin;
                ::if_91_fin::
                __MEMORY_WRITE_32__(mem_0,reg5,reg1);
                if reg1~=0 then goto block_80_fin; end;
                reg3 = __MEMORY_READ_32__(mem_0,1059200);
                reg6 = __MEMORY_READ_32__(mem_0,reg0+28);
                __MEMORY_WRITE_32__(mem_0,1059200,(bit_band(reg3,(bit_rol(-2,reg6)))));
                do return  end
            ::block_80_fin::
            __MEMORY_WRITE_32__(mem_0,reg1+24,reg2);
            reg2 = __MEMORY_READ_32__(mem_0,reg0+16);
            reg5 = reg2;
            if reg5==0 then goto if_129_fin end 
                __MEMORY_WRITE_32__(mem_0,reg1+16,reg5);
                __MEMORY_WRITE_32__(mem_0,reg5+24,reg1);
            ::if_129_fin::
            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
            reg0 = reg2;
            if ((reg0 == 0) and 1 or 0)~=0 then goto block_76_fin; end;
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 20)),reg0);
            __MEMORY_WRITE_32__(mem_0,reg0+24,reg1);
        ::block_76_fin::
    end
    function __FUNCS__.func_55(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6,reg7;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 + -64));
        __GLOBALS__[0] = reg3;
        reg2 = 1;
        
            reg4 = __MEMORY_READ_8__(mem_0,reg0+4);
            if reg4~=0 then goto block_10_fin; end;
            reg4 = __MEMORY_READ_8__(mem_0,reg0+5);
            reg2 = reg4;
            
                
                    
                        
                            reg4 = __MEMORY_READ_32__(mem_0,reg0);
                            reg5 = reg4;
                            reg4 = __MEMORY_READ_8__(mem_0,reg5);
                            if (((bit_band(reg4,4)) == 0) and 1 or 0)==0 then goto if_28_fin end 
                                if reg2~=0 then goto block_20_fin; end;
                                goto block_17_fin;
                            ::if_28_fin::
                            if ((reg2 == 0) and 1 or 0)~=0 then goto block_19_fin; end;
                            goto block_18_fin;
                        ::block_20_fin::
                        reg2 = 1;
                        reg4 = __MEMORY_READ_32__(mem_0,reg5+24);
                        reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + 28)));
                        reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                        reg6 = __TABLE_FUNCS_0__[reg7+1](reg4,1055422,2);
                        if ((reg6 == 0) and 1 or 0)~=0 then goto block_17_fin; end;
                        goto block_10_fin;
                    ::block_19_fin::
                    reg2 = 1;
                    reg4 = __MEMORY_READ_32__(mem_0,reg5+24);
                    reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg5 + 28)));
                    reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                    reg6 = __TABLE_FUNCS_0__[reg7+1](reg4,1055446,1);
                    if reg6~=0 then goto block_10_fin; end;
                ::block_18_fin::
                reg2 = 1;
                __MEMORY_WRITE_8__(mem_0,reg3+23,1);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 52)),1055328);
                __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 16)),(bit_tobit(reg3 + 23)));
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5+24);
                (reg4):store(mem_0,reg3+8);
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5+8);
                reg6 = reg4;
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5+16);
                reg7 = reg4;
                reg4 = __MEMORY_READ_8__(mem_0,reg5+32);
                __MEMORY_WRITE_8__(mem_0,reg3+56,reg4);
                (reg7):store(mem_0,reg3+40);
                (reg6):store(mem_0,reg3+32);
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg5);
                (reg4):store(mem_0,reg3+24);
                __MEMORY_WRITE_32__(mem_0,reg3+48,(bit_tobit(reg3 + 8)));
                reg4 = __MEMORY_READ_32__(mem_0,1049028);
                reg4 = __TABLE_FUNCS_0__[reg4+1](reg1,(bit_tobit(reg3 + 24)));
                if reg4~=0 then goto block_10_fin; end;
                reg4 = __MEMORY_READ_32__(mem_0,reg3+48);
                reg6 = __MEMORY_READ_32__(mem_0,reg3+52);
                reg7 = __MEMORY_READ_32__(mem_0,reg6+12);
                reg6 = __TABLE_FUNCS_0__[reg7+1](reg4,1055420,2);
                reg2 = reg6;
                goto block_10_fin;
            ::block_17_fin::
            reg4 = __MEMORY_READ_32__(mem_0,1049028);
            reg4 = __TABLE_FUNCS_0__[reg4+1](reg1,reg5);
            reg2 = reg4;
        ::block_10_fin::
        __MEMORY_WRITE_8__(mem_0,reg0+5,1);
        __MEMORY_WRITE_8__(mem_0,reg0+4,reg2);
        __GLOBALS__[0] = (bit_tobit(reg3 - -64));
    end
    function __FUNCS__.func_56()
        local reg0,reg1,reg2,reg3,reg4,reg5;
        reg0 = __MEMORY_READ_32__(mem_0,1059628);
        reg1 = reg0;
        if ((reg1 == 0) and 1 or 0)==0 then goto if_6_fin end 
            __MEMORY_WRITE_32__(mem_0,1059644,4095);
            do return 0 end
        ::if_6_fin::
        reg0 = 1059620;
        -- FORCE INIT VAR | i32
        reg2 = 0;
        
        while true do ::loop_15_start::
            reg3 = reg1;
            reg4 = __MEMORY_READ_32__(mem_0,reg3+8);
            reg1 = reg4;
            reg4 = __MEMORY_READ_32__(mem_0,reg3+4);
            reg5 = reg4;
            reg4 = __MEMORY_READ_32__(mem_0,reg3);
            reg5 = reg4;
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 12)));
            reg0 = reg3;
            reg0 = bit_tobit(reg2 + 1);
            reg2 = reg0;
            if reg1~=0 then goto loop_15_start; end;
            break
        end
        
        
        __MEMORY_WRITE_32__(mem_0,1059644,((((__UNSIGNED__(reg2) > __UNSIGNED__(4095)) and 1 or 0) == 0) and 4095 or reg2));
        -- FORCE INIT VAR | i32
        reg0 = 0;
        do return reg0; end;
    end
    function __FUNCS__.func_57(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 48));
        __GLOBALS__[0] = reg3;
        reg2 = (bit_tobit(reg1 + 4));
        
            reg4 = __MEMORY_READ_32__(mem_0,reg1+4);
            if reg4==0 then goto if_15_fin end 
                reg4 = __MEMORY_READ_32__(mem_0,1049400);
                reg5 = reg4;
                goto block_12_fin;
            ::if_15_fin::
            reg4 = __MEMORY_READ_32__(mem_0,reg1);
            reg6 = reg4;
            (__LONG_INT__(0,0)):store(mem_0,reg3+12);
            reg4 = __MEMORY_READ_32__(mem_0,1049400);
            reg5 = reg4;
            __MEMORY_WRITE_32__(mem_0,reg3+8,reg5);
            __MEMORY_WRITE_32__(mem_0,reg3+20,(bit_tobit(reg3 + 8)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg6 + 16)));
            (reg4):store(mem_0,(bit_tobit(reg3 + 40)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg6 + 8)));
            (reg4):store(mem_0,(bit_tobit(reg3 + 32)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg6);
            (reg4):store(mem_0,reg3+24);
            reg4 = __FUNCS__.func_27((bit_tobit(reg3 + 20)),1048944,(bit_tobit(reg3 + 24)));
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 16)));
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 8)),reg4);
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg3+8);
            (reg4):store(mem_0,reg2);
        ::block_12_fin::
        reg6 = (bit_tobit(reg3 + 32));
        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 8)));
        __MEMORY_WRITE_32__(mem_0,reg6,reg4);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 12)),0);
        reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg2);
        reg2 = reg4;
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 8)),0);
        __MEMORY_WRITE_32__(mem_0,reg1+4,reg5);
        (reg2):store(mem_0,reg3+24);
        reg2 = __FUNCS__.func_148(12,4);
        reg1 = reg2;
        if ((reg1 == 0) and 1 or 0)==0 then goto if_112_fin end 
            __FUNCS__.func_170(12,4);
            error('unreachable');
        ::if_112_fin::
        reg2 = __LONG_INT__(0,0); reg2:load(mem_0,reg3+24);
        (reg2):store(mem_0,reg1);
        reg2 = __MEMORY_READ_32__(mem_0,reg6);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg1 + 8)),reg2);
        __MEMORY_WRITE_32__(mem_0,reg0+4,1051084);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
        __GLOBALS__[0] = (bit_tobit(reg3 + 48));
    end
    function __FUNCS__.func_58(reg0)
        local reg1,reg2,reg3,reg4;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 32));
        __GLOBALS__[0] = reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = reg1;
        __MEMORY_WRITE_32__(mem_0,reg0,2);
        
            
                
                    
                        
                        if reg3 == 0 then goto block_14_fin;
                        elseif reg3 == 1 then goto block_15_fin;
                        elseif reg3 == 2 then goto block_14_fin;
                        else goto block_16_fin;
                        end
                    ::block_16_fin::
                    __FUNCS__.func_126(1051324,28,1051352);
                    error('unreachable');
                ::block_15_fin::
                reg1 = __MEMORY_READ_8__(mem_0,reg0+4);
                reg3 = reg1;
                __MEMORY_WRITE_8__(mem_0,reg0+4,1);
                reg1 = bit_band(reg3,1);
                reg3 = reg1;
                __MEMORY_WRITE_8__(mem_0,reg2+7,reg3);
                if reg3~=0 then goto block_13_fin; end;
                reg3 = (bit_tobit(reg0 + 4));
                
                    
                        
                            
                                reg1 = __MEMORY_READ_32__(mem_0,1059144);
                                if (bit_band(reg1,2147483647))==0 then goto if_52_fin end 
                                    reg1 = __FUNCS__.func_134();
                                    reg4 = reg1;
                                    reg1 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg0 + 5)));
                                    if ((reg1 == 0) and 1 or 0)~=0 then goto block_46_fin; end;
                                    reg1 = bit_bxor(reg4,1);
                                    reg4 = reg1;
                                    goto block_47_fin;
                                ::if_52_fin::
                                reg1 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg0 + 5)));
                                if ((reg1 == 0) and 1 or 0)~=0 then goto block_45_fin; end;
                            ::block_47_fin::
                            __MEMORY_WRITE_8__(mem_0,reg2+12,reg4);
                            __MEMORY_WRITE_32__(mem_0,reg2+8,reg3);
                            __FUNCS__.func_79(1049308,43,(bit_tobit(reg2 + 8)),1049352,1051368);
                            error('unreachable');
                        ::block_46_fin::
                        if ((reg4 == 0) and 1 or 0)~=0 then goto block_44_fin; end;
                    ::block_45_fin::
                    reg0 = __MEMORY_READ_32__(mem_0,1059144);
                    if (((bit_band(reg0,2147483647)) == 0) and 1 or 0)~=0 then goto block_44_fin; end;
                    reg0 = __FUNCS__.func_134();
                    if reg0~=0 then goto block_44_fin; end;
                    __MEMORY_WRITE_8__(mem_0,reg3+1,1);
                ::block_44_fin::
                __MEMORY_WRITE_8__(mem_0,reg3,0);
            ::block_14_fin::
            __GLOBALS__[0] = (bit_tobit(reg2 + 32));
            do return  end
        ::block_13_fin::
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 28)),0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 24)),1049032);
        (__LONG_INT__(1,0)):store(mem_0,reg2+12);
        __MEMORY_WRITE_32__(mem_0,reg2+8,1051628);
        __FUNCS__.func_88((bit_tobit(reg2 + 7)),(bit_tobit(reg2 + 8)));
        error('unreachable');
    end
    function __FUNCS__.func_59(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+12,0);
        
            
                
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(128)) and 1 or 0)==0 then goto if_21_fin end 
                        if ((__UNSIGNED__(reg1) < __UNSIGNED__(2048)) and 1 or 0)~=0 then goto block_17_fin; end;
                        if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)~=0 then goto block_16_fin; end;
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        reg0 = 3; goto block_15_fin;
                    ::if_21_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+12,reg1);
                    reg0 = 1; goto block_15_fin;
                ::block_17_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg0 = 2; goto block_15_fin;
            ::block_16_fin::
            __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
            __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
            __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
            __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
            reg0 = 4
            -- BLOCK RET (block):
        ::block_15_fin::
        reg1 = __FUNCS__.func_30(reg2,(bit_tobit(reg3 + 12)),reg0);
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg1; end;
    end
    function __FUNCS__.func_60()
        local reg0,reg1,reg2,reg3,reg4;
        reg0 = __GLOBALS__[0];
        reg1 = (bit_tobit(reg0 - 32));
        __GLOBALS__[0] = reg1;
        
            
                reg0 = __MEMORY_READ_32__(mem_0,1059188);
                reg2 = reg0;
                if ((__UNSIGNED__(reg2) < __UNSIGNED__(2147483647)) and 1 or 0)==0 then goto if_14_fin end 
                    reg0 = __MEMORY_READ_32__(mem_0,1059192);
                    reg3 = reg0;
                    if reg3~=0 then goto block_7_fin; end;
                    __MEMORY_WRITE_32__(mem_0,reg1+8,0);
                    reg0 = __FUNCS__.func_29((bit_tobit(reg1 + 8)));
                    reg3 = reg0;
                    reg0 = __MEMORY_READ_32__(mem_0,1059188);
                    if reg0~=0 then goto block_8_fin; end;
                    __MEMORY_WRITE_32__(mem_0,1059188,-1);
                    
                        reg0 = __MEMORY_READ_32__(mem_0,1059192);
                        reg2 = reg0;
                        if ((reg2 == 0) and 1 or 0)~=0 then goto block_33_fin; end;
                        reg0 = __MEMORY_READ_32__(mem_0,reg2);
                        reg4 = reg2;
                        reg2 = reg0;
                        __MEMORY_WRITE_32__(mem_0,reg4,(bit_tobit(reg2 + -1)));
                        if ((reg2 ~= 1) and 1 or 0)~=0 then goto block_33_fin; end;
                        reg0 = __MEMORY_READ_32__(mem_0,1059192);
                        __FUNCS__.func_100(reg0);
                    ::block_33_fin::
                    __MEMORY_WRITE_32__(mem_0,1059192,reg3);
                    reg0 = __MEMORY_READ_32__(mem_0,1059188);
                    reg2 = (bit_tobit(reg0 + 1));
                    __MEMORY_WRITE_32__(mem_0,1059188,reg2);
                    goto block_7_fin;
                ::if_14_fin::
                __FUNCS__.func_79(1049048,24,(bit_tobit(reg1 + 24)),1049292,1050936);
                error('unreachable');
            ::block_8_fin::
            __FUNCS__.func_79(1049032,16,(bit_tobit(reg1 + 24)),1049260,1050952);
            error('unreachable');
        ::block_7_fin::
        
            if ((reg2 == 0) and 1 or 0)==0 then goto if_89_fin end 
                __MEMORY_WRITE_32__(mem_0,1059188,-1);
                reg0 = __MEMORY_READ_32__(mem_0,reg3);
                reg2 = reg0;
                __MEMORY_WRITE_32__(mem_0,reg3,(bit_tobit(reg2 + 1)));
                if ((reg2 <= -1) and 1 or 0)~=0 then goto block_86_fin; end;
                reg0 = __MEMORY_READ_32__(mem_0,1059188);
                __MEMORY_WRITE_32__(mem_0,1059188,(bit_tobit(reg0 + 1)));
                __GLOBALS__[0] = (bit_tobit(reg1 + 32));
                do return reg3 end
            ::if_89_fin::
            __FUNCS__.func_79(1049032,16,(bit_tobit(reg1 + 24)),1049260,1050968);
            error('unreachable');
        ::block_86_fin::
        error('unreachable');
    end
    function __FUNCS__.func_61(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+12,0);
        
            
                
                    if ((__UNSIGNED__(reg1) >= __UNSIGNED__(128)) and 1 or 0)==0 then goto if_20_fin end 
                        if ((__UNSIGNED__(reg1) < __UNSIGNED__(2048)) and 1 or 0)~=0 then goto block_16_fin; end;
                        if ((__UNSIGNED__(reg1) >= __UNSIGNED__(65536)) and 1 or 0)~=0 then goto block_15_fin; end;
                        __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band(reg1,63)),128)));
                        __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,12)),224)));
                        __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
                        reg2 = 3; goto block_14_fin;
                    ::if_20_fin::
                    __MEMORY_WRITE_8__(mem_0,reg3+12,reg1);
                    reg2 = 1; goto block_14_fin;
                ::block_16_fin::
                __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band(reg1,63)),128)));
                __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,6)),192)));
                reg2 = 2; goto block_14_fin;
            ::block_15_fin::
            __MEMORY_WRITE_8__(mem_0,reg3+15,(bit_bor((bit_band(reg1,63)),128)));
            __MEMORY_WRITE_8__(mem_0,reg3+12,(bit_bor((bit_rshift(reg1,18)),240)));
            __MEMORY_WRITE_8__(mem_0,reg3+14,(bit_bor((bit_band((bit_rshift(reg1,6)),63)),128)));
            __MEMORY_WRITE_8__(mem_0,reg3+13,(bit_bor((bit_band((bit_rshift(reg1,12)),63)),128)));
            reg2 = 4
            -- BLOCK RET (block):
        ::block_14_fin::
        reg1 = __FUNCS__.func_30(reg0,(bit_tobit(reg3 + 12)),reg2);
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg1; end;
    end
    function __FUNCS__.func_62(reg0)
        local reg1,reg2,reg3,reg4,reg5;
        reg1 = 1048604;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 48));
        __GLOBALS__[0] = reg3;
        
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,1059152);
            if ((reg4 == __LONG_INT__(1,0)) and 1 or 0)==0 then goto if_16_fin end 
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,1059168);
                reg5 = reg4;
                reg4 = __LONG_INT__(0,0); reg4:load(mem_0,1059160);
                reg2 = reg4; goto block_11_fin;
            ::if_16_fin::
            reg4 = (bit_tobit(reg3 + 16));
            (__LONG_INT__(2,0)):store(mem_0,reg4+8);
            (__LONG_INT__(1,0)):store(mem_0,reg4);
            (__LONG_INT__(1,0)):store(mem_0,1059152);
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg3+24);
            reg5 = reg4;
            (reg5):store(mem_0,1059168);
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg3+16);
            reg2 = reg4
            -- BLOCK RET (block):
        ::block_11_fin::
        reg4 = reg2;
        ((reg4 + __LONG_INT__(1,0))):store(mem_0,1059160);
        (__LONG_INT__(0,0)):store(mem_0,(bit_tobit(reg0 + 24)));
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 20)),1051824);
        __MEMORY_WRITE_32__(mem_0,reg0+16,0);
        (reg5):store(mem_0,reg0+8);
        (reg4):store(mem_0,reg0);
        __FUNCS__.func_3((bit_tobit(reg3 + 32)),(bit_tobit(reg0 + 16)),9,reg0);
        
        while true do ::loop_76_start::
            reg2 = __MEMORY_READ_32__(mem_0,reg1);
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 4)));
            __FUNCS__.func_17((bit_tobit(reg3 + 8)),reg0,reg2,reg4);
            reg2 = bit_tobit(reg1 + 8);
            reg1 = reg2;
            if ((reg1 ~= 1048676) and 1 or 0)~=0 then goto loop_76_start; end;
            break
        end
        
        __GLOBALS__[0] = (bit_tobit(reg3 + 48));
    end
    function __FUNCS__.func_63(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7,reg8;
        reg4 = __GLOBALS__[0];
        reg5 = (bit_tobit(reg4 - 32));
        __GLOBALS__[0] = reg5;
        reg4 = 1;
        reg6 = __MEMORY_READ_32__(mem_0,1059144);
        reg7 = reg6;
        __MEMORY_WRITE_32__(mem_0,1059144,(bit_tobit(reg7 + 1)));
        
            reg6 = __MEMORY_READ_32__(mem_0,1059648);
            if ((reg6 == 1) and 1 or 0)==0 then goto if_21_fin end 
                reg6 = __MEMORY_READ_32__(mem_0,1059652);
                reg4 = (bit_tobit(reg6 + 1));
                goto block_16_fin;
            ::if_21_fin::
            __MEMORY_WRITE_32__(mem_0,1059648,1);
        ::block_16_fin::
        __MEMORY_WRITE_32__(mem_0,1059652,reg4);
        
            
                if (bit_bor(((reg7 < 0) and 1 or 0),((__UNSIGNED__(reg4) > __UNSIGNED__(2)) and 1 or 0)))~=0 then goto block_37_fin; end;
                __MEMORY_WRITE_32__(mem_0,reg5+28,reg3);
                __MEMORY_WRITE_32__(mem_0,reg5+24,reg2);
                reg6 = __MEMORY_READ_32__(mem_0,1059132);
                reg2 = reg6;
                if ((reg2 <= -1) and 1 or 0)~=0 then goto block_37_fin; end;
                reg6 = bit_tobit(reg2 + 1);
                reg2 = reg6;
                __MEMORY_WRITE_32__(mem_0,1059132,reg2);
                reg6 = __MEMORY_READ_32__(mem_0,1059140);
                reg3 = reg6;
                if reg3==0 then goto if_68_else end 
                    reg7 = __MEMORY_READ_32__(mem_0,1059136);
                    reg8 = __MEMORY_READ_32__(mem_0,reg1+16);
                    __TABLE_FUNCS_0__[reg8+1]((bit_tobit(reg5 + 8)),reg0);
                    reg8 = __LONG_INT__(0,0); reg8:load(mem_0,reg5+8);
                    (reg8):store(mem_0,reg5+16);
                    reg8 = __MEMORY_READ_32__(mem_0,reg3+20);
                    __TABLE_FUNCS_0__[reg8+1](reg7,(bit_tobit(reg5 + 16)));
                    reg3 = __MEMORY_READ_32__(mem_0,1059132);
                    reg6 = reg3
                goto if_68_fin
                ::if_68_else::
                    reg6 = reg2
                    -- BLOCK RET (if):
                ::if_68_fin::
                __MEMORY_WRITE_32__(mem_0,1059132,(bit_tobit(reg6 + -1)));
                if ((__UNSIGNED__(reg4) <= __UNSIGNED__(1)) and 1 or 0)~=0 then goto block_36_fin; end;
            ::block_37_fin::
            error('unreachable');
        ::block_36_fin::
        reg3 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg2;
        __MEMORY_WRITE_32__(mem_0,reg2+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg2+8,reg0);
        error('unreachable');
    end
    function __FUNCS__.func_64(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7;
        
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg3 = (bit_band(reg2,3));
            if ((__UNSIGNED__((bit_tobit(reg2 + -1))) >= __UNSIGNED__(3)) and 1 or 0)==0 then goto if_15_fin end 
                reg4 = (bit_band(reg2,-4));
                -- FORCE INIT VAR | i32
                reg5 = 0;
                -- FORCE INIT VAR | i32
                reg5 = 0;
                -- FORCE INIT VAR | i32
                reg5 = 0;
                
                while true do ::loop_20_start::
                    reg2 = (bit_tobit(reg0 + reg5));
                    reg6 = (bit_tobit(reg1 + reg5));
                    reg7 = __MEMORY_READ_8__(mem_0,reg6);
                    __MEMORY_WRITE_8__(mem_0,reg2,reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg6 + 1)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 1)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg6 + 2)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 2)),reg7);
                    reg7 = __MEMORY_READ_8__(mem_0,(bit_tobit(reg6 + 3)));
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 3)),reg7);
                    reg6 = bit_tobit(reg5 + 4);
                    reg5 = reg6;
                    if ((reg4 ~= reg5) and 1 or 0)~=0 then goto loop_20_start; end;
                    break
                end
                
            ::if_15_fin::
            if ((reg3 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg2 = (bit_tobit(reg1 + reg5));
            reg1 = bit_tobit(reg0 + reg5);
            reg5 = reg1;
            
            while true do ::loop_75_start::
                reg1 = __MEMORY_READ_8__(mem_0,reg2);
                __MEMORY_WRITE_8__(mem_0,reg5,reg1);
                reg1 = bit_tobit(reg2 + 1);
                reg2 = reg1;
                reg1 = bit_tobit(reg5 + 1);
                reg5 = reg1;
                reg1 = bit_tobit(reg3 + -1);
                reg3 = reg1;
                if reg3~=0 then goto loop_75_start; end;
                break
            end
            
        ::block_2_fin::
        do return reg0; end;
    end
    function __FUNCS__.func_65(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6;
        
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg3 = (bit_band(reg2,7));
            if ((__UNSIGNED__((bit_tobit(reg2 + -1))) >= __UNSIGNED__(7)) and 1 or 0)==0 then goto if_15_fin end 
                reg4 = (bit_band(reg2,-8));
                -- FORCE INIT VAR | i32
                reg5 = 0;
                -- FORCE INIT VAR | i32
                reg5 = 0;
                
                while true do ::loop_20_start::
                    reg2 = (bit_tobit(reg0 + reg5));
                    __MEMORY_WRITE_8__(mem_0,reg2,reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 7)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 6)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 5)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 4)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 3)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 2)),reg1);
                    __MEMORY_WRITE_8__(mem_0,(bit_tobit(reg2 + 1)),reg1);
                    reg6 = bit_tobit(reg5 + 8);
                    reg5 = reg6;
                    if ((reg4 ~= reg5) and 1 or 0)~=0 then goto loop_20_start; end;
                    break
                end
                
            ::if_15_fin::
            if ((reg3 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg2 = (bit_tobit(reg0 + reg5));
            
            while true do ::loop_78_start::
                __MEMORY_WRITE_8__(mem_0,reg2,reg1);
                reg5 = bit_tobit(reg2 + 1);
                reg2 = reg5;
                reg5 = bit_tobit(reg3 + -1);
                reg3 = reg5;
                if reg3~=0 then goto loop_78_start; end;
                break
            end
            
        ::block_2_fin::
        do return reg0; end;
    end
    function __FUNCS__.func_66(reg0, reg1, reg2)
        local reg3,reg4,reg5;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 32));
        __GLOBALS__[0] = reg4;
        
            reg3 = bit_tobit(reg1 + reg2);
            reg2 = reg3;
            if ((__UNSIGNED__(reg2) < __UNSIGNED__(reg1)) and 1 or 0)~=0 then goto block_7_fin; end;
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            reg1 = reg3;
            reg3 = (bit_lshift(reg1,1));
            
            reg5 = (((__UNSIGNED__(reg3) > __UNSIGNED__(reg2)) and 1 or 0) == 0) and reg2 or reg3;
            reg2 = reg5;
            
            reg3 = (((__UNSIGNED__(reg2) > __UNSIGNED__(8)) and 1 or 0) == 0) and 8 or reg2;
            reg2 = reg3;
            
                if reg1==0 then goto if_37_fin end 
                    __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 24)),1);
                    __MEMORY_WRITE_32__(mem_0,reg4+20,reg1);
                    reg1 = __MEMORY_READ_32__(mem_0,reg0);
                    __MEMORY_WRITE_32__(mem_0,reg4+16,reg1);
                    goto block_35_fin;
                ::if_37_fin::
                __MEMORY_WRITE_32__(mem_0,reg4+16,0);
            ::block_35_fin::
            __FUNCS__.func_71(reg4,reg2,(bit_tobit(reg4 + 16)));
            reg1 = __MEMORY_READ_32__(mem_0,reg4);
            if ((reg1 == 1) and 1 or 0)==0 then goto if_66_fin end 
                reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 8)));
                reg0 = reg1;
                if ((reg0 == 0) and 1 or 0)~=0 then goto block_7_fin; end;
                reg1 = __MEMORY_READ_32__(mem_0,reg4+4);
                __FUNCS__.func_170(reg1,reg0);
                error('unreachable');
            ::if_66_fin::
            reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg4+4);
            (reg1):store(mem_0,reg0);
            __GLOBALS__[0] = (bit_tobit(reg4 + 32));
            do return  end
        ::block_7_fin::
        __FUNCS__.func_159();
        error('unreachable');
    end
    function __FUNCS__.func_67(reg0)
        local reg1,reg2,reg3,reg4,reg5,reg6;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 16));
        __GLOBALS__[0] = reg2;
        
            reg3 = __MEMORY_READ_8__(mem_0,reg0+4);
            if reg3~=0 then reg1 = 1; goto block_8_fin; end;
            reg3 = __MEMORY_READ_32__(mem_0,reg0);
            reg4 = reg3;
            reg3 = __MEMORY_READ_8__(mem_0,reg0+5);
            if ((reg3 == 0) and 1 or 0)==0 then goto if_20_fin end 
                reg3 = __MEMORY_READ_32__(mem_0,reg4+24);
                reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 28)));
                reg6 = __MEMORY_READ_32__(mem_0,reg5+12);
                reg5 = __TABLE_FUNCS_0__[reg6+1](reg3,1055434,7);
                reg1 = reg5; goto block_8_fin;
            ::if_20_fin::
            reg3 = __MEMORY_READ_8__(mem_0,reg4);
            if (((bit_band(reg3,4)) == 0) and 1 or 0)==0 then goto if_38_fin end 
                reg3 = __MEMORY_READ_32__(mem_0,reg4+24);
                reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 28)));
                reg6 = __MEMORY_READ_32__(mem_0,reg5+12);
                reg5 = __TABLE_FUNCS_0__[reg6+1](reg3,1055428,6);
                reg1 = reg5; goto block_8_fin;
            ::if_38_fin::
            __MEMORY_WRITE_8__(mem_0,reg2+15,1);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 8)),(bit_tobit(reg2 + 15)));
            reg3 = __LONG_INT__(0,0); reg3:load(mem_0,reg4+24);
            (reg3):store(mem_0,reg2);
            reg3 = __FUNCS__.func_30(reg2,1055424,3);
            if reg3~=0 then reg1 = 1; goto block_8_fin; end;
            reg3 = __MEMORY_READ_32__(mem_0,reg4+24);
            reg5 = __MEMORY_READ_32__(mem_0,reg4+28);
            reg4 = __MEMORY_READ_32__(mem_0,reg5+12);
            reg4 = __TABLE_FUNCS_0__[reg4+1](reg3,1055427,1);
            reg1 = reg4
            -- BLOCK RET (block):
        ::block_8_fin::
        reg3 = reg0;
        reg0 = reg1;
        __MEMORY_WRITE_8__(mem_0,reg3+4,reg0);
        __GLOBALS__[0] = (bit_tobit(reg2 + 16));
        do return reg0; end;
    end
    function __FUNCS__.func_68(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 48));
        __GLOBALS__[0] = reg3;
        reg2 = (bit_tobit(reg1 + 4));
        reg4 = __MEMORY_READ_32__(mem_0,reg1+4);
        if ((reg4 == 0) and 1 or 0)==0 then goto if_14_fin end 
            reg4 = __MEMORY_READ_32__(mem_0,reg1);
            reg1 = reg4;
            (__LONG_INT__(0,0)):store(mem_0,reg3+12);
            reg4 = __MEMORY_READ_32__(mem_0,1049400);
            __MEMORY_WRITE_32__(mem_0,reg3+8,reg4);
            __MEMORY_WRITE_32__(mem_0,reg3+20,(bit_tobit(reg3 + 8)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg1 + 16)));
            (reg4):store(mem_0,(bit_tobit(reg3 + 40)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,(bit_tobit(reg1 + 8)));
            (reg4):store(mem_0,(bit_tobit(reg3 + 32)));
            reg4 = __LONG_INT__(0,0); reg4:load(mem_0,reg1);
            (reg4):store(mem_0,reg3+24);
            reg1 = __FUNCS__.func_27((bit_tobit(reg3 + 20)),1048944,(bit_tobit(reg3 + 24)));
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 16)));
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg2 + 8)),reg1);
            reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg3+8);
            (reg1):store(mem_0,reg2);
        ::if_14_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+4,1051084);
        __MEMORY_WRITE_32__(mem_0,reg0,reg2);
        __GLOBALS__[0] = (bit_tobit(reg3 + 48));
    end
    function __FUNCS__.func_69(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg3;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = __FUNCS__.func_32(reg3,reg1,reg2);
        reg3 = reg4;
        reg2 = ((reg3)[1]);
        reg4 = (bit_band(reg2,255));
        if ((reg4 ~= 4) and 1 or 0)==0 then goto if_18_fin end 
            reg5 = __MEMORY_READ_8__(mem_0,reg0+4);
            if ((reg5 == 3) and 1 or 0)==0 then goto if_23_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                reg1 = reg5;
                reg5 = __MEMORY_READ_32__(mem_0,reg1);
                reg6 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg7 = __MEMORY_READ_32__(mem_0,reg6);
                __TABLE_FUNCS_0__[reg7+1](reg5);
                reg5 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg6 = reg5;
                reg5 = __MEMORY_READ_32__(mem_0,reg6+4);
                if reg5==0 then goto if_38_fin end 
                    reg5 = __MEMORY_READ_32__(mem_0,reg6+8);
                    reg5 = __MEMORY_READ_32__(mem_0,reg1);
                    __FUNCS__.func_10(reg5);
                ::if_38_fin::
                __FUNCS__.func_10(reg1);
            ::if_23_fin::
            __MEMORY_WRITE_8__(mem_0,reg0+4,reg2);
            reg1 = (reg3):_shr_u(__LONG_INT__(8,0));
            reg3 = reg1;
            (((reg3):_shr_u(__LONG_INT__(48,0)))):store8(mem_0,(bit_tobit(reg0 + 11)));
            (((reg3):_shr_u(__LONG_INT__(32,0)))):store16(mem_0,(bit_tobit(reg0 + 9)));
            (reg3):store32(mem_0,(bit_tobit(reg0 + 5)));
        ::if_18_fin::
        do return ((reg4 ~= 4) and 1 or 0); end;
    end
    function __FUNCS__.func_70(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = __FUNCS__.func_32(reg3,reg1,reg2);
        reg3 = reg4;
        reg2 = ((reg3)[1]);
        reg4 = (bit_band(reg2,255));
        if ((reg4 ~= 4) and 1 or 0)==0 then goto if_16_fin end 
            reg5 = __MEMORY_READ_8__(mem_0,reg0+4);
            if ((reg5 == 3) and 1 or 0)==0 then goto if_21_fin end 
                reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
                reg1 = reg5;
                reg5 = __MEMORY_READ_32__(mem_0,reg1);
                reg6 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg7 = __MEMORY_READ_32__(mem_0,reg6);
                __TABLE_FUNCS_0__[reg7+1](reg5);
                reg5 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg6 = reg5;
                reg5 = __MEMORY_READ_32__(mem_0,reg6+4);
                if reg5==0 then goto if_36_fin end 
                    reg5 = __MEMORY_READ_32__(mem_0,reg6+8);
                    reg5 = __MEMORY_READ_32__(mem_0,reg1);
                    __FUNCS__.func_10(reg5);
                ::if_36_fin::
                __FUNCS__.func_10(reg1);
            ::if_21_fin::
            __MEMORY_WRITE_8__(mem_0,reg0+4,reg2);
            reg1 = (reg3):_shr_u(__LONG_INT__(8,0));
            reg3 = reg1;
            (((reg3):_shr_u(__LONG_INT__(48,0)))):store8(mem_0,(bit_tobit(reg0 + 11)));
            (((reg3):_shr_u(__LONG_INT__(32,0)))):store16(mem_0,(bit_tobit(reg0 + 9)));
            (reg3):store32(mem_0,(bit_tobit(reg0 + 5)));
        ::if_16_fin::
        do return ((reg4 ~= 4) and 1 or 0); end;
    end
    function __FUNCS__.func_71(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6,reg7;
        
            
                
                    
                        
                            
                                reg5 = 1;
                                if ((reg1 < 0) and 1 or 0)~=0 then reg4 = reg5; goto block_7_fin; end;
                                reg6 = __MEMORY_READ_32__(mem_0,reg2);
                                reg7 = reg6;
                                if ((reg7 == 0) and 1 or 0)~=0 then goto block_5_fin; end;
                                reg6 = __MEMORY_READ_32__(mem_0,reg2+4);
                                reg2 = reg6;
                                if reg2~=0 then goto block_6_fin; end;
                                if reg1~=0 then goto block_4_fin; end;
                                reg3 = 1; goto block_3_fin;
                                reg4 = error('unreachable')
                                -- BLOCK RET (block):
                            ::block_7_fin::
                            reg5 = reg4;
                            reg1 = 0;
                            goto block_2_fin;
                        ::block_6_fin::
                        reg4 = __FUNCS__.func_144(reg7,reg1);
                        reg3 = reg4; goto block_3_fin;
                    ::block_5_fin::
                    if reg1~=0 then goto block_4_fin; end;
                    reg3 = 1; goto block_3_fin;
                ::block_4_fin::
                reg4 = __FUNCS__.func_148(reg1,1);
                reg3 = reg4
                -- BLOCK RET (block):
            ::block_3_fin::
            reg2 = reg3;
            if reg2==0 then goto if_49_fin end 
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg2);
                reg5 = 0;
                goto block_2_fin;
            ::if_49_fin::
            __MEMORY_WRITE_32__(mem_0,reg0+4,reg1);
            reg1 = 1;
        ::block_2_fin::
        __MEMORY_WRITE_32__(mem_0,reg0,reg5);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),reg1);
    end
    function __FUNCS__.func_72(reg0, reg1)
        local reg2,reg3,reg4,reg5;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_8__(mem_0,reg0);
        reg4 = reg2;
        reg0 = 0;
        
        while true do ::loop_12_start::
            reg2 = (bit_band(reg4,15));
            
            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg0 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg2) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg2)));
            reg5 = bit_tobit(reg0 + -1);
            reg0 = reg5;
            reg2 = reg4;
            reg4 = (bit_rshift(reg2,4));
            if ((__UNSIGNED__(reg2) > __UNSIGNED__(15)) and 1 or 0)~=0 then goto loop_12_start; end;
            break
        end
        
        reg4 = (bit_tobit(reg0 + 128));
        if ((__UNSIGNED__(reg4) >= __UNSIGNED__(129)) and 1 or 0)==0 then goto if_50_fin end 
            __FUNCS__.func_83(reg4,128,1055476);
            error('unreachable');
        ::if_50_fin::
        reg2 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg0 + reg3)) + 128)),(bit_tobit(0 - reg0)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 128));
        do return reg2; end;
    end
    function __FUNCS__.func_73(reg0, reg1)
        local reg2,reg3,reg4,reg5;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_8__(mem_0,reg0);
        reg4 = reg2;
        reg0 = 0;
        
        while true do ::loop_12_start::
            reg2 = (bit_band(reg4,15));
            
            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg0 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg2) < __UNSIGNED__(10)) and 1 or 0) == 0) and 55 or 48) + reg2)));
            reg5 = bit_tobit(reg0 + -1);
            reg0 = reg5;
            reg2 = reg4;
            reg4 = (bit_rshift(reg2,4));
            if ((__UNSIGNED__(reg2) > __UNSIGNED__(15)) and 1 or 0)~=0 then goto loop_12_start; end;
            break
        end
        
        reg4 = (bit_tobit(reg0 + 128));
        if ((__UNSIGNED__(reg4) >= __UNSIGNED__(129)) and 1 or 0)==0 then goto if_50_fin end 
            __FUNCS__.func_83(reg4,128,1055476);
            error('unreachable');
        ::if_50_fin::
        reg2 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg0 + reg3)) + 128)),(bit_tobit(0 - reg0)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 128));
        do return reg2; end;
    end
    function __FUNCS__.func_74(reg0, reg1)
        local reg2,reg3,reg4,reg5;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        -- FORCE INIT VAR | i32
        reg2 = 0;
        -- FORCE INIT VAR | i32
        reg2 = 0;
        
        while true do ::loop_10_start::
            reg4 = (bit_band(reg0,15));
            
            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg2 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 87 or 48) + reg4)));
            reg4 = bit_tobit(reg2 + -1);
            reg2 = reg4;
            reg4 = bit_rshift(reg0,4);
            reg5 = (__UNSIGNED__(reg0) > __UNSIGNED__(15)) and 1 or 0;
            reg0 = reg4;
            if reg5~=0 then goto loop_10_start; end;
            break
        end
        
        reg0 = (bit_tobit(reg2 + 128));
        if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)==0 then goto if_47_fin end 
            __FUNCS__.func_83(reg0,128,1055476);
            error('unreachable');
        ::if_47_fin::
        reg0 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg2 + reg3)) + 128)),(bit_tobit(0 - reg2)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 128));
        do return reg0; end;
    end
    function __FUNCS__.func_75(reg0, reg1)
        local reg2,reg3,reg4,reg5;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 128));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        -- FORCE INIT VAR | i32
        reg2 = 0;
        -- FORCE INIT VAR | i32
        reg2 = 0;
        
        while true do ::loop_10_start::
            reg4 = (bit_band(reg0,15));
            
            __MEMORY_WRITE_8__(mem_0,(bit_tobit((bit_tobit(reg2 + reg3)) + 127)),(bit_tobit(((((__UNSIGNED__(reg4) < __UNSIGNED__(10)) and 1 or 0) == 0) and 55 or 48) + reg4)));
            reg4 = bit_tobit(reg2 + -1);
            reg2 = reg4;
            reg4 = bit_rshift(reg0,4);
            reg5 = (__UNSIGNED__(reg0) > __UNSIGNED__(15)) and 1 or 0;
            reg0 = reg4;
            if reg5~=0 then goto loop_10_start; end;
            break
        end
        
        reg0 = (bit_tobit(reg2 + 128));
        if ((__UNSIGNED__(reg0) >= __UNSIGNED__(129)) and 1 or 0)==0 then goto if_47_fin end 
            __FUNCS__.func_83(reg0,128,1055476);
            error('unreachable');
        ::if_47_fin::
        reg0 = __FUNCS__.func_13(reg1,1,1055492,2,(bit_tobit((bit_tobit(reg2 + reg3)) + 128)),(bit_tobit(0 - reg2)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 128));
        do return reg0; end;
    end
    function __FUNCS__.func_76(reg0)
        local reg1,reg2,reg3,reg4,reg5;
        reg1 = __MEMORY_READ_8__(mem_0,reg0+8);
        reg2 = reg1;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
        reg3 = reg1;
        if reg3==0 then goto if_8_fin end 
            reg1 = bit_band(reg2,255);
            reg2 = reg1;
            
                if reg2~=0 then reg1 = 1; goto block_14_fin; end;
                
                    if ((reg3 ~= 1) and 1 or 0)~=0 then goto block_19_fin; end;
                    reg4 = __MEMORY_READ_8__(mem_0,reg0+9);
                    if ((reg4 == 0) and 1 or 0)~=0 then goto block_19_fin; end;
                    reg4 = __MEMORY_READ_32__(mem_0,reg0);
                    reg3 = reg4;
                    reg4 = __MEMORY_READ_8__(mem_0,reg3);
                    if (bit_band(reg4,4))~=0 then goto block_19_fin; end;
                    reg4 = __MEMORY_READ_32__(mem_0,reg3+24);
                    reg5 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 28)));
                    reg3 = __MEMORY_READ_32__(mem_0,reg5+12);
                    reg3 = __TABLE_FUNCS_0__[reg3+1](reg4,1055444,1);
                    if reg3~=0 then reg1 = 1; goto block_14_fin; end;
                ::block_19_fin::
                reg3 = __MEMORY_READ_32__(mem_0,reg0);
                reg2 = reg3;
                reg3 = __MEMORY_READ_32__(mem_0,reg2+24);
                reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg2 + 28)));
                reg5 = __MEMORY_READ_32__(mem_0,reg4+12);
                reg4 = __TABLE_FUNCS_0__[reg5+1](reg3,1055445,1);
                reg1 = reg4
                -- BLOCK RET (block):
            ::block_14_fin::
            reg2 = reg1;
            __MEMORY_WRITE_8__(mem_0,reg0+8,reg2);
        ::if_8_fin::
        do return (((bit_band(reg2,255)) ~= 0) and 1 or 0); end;
    end
    function __FUNCS__.func_77(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg4;
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
        reg5 = reg3;
        
            
                
                    
                        reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
                        
                        if reg6 == 0 then goto block_15_fin;
                        elseif reg6 == 1 then goto block_14_fin;
                        else goto block_12_fin;
                        end
                    ::block_15_fin::
                    if reg5~=0 then goto block_12_fin; end;
                    reg0 = 0;
                    reg3 = 1049032; goto block_13_fin;
                ::block_14_fin::
                if reg5~=0 then goto block_12_fin; end;
                reg6 = __MEMORY_READ_32__(mem_0,reg0);
                reg5 = reg6;
                reg6 = __MEMORY_READ_32__(mem_0,reg5+4);
                reg0 = reg6;
                reg6 = __MEMORY_READ_32__(mem_0,reg5);
                reg3 = reg6
                -- BLOCK RET (block):
            ::block_13_fin::
            reg5 = reg3;
            __MEMORY_WRITE_32__(mem_0,reg4+4,reg0);
            __MEMORY_WRITE_32__(mem_0,reg4,reg5);
            reg3 = __MEMORY_READ_32__(mem_0,reg1+8);
            __FUNCS__.func_63(reg4,1051064,reg3,reg2);
            error('unreachable');
        ::block_12_fin::
        __MEMORY_WRITE_32__(mem_0,reg4+4,0);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        reg0 = __MEMORY_READ_32__(mem_0,reg1+8);
        __FUNCS__.func_63(reg4,1051044,reg0,reg2);
        error('unreachable');
    end
    function __FUNCS__.func_78(reg0, reg1, reg2)
        local reg3,reg4,reg5;
        
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            reg4 = reg3;
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
            reg5 = reg3;
            if ((__UNSIGNED__((bit_tobit(reg4 - reg5))) >= __UNSIGNED__(reg2)) and 1 or 0)~=0 then goto block_2_fin; end;
            if ((reg5 == 0) and 1 or 0)==0 then goto if_19_fin end 
                reg5 = 0;
                goto block_2_fin;
            ::if_19_fin::
            reg5 = 0;
            __MEMORY_WRITE_8__(mem_0,reg0+12,0);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),0);
        ::block_2_fin::
        if ((__UNSIGNED__(reg4) > __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_38_fin end 
            reg3 = __MEMORY_READ_32__(mem_0,reg0);
            reg4 = __FUNCS__.func_64((bit_tobit(reg3 + reg5)),reg1,reg2);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + 8)),(bit_tobit(reg2 + reg5)));
            do return __LONG_INT__(4,0) end
        ::if_38_fin::
        __MEMORY_WRITE_8__(mem_0,reg0+12,0);
        do return __LONG_INT__(4,0); end;
    end
    function __FUNCS__.func_79(reg0, reg1, reg2, reg3, reg4)
        local reg5,reg6;
        reg5 = __GLOBALS__[0];
        reg6 = (bit_tobit(reg5 + -64));
        __GLOBALS__[0] = reg6;
        __MEMORY_WRITE_32__(mem_0,reg6+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg6+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg6+20,reg3);
        __MEMORY_WRITE_32__(mem_0,reg6+16,reg2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 44)),2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg6 + 60)),52);
        (__LONG_INT__(2,0)):store(mem_0,reg6+28);
        __MEMORY_WRITE_32__(mem_0,reg6+24,1055312);
        __MEMORY_WRITE_32__(mem_0,reg6+52,51);
        __MEMORY_WRITE_32__(mem_0,reg6+40,(bit_tobit(reg6 + 48)));
        __MEMORY_WRITE_32__(mem_0,reg6+56,(bit_tobit(reg6 + 16)));
        __MEMORY_WRITE_32__(mem_0,reg6+48,(bit_tobit(reg6 + 8)));
        __FUNCS__.func_122((bit_tobit(reg6 + 24)),reg4);
        error('unreachable');
    end
    function __FUNCS__.func_80(reg0, reg1)
        local reg2,reg3,reg4,reg5,reg6;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = 1;
        
            reg4 = __FUNCS__.func_48(reg0,reg1);
            if reg4~=0 then goto block_9_fin; end;
            reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
            reg5 = reg4;
            reg4 = __MEMORY_READ_32__(mem_0,reg1+24);
            __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg3 + 28)),0);
            __MEMORY_WRITE_32__(mem_0,reg3+24,1054920);
            (__LONG_INT__(1,0)):store(mem_0,reg3+12);
            __MEMORY_WRITE_32__(mem_0,reg3+8,1054984);
            reg6 = __FUNCS__.func_27(reg4,reg5,(bit_tobit(reg3 + 8)));
            if reg6~=0 then goto block_9_fin; end;
            reg4 = __FUNCS__.func_48((bit_tobit(reg0 + 4)),reg1);
            reg2 = reg4;
        ::block_9_fin::
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg2; end;
    end
    function __FUNCS__.func_81(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
        reg4 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        reg2 = __FUNCS__.func_133(reg1);
        (reg2):store(mem_0,reg3);
        if reg4==0 then goto if_22_fin end 
            
            while true do ::loop_23_start::
                __MEMORY_WRITE_32__(mem_0,reg3+12,reg0);
                __FUNCS__.func_55(reg3,(bit_tobit(reg3 + 12)));
                reg1 = bit_tobit(reg0 + 1);
                reg0 = reg1;
                reg1 = bit_tobit(reg4 + -1);
                reg4 = reg1;
                if reg4~=0 then goto loop_23_start; end;
                break
            end
            
        ::if_22_fin::
        reg1 = __FUNCS__.func_123(reg3);
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg1; end;
    end
    function __FUNCS__.func_82(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 28)),2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 44)),1);
        (__LONG_INT__(2,0)):store(mem_0,reg4+12);
        __MEMORY_WRITE_32__(mem_0,reg4+8,1055136);
        __MEMORY_WRITE_32__(mem_0,reg4+36,1);
        __MEMORY_WRITE_32__(mem_0,reg4+24,(bit_tobit(reg4 + 32)));
        __MEMORY_WRITE_32__(mem_0,reg4+40,reg4);
        __MEMORY_WRITE_32__(mem_0,reg4+32,(bit_tobit(reg4 + 4)));
        __FUNCS__.func_122((bit_tobit(reg4 + 8)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_83(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 28)),2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 44)),1);
        (__LONG_INT__(2,0)):store(mem_0,reg4+12);
        __MEMORY_WRITE_32__(mem_0,reg4+8,1055988);
        __MEMORY_WRITE_32__(mem_0,reg4+36,1);
        __MEMORY_WRITE_32__(mem_0,reg4+24,(bit_tobit(reg4 + 32)));
        __MEMORY_WRITE_32__(mem_0,reg4+40,(bit_tobit(reg4 + 4)));
        __MEMORY_WRITE_32__(mem_0,reg4+32,reg4);
        __FUNCS__.func_122((bit_tobit(reg4 + 8)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_84(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 28)),2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 44)),1);
        (__LONG_INT__(2,0)):store(mem_0,reg4+12);
        __MEMORY_WRITE_32__(mem_0,reg4+8,1056020);
        __MEMORY_WRITE_32__(mem_0,reg4+36,1);
        __MEMORY_WRITE_32__(mem_0,reg4+24,(bit_tobit(reg4 + 32)));
        __MEMORY_WRITE_32__(mem_0,reg4+40,(bit_tobit(reg4 + 4)));
        __MEMORY_WRITE_32__(mem_0,reg4+32,reg4);
        __FUNCS__.func_122((bit_tobit(reg4 + 8)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_85(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 28)),2);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 44)),1);
        (__LONG_INT__(2,0)):store(mem_0,reg4+12);
        __MEMORY_WRITE_32__(mem_0,reg4+8,1056072);
        __MEMORY_WRITE_32__(mem_0,reg4+36,1);
        __MEMORY_WRITE_32__(mem_0,reg4+24,(bit_tobit(reg4 + 32)));
        __MEMORY_WRITE_32__(mem_0,reg4+40,(bit_tobit(reg4 + 4)));
        __MEMORY_WRITE_32__(mem_0,reg4+32,reg4);
        __FUNCS__.func_122((bit_tobit(reg4 + 8)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_86(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
        reg4 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+24);
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg0 + 16)));
        (reg1):store(mem_0,(bit_tobit(reg3 + 24)));
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,(bit_tobit(reg0 + 8)));
        (reg1):store(mem_0,(bit_tobit(reg3 + 16)));
        reg1 = __LONG_INT__(0,0); reg1:load(mem_0,reg0);
        (reg1):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27(reg2,reg4,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_87(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg4 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27(reg2,reg4,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_88(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+4,1049588);
        __MEMORY_WRITE_32__(mem_0,reg3,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        __FUNCS__.func_41(reg3,1049368,(bit_tobit(reg3 + 4)),1049368,(bit_tobit(reg3 + 8)),1051684);
        error('unreachable');
    end
    function __FUNCS__.func_89(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 32));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,1050768);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg4 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg4 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg4+8);
        __FUNCS__.func_41(reg4,1049384,(bit_tobit(reg4 + 4)),1049384,(bit_tobit(reg4 + 8)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_90(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 32));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg2 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg4 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg2 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg4 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg2);
        (reg0):store(mem_0,reg4+8);
        __FUNCS__.func_41(reg4,1055152,(bit_tobit(reg4 + 4)),1055152,(bit_tobit(reg4 + 8)),1051972);
        error('unreachable');
    end
    function __FUNCS__.func_91(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg2);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1048992,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_92(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg2);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1048968,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_93(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg2);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1048944,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_94(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg2);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1055696,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_95(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1048968,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_96(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1048992,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_97(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 32));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+4,reg0);
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 16)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 24)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,(bit_tobit(reg1 + 8)));
        (reg0):store(mem_0,(bit_tobit(reg3 + 16)));
        reg0 = __LONG_INT__(0,0); reg0:load(mem_0,reg1);
        (reg0):store(mem_0,reg3+8);
        reg0 = __FUNCS__.func_27((bit_tobit(reg3 + 4)),1055696,(bit_tobit(reg3 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg3 + 32));
        do return reg0; end;
    end
    function __FUNCS__.func_98(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg1 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        reg0 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg1,0);
        
            if reg0==0 then goto if_11_fin end 
                reg2 = __FUNCS__.func_148(1024,1);
                reg1 = reg2;
                if ((reg1 == 0) and 1 or 0)~=0 then goto block_9_fin; end;
                reg2 = __MEMORY_READ_32__(mem_0,reg0);
                reg0 = reg2;
                __MEMORY_WRITE_8__(mem_0,reg0+16,0);
                (__LONG_INT__(1024,0)):store(mem_0,reg0+8);
                __MEMORY_WRITE_32__(mem_0,reg0+4,reg1);
                __MEMORY_WRITE_32__(mem_0,reg0,0);
                do return  end
            ::if_11_fin::
            __FUNCS__.func_110(1049216,43,1050616);
            error('unreachable');
        ::block_9_fin::
        __FUNCS__.func_170(1024,1);
        error('unreachable');
    end
    function __FUNCS__.func_99(reg0, reg1, reg2, reg3, reg4)
        local reg5;
        
            reg5 = reg1 - reg3;
            reg3 = reg5;
            if ((reg3):_gt_u(reg1) and 1 or 0)~=0 then goto block_1_fin; end;
            
                if ((__UNSIGNED__(reg2) >= __UNSIGNED__(reg4)) and 1 or 0)==0 then goto if_13_fin end 
                    reg1 = reg3;
                    goto block_9_fin;
                ::if_13_fin::
                reg1 = (reg3 + __LONG_INT__(-1,-1));
                if ((reg1):_gt_u(reg3) and 1 or 0)~=0 then goto block_1_fin; end;
                reg3 = bit_tobit(reg2 + 1000000000);
                reg2 = reg3;
            ::block_9_fin::
            (reg1):store(mem_0,reg0);
            __MEMORY_WRITE_32__(mem_0,reg0+8,(bit_tobit(reg2 - reg4)));
            do return  end
        ::block_1_fin::
        __FUNCS__.func_101(1050815,35,1050876);
        error('unreachable');
    end
    function __FUNCS__.func_100(reg0)
        local reg1,reg2;
        
            reg1 = __MEMORY_READ_32__(mem_0,reg0+16);
            reg2 = reg1;
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            __MEMORY_WRITE_8__(mem_0,reg2,0);
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
            if ((reg1 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg0+16);
            __FUNCS__.func_10(reg1);
        ::block_2_fin::
        
            if ((reg0 == -1) and 1 or 0)~=0 then goto block_21_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
            reg2 = reg1;
            __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_tobit(reg2 + -1)));
            if ((reg2 ~= 1) and 1 or 0)~=0 then goto block_21_fin; end;
            __FUNCS__.func_10(reg0);
        ::block_21_fin::
    end
    function __FUNCS__.func_101(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 48));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4+8,reg0);
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 36)),1);
        (__LONG_INT__(1,0)):store(mem_0,reg4+20);
        __MEMORY_WRITE_32__(mem_0,reg4+16,1055060);
        __MEMORY_WRITE_32__(mem_0,reg4+44,51);
        __MEMORY_WRITE_32__(mem_0,reg4+32,(bit_tobit(reg4 + 40)));
        __MEMORY_WRITE_32__(mem_0,reg4+40,(bit_tobit(reg4 + 8)));
        __FUNCS__.func_122((bit_tobit(reg4 + 16)),reg2);
        error('unreachable');
    end
    function __FUNCS__.func_102(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        __FUNCS__.func_117(reg3,reg1);
        __MEMORY_WRITE_32__(mem_0,reg3+12,reg0);
        __FUNCS__.func_53(reg3,(bit_tobit(reg3 + 12)),1049384);
        __MEMORY_WRITE_32__(mem_0,reg3+12,(bit_tobit(reg0 + 4)));
        __FUNCS__.func_53(reg3,(bit_tobit(reg3 + 12)),1051144);
        reg0 = __FUNCS__.func_76(reg3);
        __GLOBALS__[0] = (bit_tobit(reg3 + 16));
        do return reg0; end;
    end
    function __FUNCS__.func_103(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = __MEMORY_READ_32__(mem_0,reg3);
        reg3 = reg4;
        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg3 + 4)));
        reg5 = (bit_tobit(reg3 + 8));
        reg6 = __MEMORY_READ_32__(mem_0,reg5);
        reg0 = reg6;
        if ((__UNSIGNED__((bit_tobit(reg4 - reg0))) < __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_18_fin end 
            __FUNCS__.func_66(reg3,reg0,reg2);
            reg4 = __MEMORY_READ_32__(mem_0,reg5);
            reg0 = reg4;
        ::if_18_fin::
        reg4 = __MEMORY_READ_32__(mem_0,reg3);
        reg3 = __FUNCS__.func_64((bit_tobit(reg4 + reg0)),reg1,reg2);
        __MEMORY_WRITE_32__(mem_0,reg5,(bit_tobit(reg0 + reg2)));
        do return 0; end;
    end
    function __FUNCS__.func_104(reg0, reg1, reg2)
        local reg3,reg4,reg5,reg6;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg4 = reg3;
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg4 + 4)));
        reg5 = (bit_tobit(reg4 + 8));
        reg6 = __MEMORY_READ_32__(mem_0,reg5);
        reg0 = reg6;
        if ((__UNSIGNED__((bit_tobit(reg3 - reg0))) < __UNSIGNED__(reg2)) and 1 or 0)==0 then goto if_17_fin end 
            __FUNCS__.func_66(reg4,reg0,reg2);
            reg3 = __MEMORY_READ_32__(mem_0,reg5);
            reg0 = reg3;
        ::if_17_fin::
        reg3 = __MEMORY_READ_32__(mem_0,reg4);
        reg4 = __FUNCS__.func_64((bit_tobit(reg3 + reg0)),reg1,reg2);
        __MEMORY_WRITE_32__(mem_0,reg5,(bit_tobit(reg0 + reg2)));
        do return 0; end;
    end
    function __FUNCS__.func_105(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        reg3 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg1,0);
        
            if reg3==0 then goto if_10_fin end 
                reg2 = __MEMORY_READ_32__(mem_0,reg1+4);
                reg4 = reg2;
                reg2 = __FUNCS__.func_148(8,4);
                reg1 = reg2;
                if ((reg1 == 0) and 1 or 0)~=0 then goto block_8_fin; end;
                __MEMORY_WRITE_32__(mem_0,reg1+4,reg4);
                __MEMORY_WRITE_32__(mem_0,reg1,reg3);
                __MEMORY_WRITE_32__(mem_0,reg0+4,1051100);
                __MEMORY_WRITE_32__(mem_0,reg0,reg1);
                do return  end
            ::if_10_fin::
            error('unreachable');
        ::block_8_fin::
        __FUNCS__.func_170(8,4);
        error('unreachable');
    end
    function __FUNCS__.func_106(reg0)
        local reg1,reg2;
        
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 16)));
            if ((reg1 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
            reg2 = reg1;
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            __FUNCS__.func_10(reg2);
        ::block_2_fin::
        
            if ((reg0 == -1) and 1 or 0)~=0 then goto block_17_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
            reg2 = reg1;
            __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_tobit(reg2 + -1)));
            if ((reg2 ~= 1) and 1 or 0)~=0 then goto block_17_fin; end;
            __FUNCS__.func_10(reg0);
        ::block_17_fin::
    end
    function __FUNCS__.func_107(reg0)
        local reg1,reg2,reg3,reg4;
        reg1 = __MEMORY_READ_8__(mem_0,reg0+4);
        if ((reg1 == 3) and 1 or 0)==0 then goto if_6_fin end 
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
            reg2 = reg1;
            reg1 = __MEMORY_READ_32__(mem_0,reg2);
            reg3 = __MEMORY_READ_32__(mem_0,reg2+4);
            reg4 = __MEMORY_READ_32__(mem_0,reg3);
            __TABLE_FUNCS_0__[reg4+1](reg1);
            reg1 = __MEMORY_READ_32__(mem_0,reg2+4);
            reg3 = reg1;
            reg1 = __MEMORY_READ_32__(mem_0,reg3+4);
            if reg1==0 then goto if_21_fin end 
                reg1 = __MEMORY_READ_32__(mem_0,reg3+8);
                reg1 = __MEMORY_READ_32__(mem_0,reg2);
                __FUNCS__.func_10(reg1);
            ::if_21_fin::
            reg1 = __MEMORY_READ_32__(mem_0,reg0+8);
            __FUNCS__.func_10(reg1);
        ::if_6_fin::
    end
    function __FUNCS__.func_108(reg0, reg1, reg2, reg3)
        local reg4,reg5,reg6,reg7;
        
            
                if ((reg1 ~= 1114112) and 1 or 0)==0 then goto if_6_fin end 
                    reg5 = __MEMORY_READ_32__(mem_0,reg0+24);
                    reg6 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
                    reg7 = __MEMORY_READ_32__(mem_0,reg6+16);
                    reg6 = __TABLE_FUNCS_0__[reg7+1](reg5,reg1);
                    if reg6~=0 then reg4 = 1; goto block_2_fin; end;
                ::if_6_fin::
                if reg2~=0 then goto block_1_fin; end;
                reg4 = 0
                -- BLOCK RET (block):
            ::block_2_fin::
            do return reg4 end
        ::block_1_fin::
        reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg4 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg0 = __MEMORY_READ_32__(mem_0,reg4+12);
        reg0 = __TABLE_FUNCS_0__[reg0+1](reg1,reg2,reg3);
        do return reg0; end;
    end
    function __FUNCS__.func_109(reg0, reg1, reg2, reg3)
        local reg4,reg5;
        if ((reg3 == 0) and 1 or 0)==0 then goto if_4_fin end 
            __FUNCS__.func_101(1056388,53,1056444);
            error('unreachable');
        ::if_4_fin::
        reg4 = (__LONG_INT__(reg3,0));
        reg5 = ((reg1):_div_u(reg4));
        (reg5):store(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0+8,(bit_tobit(((((((reg1 - (reg4 * reg5)) * __LONG_INT__(1000000000,0))):_div_u(reg4)))[1]) + (__IDIV_U__(reg2,reg3)))));
    end
    function __FUNCS__.func_110(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 32));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg4 + 20)),0);
        __MEMORY_WRITE_32__(mem_0,reg4+16,1054920);
        (__LONG_INT__(1,0)):store(mem_0,reg4+4);
        __MEMORY_WRITE_32__(mem_0,reg4+28,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4+24,reg0);
        __MEMORY_WRITE_32__(mem_0,reg4,(bit_tobit(reg4 + 24)));
        __FUNCS__.func_122(reg4,reg2);
        error('unreachable');
    end
    function __FUNCS__.func_111(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+4);
        reg3 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        reg4 = reg2;
        reg2 = __FUNCS__.func_148(8,4);
        reg1 = reg2;
        if ((reg1 == 0) and 1 or 0)==0 then goto if_13_fin end 
            __FUNCS__.func_170(8,4);
            error('unreachable');
        ::if_13_fin::
        __MEMORY_WRITE_32__(mem_0,reg1+4,reg3);
        __MEMORY_WRITE_32__(mem_0,reg1,reg4);
        __MEMORY_WRITE_32__(mem_0,reg0+4,1051100);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
    end
    function __FUNCS__.func_112(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        reg3 = (bit_band(reg2,1));
        reg2 = __MEMORY_READ_32F__(mem_0,reg0);
        reg0 = reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+16);
        if ((reg2 == 1) and 1 or 0)==0 then goto if_15_fin end 
            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 20)));
            reg4 = __FUNCS__.func_14(reg1,reg0,reg3,reg2);
            do return reg4 end
        ::if_15_fin::
        reg2 = __FUNCS__.func_23(reg1,reg0,reg3);
        do return reg2; end;
    end
    function __FUNCS__.func_113(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_GROW__(mem_0,__UNSIGNED__((bit_rshift(reg1,16)))); 
        reg3 = reg2;
        __MEMORY_WRITE_32__(mem_0,reg0+8,0);
        reg2 = bit_band(reg1,-65536);
        reg1 = ((reg3 == -1) and 1 or 0);
        
        __MEMORY_WRITE_32__(mem_0,reg0+4,((reg1 == 0) and reg2 or 0));
        
        __MEMORY_WRITE_32__(mem_0,reg0,((reg1 == 0) and (bit_lshift(reg3,16)) or 0));
    end
    function __FUNCS__.func_114(reg0)
        local reg1,reg2,reg3,reg4;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 16));
        __GLOBALS__[0] = reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
        reg3 = reg1;
        if ((reg3 == 0) and 1 or 0)==0 then goto if_11_fin end 
            __FUNCS__.func_110(1049216,43,1051012);
            error('unreachable');
        ::if_11_fin::
        reg1 = __MEMORY_READ_32__(mem_0,reg0+8);
        reg4 = reg1;
        if ((reg4 == 0) and 1 or 0)==0 then goto if_22_fin end 
            __FUNCS__.func_110(1049216,43,1051028);
            error('unreachable');
        ::if_22_fin::
        __MEMORY_WRITE_32__(mem_0,reg2+8,reg3);
        __MEMORY_WRITE_32__(mem_0,reg2+4,reg0);
        __MEMORY_WRITE_32__(mem_0,reg2,reg4);
        reg0 = __MEMORY_READ_32__(mem_0,reg2);
        reg1 = __MEMORY_READ_32__(mem_0,reg2+4);
        reg3 = __MEMORY_READ_32__(mem_0,reg2+8);
        __FUNCS__.func_77(reg0,reg1,reg3);
        error('unreachable');
    end
    function __FUNCS__.func_115(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        reg2 = __FUNCS__.func_153(reg1);
        if ((reg2 == 0) and 1 or 0)==0 then goto if_7_fin end 
            reg2 = __FUNCS__.func_154(reg1);
            if ((reg2 == 0) and 1 or 0)==0 then goto if_11_fin end 
                reg2 = __FUNCS__.func_161(reg0,reg1);
                do return reg2 end
            ::if_11_fin::
            reg2 = __FUNCS__.func_75(reg0,reg1);
            do return reg2 end
        ::if_7_fin::
        reg2 = __FUNCS__.func_74(reg0,reg1);
        do return reg2; end;
    end
    function __FUNCS__.func_116(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        reg2 = __FUNCS__.func_153(reg1);
        if ((reg2 == 0) and 1 or 0)==0 then goto if_7_fin end 
            reg2 = __FUNCS__.func_154(reg1);
            if ((reg2 == 0) and 1 or 0)==0 then goto if_11_fin end 
                reg2 = __MEMORY_READ_8__(mem_0,reg0);reg2=__LONG_INT__(reg2,0);
                reg3 = __FUNCS__.func_46(reg2,1,reg1);
                do return reg3 end
            ::if_11_fin::
            reg2 = __FUNCS__.func_73(reg0,reg1);
            do return reg2 end
        ::if_7_fin::
        reg2 = __FUNCS__.func_72(reg0,reg1);
        do return reg2; end;
    end
    function __FUNCS__.func_117(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+24);
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
        reg4 = __MEMORY_READ_32__(mem_0,reg3+12);
        reg3 = __TABLE_FUNCS_0__[reg4+1](reg2,1051136,8);
        __MEMORY_WRITE_8__(mem_0,reg0+8,reg3);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
        __MEMORY_WRITE_8__(mem_0,reg0+9,0);
        __MEMORY_WRITE_32__(mem_0,reg0+4,0);
    end
    function __FUNCS__.func_118(reg0)
        local reg1,reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        reg2 = reg1;
        
            reg1 = __MEMORY_READ_8__(mem_0,reg0+4);
            if reg1~=0 then goto block_5_fin; end;
            reg0 = __MEMORY_READ_32__(mem_0,1059144);
            if (((bit_band(reg0,2147483647)) == 0) and 1 or 0)~=0 then goto block_5_fin; end;
            reg0 = __FUNCS__.func_134();
            if reg0~=0 then goto block_5_fin; end;
            __MEMORY_WRITE_8__(mem_0,reg2+1,1);
        ::block_5_fin::
        __MEMORY_WRITE_8__(mem_0,reg2,0);
    end
    function __FUNCS__.func_119(reg0)
        local reg1,reg2;
        reg1 = __GLOBALS__[0];
        reg2 = (bit_tobit(reg1 - 16));
        __GLOBALS__[0] = reg2;
        __MEMORY_WRITE_32__(mem_0,reg2+12,1050472);
        __MEMORY_WRITE_32__(mem_0,reg2+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg2+4,1049072);
        __MEMORY_WRITE_32__(mem_0,reg2,1049032);
        __FUNCS__.func_114(reg2);
        error('unreachable');
    end
    function __FUNCS__.func_120(reg0, reg1)
        local reg2;
        reg2 = __GLOBALS__[0];
        reg0 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg0;
        reg2 = __FUNCS__.func_132(reg1);
        (reg2):store(mem_0,reg0+8);
        reg1 = __FUNCS__.func_67((bit_tobit(reg0 + 8)));
        __GLOBALS__[0] = (bit_tobit(reg0 + 16));
        do return reg1; end;
    end
    function __FUNCS__.func_121(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0+4);
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor((bit_bor((bit_band(reg2,1)),reg1)),2)));
        reg2 = bit_tobit((bit_tobit(reg0 + reg1)) + 4);
        reg0 = reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0,(bit_bor(reg1,1)));
    end
    function __FUNCS__.func_122(reg0, reg1)
        local reg2,reg3;
        reg2 = __GLOBALS__[0];
        reg3 = (bit_tobit(reg2 - 16));
        __GLOBALS__[0] = reg3;
        __MEMORY_WRITE_32__(mem_0,reg3+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg3+8,reg0);
        __MEMORY_WRITE_32__(mem_0,reg3+4,1055068);
        __MEMORY_WRITE_32__(mem_0,reg3,1054920);
        __FUNCS__.func_114(reg3);
        error('unreachable');
    end
    function __FUNCS__.func_123(reg0)
        local reg1,reg2,reg3;
        reg1 = 1;
        reg2 = __MEMORY_READ_8__(mem_0,reg0+4);
        if reg2==0 then goto if_6_else end 
            reg2 = reg1
        goto if_6_fin
        ::if_6_else::
            reg1 = __MEMORY_READ_32__(mem_0,reg0);
            reg0 = reg1;
            reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
            reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
            reg0 = __MEMORY_READ_32__(mem_0,reg3+12);
            reg0 = __TABLE_FUNCS_0__[reg0+1](reg1,1055448,1);
            reg2 = reg0
            -- BLOCK RET (if):
        ::if_6_fin::
        do return reg2; end;
    end
    function __FUNCS__.func_124(reg0)
        local reg1;
        
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
            if ((reg1 == 0) and 1 or 0)~=0 then goto block_1_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            reg0 = reg1;
            if ((reg0 == 0) and 1 or 0)~=0 then goto block_1_fin; end;
            __FUNCS__.func_10(reg0);
        ::block_1_fin::
    end
    function __FUNCS__.func_125(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+12,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4+8,reg0);
        __FUNCS__.func_63((bit_tobit(reg4 + 8)),1051116,0,reg2);
        error('unreachable');
    end
    function __FUNCS__.func_126(reg0, reg1, reg2)
        local reg3,reg4;
        reg3 = __GLOBALS__[0];
        reg4 = (bit_tobit(reg3 - 16));
        __GLOBALS__[0] = reg4;
        __MEMORY_WRITE_32__(mem_0,reg4+8,reg2);
        __MEMORY_WRITE_32__(mem_0,reg4+4,reg1);
        __MEMORY_WRITE_32__(mem_0,reg4,reg0);
        reg0 = __MEMORY_READ_32__(mem_0,reg4);
        reg1 = __MEMORY_READ_32__(mem_0,reg4+4);
        reg2 = __MEMORY_READ_32__(mem_0,reg4+8);
        __FUNCS__.func_125(reg0,reg1,reg2);
        error('unreachable');
    end
    function __FUNCS__.func_127(reg0, reg1)
        local reg2,reg3,reg4;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = reg2;
        reg2 = (reg0 > -1) and 1 or 0;
        reg3 = (__LONG_INT__((bit_bxor(reg0,-1)),bit_arshift((bit_bxor(reg0,-1)),31))) + __LONG_INT__(1,0);
        reg4 = __LONG_INT__(reg0,0);
        reg0 = reg2;
        
        reg2 = __FUNCS__.func_46(((reg0 == 0) and reg3 or reg4),reg0,reg1);
        do return reg2; end;
    end
    function __FUNCS__.func_128(reg0)
        local reg1;
        
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 4)));
            if ((reg1 == 0) and 1 or 0)~=0 then goto block_1_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,reg0);
            reg0 = reg1;
            if ((reg0 == 0) and 1 or 0)~=0 then goto block_1_fin; end;
            __FUNCS__.func_10(reg0);
        ::block_1_fin::
    end
    function __FUNCS__.func_129(reg0)
        local reg1,reg2;
        
            reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
            reg2 = reg1;
            if ((reg2 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            reg1 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
            if ((reg1 == 0) and 1 or 0)~=0 then goto block_2_fin; end;
            __FUNCS__.func_10(reg2);
        ::block_2_fin::
    end
    function __FUNCS__.func_130(reg0, reg1)
        local reg2;
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg1,3)));
        reg2 = bit_tobit((bit_tobit(reg0 + reg1)) + 4);
        reg0 = reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        __MEMORY_WRITE_32__(mem_0,reg0,(bit_bor(reg1,1)));
    end
    function __FUNCS__.func_131(reg0, reg1, reg2)
        local reg3;
        reg3 = __MEMORY_READ_32__(mem_0,reg2+4);
        __MEMORY_WRITE_32__(mem_0,reg2+4,(bit_band(reg3,-2)));
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg1,1)));
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + reg1)),reg1);
    end
    function __FUNCS__.func_132(reg0)
        local reg1,reg2,reg3;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg3 = __MEMORY_READ_32__(mem_0,reg2+12);
        reg2 = __TABLE_FUNCS_0__[reg3+1](reg1,1050804,11);
        
        do return (((__LONG_INT__(reg0,0))):_or(((reg2 == 0) and __LONG_INT__(0,0) or __LONG_INT__(0,1)))); end;
    end
    function __FUNCS__.func_133(reg0)
        local reg1,reg2,reg3;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+24);
        reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 28)));
        reg3 = __MEMORY_READ_32__(mem_0,reg2+12);
        reg2 = __TABLE_FUNCS_0__[reg3+1](reg1,1055447,1);
        
        do return (((__LONG_INT__(reg0,0))):_or(((reg2 == 0) and __LONG_INT__(0,0) or __LONG_INT__(0,1)))); end;
    end
    function __FUNCS__.func_134()
        local reg0;
        reg0 = __MEMORY_READ_32__(mem_0,1059648);
        if ((reg0 == 1) and 1 or 0)==0 then goto if_5_fin end 
            reg0 = __MEMORY_READ_32__(mem_0,1059652);
            do return ((reg0 == 0) and 1 or 0) end
        ::if_5_fin::
        (__LONG_INT__(1,0)):store(mem_0,1059648);
        do return 1; end;
    end
    function __FUNCS__.func_135(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_8__(mem_0,reg0);
        if ((reg2 == 0) and 1 or 0)==0 then goto if_4_fin end 
            reg0 = __FUNCS__.func_8(reg1,1055848,5);
            do return reg0 end
        ::if_4_fin::
        reg0 = __FUNCS__.func_8(reg1,1055844,4);
        do return reg0; end;
    end
    function __FUNCS__.func_136()
        __FUNCS__.func_110(1051700,28,1051808);
        error('unreachable');
    end
    function __FUNCS__.func_137(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg1);
        if ((reg2 == 0) and 1 or 0)==0 then goto if_4_fin end 
            error('unreachable');
        ::if_4_fin::
        __MEMORY_WRITE_32__(mem_0,reg0+4,1051100);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
    end
    function __FUNCS__.func_138(reg0)
        local reg1,reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+16);
        reg2 = reg1;
        if reg2==0 then goto if_5_else end 
            reg1 = reg2
        goto if_5_fin
        ::if_5_else::
            reg2 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 20)));
            reg1 = reg2
            -- BLOCK RET (if):
        ::if_5_fin::
        do return reg1; end;
    end
    function __FUNCS__.func_139(reg0)
        
        do return ((((reg0 == 31) and 1 or 0) == 0) and (bit_tobit(25 - (bit_rshift(reg0,1)))) or 0); end;
    end
    function __FUNCS__.func_140(reg0, reg1)
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg1,1)));
        __MEMORY_WRITE_32__(mem_0,(bit_tobit(reg0 + reg1)),reg1);
    end
    function __FUNCS__.func_141(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+24);
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
        reg1 = __MEMORY_READ_32__(mem_0,reg3+12);
        reg1 = __TABLE_FUNCS_0__[reg1+1](reg2,1054992,11);
        do return reg1; end;
    end
    function __FUNCS__.func_142(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg1+24);
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg1 + 28)));
        reg1 = __MEMORY_READ_32__(mem_0,reg3+12);
        reg1 = __TABLE_FUNCS_0__[reg1+1](reg2,1055003,14);
        do return reg1; end;
    end
    function __FUNCS__.func_143(reg0, reg1)
        do return (bit_band((bit_tobit((bit_tobit(reg0 + reg1)) + -1)),(bit_tobit(0 - reg1)))); end;
    end
    function __FUNCS__.func_144(reg0, reg1)
        local reg2;
        reg2 = __FUNCS__.func_18(reg0,reg1);
        do return reg2; end;
    end
    function __FUNCS__.func_145(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = __MEMORY_READ_32__(mem_0,(bit_tobit(reg0 + 8)));
        reg0 = __FUNCS__.func_171(reg2,reg3,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_146(reg0)
        local reg1;
        reg1 = bit_lshift(reg0,1);
        reg0 = reg1;
        do return (bit_bor(reg0,(bit_tobit(0 - reg0)))); end;
    end
    function __FUNCS__.func_147(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = __MEMORY_READ_32__(mem_0,reg0+4);
        reg0 = __MEMORY_READ_32__(mem_0,reg3+12);
        reg0 = __TABLE_FUNCS_0__[reg0+1](reg2,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_148(reg0, reg1)
        local reg2;
        reg2 = __FUNCS__.func_38(reg0,reg1);
        do return reg2; end;
    end
    function __FUNCS__.func_149(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = __MEMORY_READ_32__(mem_0,reg0+4);
        reg0 = __FUNCS__.func_171(reg2,reg3,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_150(reg0, reg1)
        __MEMORY_WRITE_32__(mem_0,reg0+4,1051100);
        __MEMORY_WRITE_32__(mem_0,reg0,reg1);
    end
    function __FUNCS__.func_151(reg0)
        local reg1;
        reg1 = __MEMORY_READ_8__(mem_0,reg0+4);
        do return (bit_rshift((bit_band(reg1,2)),1)); end;
    end
    function __FUNCS__.func_152(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg3 = __MEMORY_READ_32__(mem_0,reg0+4);
        reg0 = __FUNCS__.func_8(reg1,reg2,reg3);
        do return reg0; end;
    end
    function __FUNCS__.func_153(reg0)
        local reg1;
        reg1 = __MEMORY_READ_8__(mem_0,reg0);
        do return (bit_rshift((bit_band(reg1,16)),4)); end;
    end
    function __FUNCS__.func_154(reg0)
        local reg1;
        reg1 = __MEMORY_READ_8__(mem_0,reg0);
        do return (bit_rshift((bit_band(reg1,32)),5)); end;
    end
    function __FUNCS__.func_155(reg0)
        do return (bit_band((bit_tobit(0 - reg0)),reg0)); end;
    end
    function __FUNCS__.func_156(reg0)
        local reg1;
        reg1 = __MEMORY_READ_8__(mem_0,reg0+4);
        do return (((bit_band(reg1,3)) == 0) and 1 or 0); end;
    end
    function __FUNCS__.func_157(reg0, reg1)
        __MEMORY_WRITE_32__(mem_0,reg0+4,(bit_bor(reg1,3)));
    end
    function __FUNCS__.func_158(reg0)
        local reg1,reg2;
        reg1 = __MEMORY_READ_32__(mem_0,reg0);
        reg2 = __MEMORY_READ_32__(mem_0,reg0+4);
        do return (bit_tobit(reg1 + reg2)); end;
    end
    function __FUNCS__.func_159()
        __FUNCS__.func_110(1051856,17,1051876);
        error('unreachable');
    end
    function __FUNCS__.func_160(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        
        while true do ::loop_4_start::
            goto loop_4_start;
            break
        end
        
        error('unreachable');
    end
    function __FUNCS__.func_161(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);reg2=__LONG_INT__(reg2,0);
        reg0 = __FUNCS__.func_46(reg2,1,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_162(reg0, reg1, reg2)
        local reg3;
        reg3 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = __FUNCS__.func_30(reg3,reg1,reg2);
        do return reg0; end;
    end
    function __FUNCS__.func_163(reg0, reg1)
        local reg2;
        reg2 = __LONG_INT__(0,0); reg2:load(mem_0,reg0);
        reg0 = __FUNCS__.func_46(reg2,1,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_164(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = __FUNCS__.func_135(reg2,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_165(reg0, reg1)
        local reg2;
        reg2 = __MEMORY_READ_32__(mem_0,reg0);
        reg0 = __FUNCS__.func_40(reg2,reg1);
        do return reg0; end;
    end
    function __FUNCS__.func_166(reg0)
        local reg1;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
        do return (bit_band(reg1,-8)); end;
    end
    function __FUNCS__.func_167(reg0)
        local reg1;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+4);
        do return (bit_band(reg1,1)); end;
    end
    function __FUNCS__.func_168(reg0)
        local reg1;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
        do return (bit_band(reg1,1)); end;
    end
    function __FUNCS__.func_169(reg0)
        local reg1;
        reg1 = __MEMORY_READ_32__(mem_0,reg0+12);
        do return (bit_rshift(reg1,1)); end;
    end
    function __FUNCS__.func_170(reg0, reg1)
        local reg2,reg3;
        reg2 = __MEMORY_READ_32__(mem_0,1059128);
        reg3 = reg0;
        reg0 = reg2;
        
        __TABLE_FUNCS_0__[((reg0 == 0) and 9 or reg0)+1](reg3,reg1);
        error('unreachable');
    end
    function __FUNCS__.func_171(reg0, reg1, reg2)
        local reg3;
        reg3 = __FUNCS__.func_8(reg2,reg0,reg1);
        do return reg3; end;
    end
    function __FUNCS__.func_172(reg0, reg1)
        do return (bit_tobit(reg0 + reg1)); end;
    end
    function __FUNCS__.func_173(reg0, reg1)
        do return (bit_tobit(reg0 - reg1)); end;
    end
    function __FUNCS__.func_174(reg0)
        do return (bit_tobit(reg0 + 8)); end;
    end
    function __FUNCS__.func_175(reg0)
        do return (bit_tobit(reg0 + -8)); end;
    end
    function __FUNCS__.func_176()
        __FUNCS__.func_126(1051404,37,1051488);
        error('unreachable');
    end
    function __FUNCS__.func_177(reg0)
        do return __LONG_INT__(-322454284,2129832222); end;
    end
    function __FUNCS__.func_178(reg0)
        do return __LONG_INT__(783569176,-1948699795); end;
    end
    function __FUNCS__.func_179(reg0)
        do return __LONG_INT__(-2102833991,-70897127); end;
    end
    function __FUNCS__.func_180(reg0)
    end
    function __FUNCS__.func_181(reg0, reg1)
    end
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+0] = __FUNCS__.func_161;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+1] = __FUNCS__.func_49;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+2] = __FUNCS__.func_127;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+3] = __FUNCS__.func_135;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+4] = __FUNCS__.func_112;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+5] = __FUNCS__.func_145;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+6] = __FUNCS__.func_149;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+7] = __FUNCS__.func_20;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+8] = __FUNCS__.func_181;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+9] = __FUNCS__.func_180;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+10] = __FUNCS__.func_104;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+11] = __FUNCS__.func_44;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+12] = __FUNCS__.func_93;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+13] = __FUNCS__.func_103;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+14] = __FUNCS__.func_50;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+15] = __FUNCS__.func_92;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+16] = __FUNCS__.func_69;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+17] = __FUNCS__.func_165;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+18] = __FUNCS__.func_91;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+19] = __FUNCS__.func_116;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+20] = __FUNCS__.func_178;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+21] = __FUNCS__.func_142;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+22] = __FUNCS__.func_124;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+23] = __FUNCS__.func_102;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+24] = __FUNCS__.func_141;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+25] = __FUNCS__.func_118;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+26] = __FUNCS__.func_120;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+27] = __FUNCS__.func_164;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+28] = __FUNCS__.func_115;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+29] = __FUNCS__.func_107;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+30] = __FUNCS__.func_70;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+31] = __FUNCS__.func_40;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+32] = __FUNCS__.func_96;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+33] = __FUNCS__.func_104;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+34] = __FUNCS__.func_51;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+35] = __FUNCS__.func_95;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+36] = __FUNCS__.func_98;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+37] = __FUNCS__.func_98;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+38] = __FUNCS__.func_129;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+39] = __FUNCS__.func_57;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+40] = __FUNCS__.func_68;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+41] = __FUNCS__.func_111;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+42] = __FUNCS__.func_150;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+43] = __FUNCS__.func_128;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+44] = __FUNCS__.func_179;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+45] = __FUNCS__.func_177;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+46] = __FUNCS__.func_105;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+47] = __FUNCS__.func_137;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+48] = __FUNCS__.func_81;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+49] = __FUNCS__.func_160;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+50] = __FUNCS__.func_152;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+51] = __FUNCS__.func_147;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+52] = __FUNCS__.func_86;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+53] = __FUNCS__.func_80;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+54] = __FUNCS__.func_35;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+55] = __FUNCS__.func_163;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+56] = __FUNCS__.func_180;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+57] = __FUNCS__.func_178;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+58] = __FUNCS__.func_33;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+59] = __FUNCS__.func_30;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+60] = __FUNCS__.func_61;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+61] = __FUNCS__.func_97;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+62] = __FUNCS__.func_162;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+63] = __FUNCS__.func_59;
    __TABLE_FUNCS_0__[__TABLE_OFFSET_0_0__+64] = __FUNCS__.func_94;
    __EXPORTS__["memory"] = mem_0;
    __EXPORTS__["add"] = __FUNCS__.func_172;
    __EXPORTS__["main"] = __FUNCS__.func_5;
    
    function module.init()
    end
end

return module
