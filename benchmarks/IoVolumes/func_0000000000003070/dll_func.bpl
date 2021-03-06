/* Bitvector operations */
function {:bvbuiltin "bvand"} AND_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvor"} OR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvxor"} XOR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvnot"} NOT_1(p1: bv1) : bv1;

function {:bvbuiltin "bvadd"} PLUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsub"} MINUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmul"} TIMES_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmod"} MOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsmod"} SMOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvshl"} LSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvlshr"} RSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvashr"} ARSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvand"} AND_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvor"} OR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvxor"} XOR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvult"} LT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvule"} LE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvugt"} GT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvuge"} GE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvslt"} SLT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvsle"} SLE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvneg"} NEG_8(p1: bv8) : bv8;
function {:bvbuiltin "bvnot"} NOT_8(p1: bv8) : bv8;

function {:bvbuiltin "bvadd"} PLUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsub"} MINUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmul"} TIMES_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmod"} MOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsmod"} SMOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvshl"} LSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvlshr"} RSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvashr"} ARSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvand"} AND_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvor"} OR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvxor"} XOR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvult"} LT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvule"} LE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvugt"} GT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvuge"} GE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvslt"} SLT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvsle"} SLE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvneg"} NEG_16(p1: bv16) : bv16;
function {:bvbuiltin "bvnot"} NOT_16(p1: bv16) : bv16;

function {:bvbuiltin "bvadd"} PLUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsub"} MINUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmul"} TIMES_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmod"} MOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsmod"} SMOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvshl"} LSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvlshr"} RSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvashr"} ARSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvand"} AND_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvor"} OR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvxor"} XOR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvult"} LT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvule"} LE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvugt"} GT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvuge"} GE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvslt"} SLT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvsle"} SLE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvneg"} NEG_32(p1: bv32) : bv32;
function {:bvbuiltin "bvnot"} NOT_32(p1: bv32) : bv32;

function {:bvbuiltin "bvadd"} PLUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsub"} MINUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmul"} TIMES_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmod"} MOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsmod"} SMOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvshl"} LSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvlshr"} RSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvashr"} ARSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvand"} AND_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvor"} OR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvxor"} XOR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvult"} LT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvule"} LE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvugt"} GT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvuge"} GE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvslt"} SLT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvsle"} SLE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvneg"} NEG_64(p1: bv64) : bv64;
function {:bvbuiltin "bvnot"} NOT_64(p1: bv64) : bv64;

function {:bvbuiltin "bvmul"} TIMES_128(p1: bv128, p2: bv128) : bv128;

/* Helpers */
function {:inline} bv2bool(x: bv1): bool { if (x == 0bv1) then false else true }
function {:inline} bool2bv(x: bool): bv1 { if (!x) then 0bv1 else 1bv1 }

/* Memory Model */
type virtual_addr_t = bv64;
type data_t = bv8;
type mem_t = [virtual_addr_t] data_t;

function {:inline} STORE_LE_8(mem : mem_t, addr : virtual_addr_t, value : bv8) : mem_t
  { mem[addr := value] }
function {:inline} STORE_LE_16(mem : mem_t, addr : virtual_addr_t, value : bv16) : mem_t
  {  STORE_LE_8(STORE_LE_8(mem, addr, value[8:0]), PLUS_64(addr, 1bv64), value[16:8]) }
function {:inline} STORE_LE_32(mem: mem_t, addr: virtual_addr_t, value: bv32) : mem_t
  { STORE_LE_16(STORE_LE_16(mem, addr, value[16:0]), PLUS_64(addr, 2bv64), value[32:16]) }
function {:inline} STORE_LE_64(mem: mem_t, addr: virtual_addr_t, value: bv64) : mem_t
  { STORE_LE_32(STORE_LE_32(mem, addr, value[32:0]), PLUS_64(addr, 4bv64), value[64:32]) }

function {:inline} LOAD_LE_8(mem: mem_t, addr: virtual_addr_t) : bv8
  { mem[addr] }
function {:inline} LOAD_LE_16(mem: mem_t, addr: virtual_addr_t) : bv16
  { LOAD_LE_8(mem, PLUS_64(addr, 1bv64)) ++ LOAD_LE_8(mem, addr) }
function {:inline} LOAD_LE_32(mem: mem_t, addr: virtual_addr_t) : bv32
  { LOAD_LE_16(mem, PLUS_64(addr, 2bv64)) ++ LOAD_LE_16(mem, addr) }
function {:inline} LOAD_LE_64(mem: mem_t, addr: virtual_addr_t) : bv64
  { LOAD_LE_32(mem, PLUS_64(addr, 4bv64)) ++ LOAD_LE_32(mem, addr) }

function REP_STOSB(mem: mem_t, rcx: bv64, rdi: bv64, al: bv8) : mem_t;
//This axiom assumes that direction flag is cleared, which is the assumption made by CRT, /guard, etc.
axiom (forall mem: mem_t, rcx: bv64, rdi: bv64, al: bv8 :: {REP_STOSB(mem, rcx, rdi, al)}
  (forall i : bv64 :: (GE_64(i, rdi) && LT_64(i, PLUS_64(rdi, rcx)) ==> REP_STOSB(mem, rcx, rdi, al)[i] == al) && 
                     (LT_64(i, rdi) || GE_64(i, PLUS_64(rdi, rcx)) ==> REP_STOSB(mem, rcx, rdi, al)[i] == mem[i])));


function {:inline} ITE_1(b : bool,  x : bv1,   y : bv1) : bv1 { if (b) then x else y }
function {:inline} ITE_8(b : bool,  x : bv8,   y : bv8) : bv8 { if (b) then x else y }
function {:inline} ITE_16(b : bool, x : bv16, y : bv16) : bv16 { if (b) then x else y }
function {:inline} ITE_32(b : bool, x : bv32, y : bv32) : bv32 { if (b) then x else y }
function {:inline} ITE_64(b : bool, x : bv64, y : bv64) : bv64 { if (b) then x else y }
function {:inline} ITE_128(b : bool, x : bv128, y : bv128) : bv128 { if (b) then x else y }

function {:inline} addrInBitmap(x: bv64) : bool { GE_64(x, _bitmap_low) && LT_64(x, _bitmap_high) }
function {:inline} addrInStack(x: bv64) : bool { GE_64(x, _stack_low) && LT_64(x, _stack_high) }

function {:inline} addrToBitmapAddrByte(addr: bv64) : bv64 {
  PLUS_64(RSHIFT_64(MINUS_64(addr, _virtual_address_space_low), 6bv64), _bitmap_low)
}

function {:inline} addrToBitmapAddrBit(addr: bv64) : bv8 {
  0bv5 ++ (RSHIFT_64(AND_64(MINUS_64(addr, _virtual_address_space_low), 63bv64), 3bv64))[3:0]
}

function {:inline} writable(mem: [bv64] bv8, addr: bv64) : bool
{
  bv2bool((RSHIFT_8(AND_8(LOAD_LE_8(mem, addrToBitmapAddrByte(addr)), LSHIFT_8(1bv8, addrToBitmapAddrBit(addr))), addrToBitmapAddrBit(addr)))[1:0])
}

function {:inline} anyAddrAffected_64(mem: [bv64] bv8, addr: bv64, new_value: bv64) : bool { LOAD_LE_64(mem, addr) != new_value }
function {:inline} anyAddrAffected_32(mem: [bv64] bv8, addr: bv64, new_value: bv32) : bool { LOAD_LE_32(mem, addr) != new_value }
function {:inline} anyAddrAffected_16(mem: [bv64] bv8, addr: bv64, new_value: bv16) : bool { LOAD_LE_16(mem, addr) != new_value }
function {:inline} anyAddrAffected_8 (mem: [bv64] bv8, addr: bv64, new_value: bv8)  : bool { LOAD_LE_8(mem, addr)  != new_value }

/* computes the largest address affected in an 8-bit update 
   use this only if addr is within the bitmap and the update produces a new value (anyAddrAffected)
*/
function {:inline} largestAddrAffected_8(mem: [bv64] bv8, addr: bv64, new_value: bv8) : bv64
{
  PLUS_64(_virtual_address_space_low, PLUS_64(LSHIFT_64(MINUS_64(addr, _bitmap_low), 6bv64), 
  (
    if (new_value[8:7] != LOAD_LE_8(mem, addr)[8:7]) then ( 63bv64 ) else (
    if (new_value[7:6] != LOAD_LE_8(mem, addr)[7:6]) then ( 55bv64 ) else (
    if (new_value[6:5] != LOAD_LE_8(mem, addr)[6:5]) then ( 47bv64 ) else (
    if (new_value[5:4] != LOAD_LE_8(mem, addr)[5:4]) then ( 39bv64 ) else (
    if (new_value[4:3] != LOAD_LE_8(mem, addr)[4:3]) then ( 31bv64 ) else (
    if (new_value[3:2] != LOAD_LE_8(mem, addr)[3:2]) then ( 23bv64 ) else (
    if (new_value[2:1] != LOAD_LE_8(mem, addr)[2:1]) then ( 15bv64 ) else ( 
    7bv64 
    )))))))
  )))
}

/* computes the smallest address affected in an 8-bit update 
   use this only if addr is within the bitmap and the update produces a new value (anyAddrAffected)
*/
function {:inline} smallestAddrAffected_8(mem: [bv64] bv8, addr: bv64, new_value: bv8) : bv64
{
  PLUS_64(_virtual_address_space_low, PLUS_64(LSHIFT_64(MINUS_64(addr, _bitmap_low), 6bv64), 
  (
    if (new_value[1:0] != LOAD_LE_8(mem, addr)[1:0]) then ( 0bv64 ) else (
    if (new_value[2:1] != LOAD_LE_8(mem, addr)[2:1]) then ( 8bv64 ) else (
    if (new_value[3:2] != LOAD_LE_8(mem, addr)[3:2]) then ( 16bv64 ) else (
    if (new_value[4:3] != LOAD_LE_8(mem, addr)[4:3]) then ( 24bv64 ) else (
    if (new_value[5:4] != LOAD_LE_8(mem, addr)[5:4]) then ( 32bv64 ) else (
    if (new_value[6:5] != LOAD_LE_8(mem, addr)[6:5]) then ( 40bv64 ) else (
    if (new_value[7:6] != LOAD_LE_8(mem, addr)[7:6]) then ( 48bv64 ) else ( 
    56bv64 
    )))))))
  )))
}


const _guard_writeTable_ptr : bv64;
const _guard_callTable_ptr : bv64;
const _bitmap_low : bv64;
const _bitmap_high : bv64;
const _stack_low : bv64;
const _stack_high : bv64;
const _virtual_address_space_low : bv64;
const _virtual_address_space_high : bv64;
const _function_addr_low : bv64;
const _function_addr_high : bv64;
axiom _guard_writeTable_ptr == 29136bv64;
axiom _guard_callTable_ptr == 29152bv64;
axiom _function_addr_low == 12400bv64;
axiom _function_addr_high == 12796bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x3070:
t_1 := AND_64(RDX, RDX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1, 4bv64)), t_1)), 2bv64)), (XOR_64((RSHIFT_64(t_1, 4bv64)), t_1)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1, 4bv64)), t_1)), 2bv64)), (XOR_64((RSHIFT_64(t_1, 4bv64)), t_1)))))[1:0]));
SF := t_1[64:63];
ZF := bool2bv(0bv64 == t_1);

label_0x3073:
if (bv2bool(ZF)) {
  goto label_0x31fb;
}

label_0x3079:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RBX);

label_0x307e:
t_5 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x307f:
t_7 := RSP;
RSP := MINUS_64(RSP, 32bv64);
CF := bool2bv(LT_64(t_7, 32bv64));
OF := AND_64((XOR_64(t_7, 32bv64)), (XOR_64(t_7, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_7)), 32bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3083:
t_11 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RCX, 8bv64))), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RCX, 8bv64))), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RCX, 8bv64))), 0bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RCX, 8bv64))), t_11)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_11, (LOAD_LE_8(mem, PLUS_64(RCX, 8bv64))))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)), 2bv8)), (XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)), 2bv8)), (XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)))))[1:0]));
SF := t_11[8:7];
ZF := bool2bv(0bv8 == t_11);

label_0x3087:
RDI := RDX;

label_0x308a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RBP);

label_0x308f:
RBX := RCX;

label_0x3092:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RSI);

label_0x3097:
if (bv2bool(ZF)) {
  goto label_0x30a7;
}

label_0x3099:
t_15 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RCX, 24bv64))), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RCX, 24bv64))), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RCX, 24bv64))), 0bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RCX, 24bv64))), t_15)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_15, (LOAD_LE_8(mem, PLUS_64(RCX, 24bv64))))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)), 2bv8)), (XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)), 2bv8)), (XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)))))[1:0]));
SF := t_15[8:7];
ZF := bool2bv(0bv8 == t_15);

label_0x309d:
if (bv2bool(ZF)) {
  goto label_0x30a7;
}

label_0x309f:
RCX := LOAD_LE_64(mem, RCX);

label_0x30a2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12455bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f70"} true;
call arbitrary_func();

label_0x30a7:
RDX := OR_64(RDX, 4294967295bv32 ++ 4294967295bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x30ab:


label_0x30b0:
t_21 := RDX;
RDX := PLUS_64(RDX, 1bv64);
OF := AND_1((bool2bv((t_21[64:63]) == (1bv64[64:63]))), (XOR_1((t_21[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t_21)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x30b3:
t_25 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RDI, RDX))), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RDI, RDX))), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RDI, RDX))), 0bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RDI, RDX))), t_25)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_25, (LOAD_LE_8(mem, PLUS_64(RDI, RDX))))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)), 2bv8)), (XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)), 2bv8)), (XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)))))[1:0]));
SF := t_25[8:7];
ZF := bool2bv(0bv8 == t_25);

label_0x30b7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x30b0;
}

label_0x30b9:
RAX := PLUS_64(RBX, 16bv64)[64:0];

label_0x30bd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30c3:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30c9:
if (bv2bool(ZF)) {
  goto label_0x30cc;
}

label_0x30cb:
assume false;

label_0x30cc:
RSI := LOAD_LE_64(mem, PLUS_64((PLUS_64(16637bv64, 12499bv64)), 0bv64));

label_0x30d3:
RCX := PLUS_64(RBX, 16bv64)[64:0];

label_0x30d7:
origDEST_33 := RCX;
origCOUNT_34 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, LSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), origDEST_33[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_6);

label_0x30db:
RAX := PLUS_64(RBX, 16bv64)[64:0];

label_0x30df:
origDEST_39 := RAX;
origCOUNT_40 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), CF, LSHIFT_64(origDEST_39, (MINUS_64(64bv64, origCOUNT_40)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv64)), origDEST_39[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), AF, unconstrained_8);

label_0x30e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RCX, 3bv64))));

label_0x30e7:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_9;
SF := unconstrained_10;
AF := unconstrained_11;
PF := unconstrained_12;

label_0x30eb:
if (bv2bool(CF)) {
  goto label_0x30ee;
}

label_0x30ed:
assume false;

label_0x30ee:
RCX := PLUS_64(RDX, 1bv64)[64:0];

label_0x30f2:
mem := STORE_LE_64(mem, PLUS_64(RBX, 16bv64), RDX);

label_0x30f6:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12539bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f60"} true;
call arbitrary_func();

label_0x30fb:
RCX := RBX;

label_0x30fe:
RBP := RAX;

label_0x3101:
RCX := AND_64(RCX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3108:
RCX := XOR_64(RCX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x310f:
if (bv2bool(ZF)) {
  goto label_0x3112;
}

label_0x3111:
assume false;

label_0x3112:
RCX := RBX;

label_0x3115:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_16);

label_0x3119:
RDX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RCX, 3bv64))));

label_0x311d:
RCX := RBX;

label_0x3120:
origDEST_55 := RCX;
origCOUNT_56 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_18);

label_0x3124:
CF := RSHIFT_64(RDX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_19;
SF := unconstrained_20;
AF := unconstrained_21;
PF := unconstrained_22;

label_0x3128:
if (bv2bool(CF)) {
  goto label_0x312b;
}

label_0x312a:
assume false;

label_0x312b:
mem := STORE_LE_64(mem, RBX, RAX);

label_0x312e:
RAX := PLUS_64(RBX, 24bv64)[64:0];

label_0x3132:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3138:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x313e:
if (bv2bool(ZF)) {
  goto label_0x3141;
}

label_0x3140:
assume false;

label_0x3141:
RAX := PLUS_64(RBX, 24bv64)[64:0];

label_0x3145:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_26);

label_0x3149:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x314d:
RAX := PLUS_64(RBX, 24bv64)[64:0];

label_0x3151:
origDEST_71 := RAX;
origCOUNT_72 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_28);

label_0x3155:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_29;
SF := unconstrained_30;
AF := unconstrained_31;
PF := unconstrained_32;

label_0x3159:
if (bv2bool(CF)) {
  goto label_0x315c;
}

label_0x315b:
assume false;

label_0x315c:
RDX := LOAD_LE_64(mem, PLUS_64(RBX, 16bv64));

label_0x3160:
RCX := RBP;

label_0x3163:
mem := STORE_LE_8(mem, PLUS_64(RBX, 24bv64), 1bv8);

label_0x3167:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12652bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x25b0"} true;
call arbitrary_func();

label_0x316c:
R8 := LOAD_LE_64(mem, PLUS_64(RBX, 16bv64));

label_0x3170:
RDX := RDI;

label_0x3173:
RCX := RBP;

label_0x3176:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12667bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3bb0"} true;
call arbitrary_func();

label_0x317b:
RDX := LOAD_LE_64(mem, PLUS_64(RBX, 16bv64));

label_0x317f:
R8 := LOAD_LE_64(mem, RBX);

label_0x3182:
RBP := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3187:
RAX := PLUS_64(RDX, R8)[64:0];

label_0x318b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3191:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3197:
if (bv2bool(ZF)) {
  goto label_0x319a;
}

label_0x3199:
assume false;

label_0x319a:
RAX := PLUS_64(RDX, R8)[64:0];

label_0x319e:
origDEST_81 := RAX;
origCOUNT_82 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_36);

label_0x31a2:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x31a6:
RAX := PLUS_64(RDX, R8)[64:0];

label_0x31aa:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, LSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), origDEST_87[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_38);

label_0x31ae:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x31b2:
if (bv2bool(CF)) {
  goto label_0x31b5;
}

label_0x31b4:
assume false;

label_0x31b5:
RAX := PLUS_64(RBX, 8bv64)[64:0];

label_0x31b9:
mem := STORE_LE_8(mem, PLUS_64(RDX, R8), 0bv8);

label_0x31be:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31c4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31ca:
if (bv2bool(ZF)) {
  goto label_0x31cd;
}

label_0x31cc:
assume false;

label_0x31cd:
RAX := PLUS_64(RBX, 8bv64)[64:0];

label_0x31d1:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_46);

label_0x31d5:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x31d9:
RAX := PLUS_64(RBX, 8bv64)[64:0];

label_0x31dd:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x31e2:
origDEST_103 := RAX;
origCOUNT_104 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_48);

label_0x31e6:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x31ea:
if (bv2bool(CF)) {
  goto label_0x31ed;
}

label_0x31ec:
assume false;

label_0x31ed:
mem := STORE_LE_8(mem, PLUS_64(RBX, 8bv64), 1bv8);

label_0x31f1:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x31f6:
t1_109 := RSP;
t2_110 := 32bv64;
RSP := PLUS_64(RSP, t2_110);
CF := bool2bv(LT_64(RSP, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x31fa:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x31fb:

ra_115 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_34,origCOUNT_40,origCOUNT_50,origCOUNT_56,origCOUNT_66,origCOUNT_72,origCOUNT_82,origCOUNT_88,origCOUNT_98,origDEST_103,origDEST_33,origDEST_39,origDEST_49,origDEST_55,origDEST_65,origDEST_71,origDEST_81,origDEST_87,origDEST_97,ra_115,t1_109,t2_110,t_1,t_11,t_15,t_21,t_25,t_5,t_7;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_12: bv1;
const unconstrained_13: bv1;
const unconstrained_14: bv1;
const unconstrained_15: bv1;
const unconstrained_16: bv1;
const unconstrained_17: bv1;
const unconstrained_18: bv1;
const unconstrained_19: bv1;
const unconstrained_2: bv1;
const unconstrained_20: bv1;
const unconstrained_21: bv1;
const unconstrained_22: bv1;
const unconstrained_23: bv1;
const unconstrained_24: bv1;
const unconstrained_25: bv1;
const unconstrained_26: bv1;
const unconstrained_27: bv1;
const unconstrained_28: bv1;
const unconstrained_29: bv1;
const unconstrained_3: bv1;
const unconstrained_30: bv1;
const unconstrained_31: bv1;
const unconstrained_32: bv1;
const unconstrained_33: bv1;
const unconstrained_34: bv1;
const unconstrained_35: bv1;
const unconstrained_36: bv1;
const unconstrained_37: bv1;
const unconstrained_38: bv1;
const unconstrained_39: bv1;
const unconstrained_4: bv1;
const unconstrained_40: bv1;
const unconstrained_41: bv1;
const unconstrained_42: bv1;
const unconstrained_43: bv1;
const unconstrained_44: bv1;
const unconstrained_45: bv1;
const unconstrained_46: bv1;
const unconstrained_47: bv1;
const unconstrained_48: bv1;
const unconstrained_49: bv1;
const unconstrained_5: bv1;
const unconstrained_50: bv1;
const unconstrained_51: bv1;
const unconstrained_52: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R9: bv64;
var R10: bv64;
var R11: bv64;
var R12: bv64;
var R13: bv64;
var R14: bv64;
var R15: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var RAX: bv64;
var RBP: bv64;
var RBX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSI: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_104: bv64;
var origCOUNT_34: bv64;
var origCOUNT_40: bv64;
var origCOUNT_50: bv64;
var origCOUNT_56: bv64;
var origCOUNT_66: bv64;
var origCOUNT_72: bv64;
var origCOUNT_82: bv64;
var origCOUNT_88: bv64;
var origCOUNT_98: bv64;
var origDEST_103: bv64;
var origDEST_33: bv64;
var origDEST_39: bv64;
var origDEST_49: bv64;
var origDEST_55: bv64;
var origDEST_65: bv64;
var origDEST_71: bv64;
var origDEST_81: bv64;
var origDEST_87: bv64;
var origDEST_97: bv64;
var ra_115: bv64;
var t1_109: bv64;
var t2_110: bv64;
var t_1: bv64;
var t_11: bv8;
var t_15: bv8;
var t_21: bv64;
var t_25: bv8;
var t_5: bv64;
var t_7: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(11504bv64);
axiom policy(4272bv64);
axiom policy(4384bv64);
axiom policy(4576bv64);
axiom policy(4624bv64);
axiom policy(4720bv64);
axiom policy(4816bv64);
axiom policy(4912bv64);
axiom policy(5008bv64);
axiom policy(5120bv64);
axiom policy(5168bv64);
axiom policy(5440bv64);
axiom policy(5520bv64);
axiom policy(6128bv64);
axiom policy(6752bv64);
axiom policy(7392bv64);
axiom policy(8032bv64);
axiom policy(9504bv64);
axiom policy(9632bv64);
axiom policy(9648bv64);
axiom policy(9664bv64);
axiom policy(9824bv64);
axiom policy(9872bv64);
axiom policy(9984bv64);
axiom policy(10080bv64);
axiom policy(10320bv64);
axiom policy(11728bv64);
axiom policy(11488bv64);
axiom policy(11616bv64);
axiom policy(13168bv64);
axiom policy(11744bv64);
axiom policy(12080bv64);
axiom policy(12128bv64);
axiom policy(12144bv64);
axiom policy(12160bv64);
axiom policy(12176bv64);
axiom policy(12192bv64);
axiom policy(12208bv64);
axiom policy(12304bv64);
axiom policy(12400bv64);
axiom policy(12800bv64);
axiom policy(13072bv64);
axiom policy(13184bv64);
axiom policy(13280bv64);
axiom policy(13856bv64);
axiom policy(14352bv64);
axiom policy(14512bv64);
axiom policy(14528bv64);
axiom policy(15248bv64);
axiom policy(16208bv64);
axiom policy(18768bv64);
axiom policy(19152bv64);
axiom policy(19520bv64);
axiom policy(20400bv64);
axiom policy(20480bv64);
axiom policy(20688bv64);
axiom policy(20768bv64);
axiom policy(20784bv64);
axiom policy(20800bv64);
axiom policy(20816bv64);
axiom policy(20832bv64);
axiom policy(21040bv64);
axiom policy(21200bv64);
