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
axiom _guard_writeTable_ptr == 29888bv64;
axiom _guard_callTable_ptr == 29904bv64;
axiom _function_addr_low == 7248bv64;
axiom _function_addr_high == 8560bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1c50:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x1c55:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1c5a:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1c61:
RDX := (0bv32 ++ 32768bv32);

label_0x1c66:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1c6e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7283bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c73"} true;
call arbitrary_func();

label_0x1c73:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1c77:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x1c7c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c85;
}

label_0x1c7e:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1c80:
goto label_0x215a;

label_0x1c85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1c8d:
t1_9 := RAX;
t2_10 := 4416bv64;
RAX := PLUS_64(RAX, t2_10);
CF := bool2bv(LT_64(RAX, t1_9));
OF := AND_1((bool2bv((t1_9[64:63]) == (t2_10[64:63]))), (XOR_1((t1_9[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_9)), t2_10)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c93:
R8 := (0bv32 ++ 1bv32);

label_0x1c99:
RDX := RAX;

label_0x1c9c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1ca0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7333bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ca5"} true;
call arbitrary_func();

label_0x1ca5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1cad:
t1_15 := RAX;
t2_16 := 4417bv64;
RAX := PLUS_64(RAX, t2_16);
CF := bool2bv(LT_64(RAX, t1_15));
OF := AND_1((bool2bv((t1_15[64:63]) == (t2_16[64:63]))), (XOR_1((t1_15[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_15)), t2_16)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1cb3:
R8 := (0bv32 ++ 1bv32);

label_0x1cb9:
RDX := RAX;

label_0x1cbc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1cc0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7365bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1cc5"} true;
call arbitrary_func();

label_0x1cc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1ccd:
t1_21 := RAX;
t2_22 := 4418bv64;
RAX := PLUS_64(RAX, t2_22);
CF := bool2bv(LT_64(RAX, t1_21));
OF := AND_1((bool2bv((t1_21[64:63]) == (t2_22[64:63]))), (XOR_1((t1_21[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_21)), t2_22)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1cd3:
R8 := (0bv32 ++ 1bv32);

label_0x1cd9:
RDX := RAX;

label_0x1cdc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1ce0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7397bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ce5"} true;
call arbitrary_func();

label_0x1ce5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1ced:
t1_27 := RAX;
t2_28 := 4419bv64;
RAX := PLUS_64(RAX, t2_28);
CF := bool2bv(LT_64(RAX, t1_27));
OF := AND_1((bool2bv((t1_27[64:63]) == (t2_28[64:63]))), (XOR_1((t1_27[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_27)), t2_28)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1cf3:
R8 := (0bv32 ++ 1bv32);

label_0x1cf9:
RDX := RAX;

label_0x1cfc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1d00:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7429bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d05"} true;
call arbitrary_func();

label_0x1d05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1d0d:
t1_33 := RAX;
t2_34 := 4420bv64;
RAX := PLUS_64(RAX, t2_34);
CF := bool2bv(LT_64(RAX, t1_33));
OF := AND_1((bool2bv((t1_33[64:63]) == (t2_34[64:63]))), (XOR_1((t1_33[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_33)), t2_34)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d13:
R8 := (0bv32 ++ 1bv32);

label_0x1d19:
RDX := RAX;

label_0x1d1c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1d20:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7461bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d25"} true;
call arbitrary_func();

label_0x1d25:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1d2d:
t1_39 := RAX;
t2_40 := 4421bv64;
RAX := PLUS_64(RAX, t2_40);
CF := bool2bv(LT_64(RAX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d33:
R8 := (0bv32 ++ 1bv32);

label_0x1d39:
RDX := RAX;

label_0x1d3c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1d40:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7493bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d45"} true;
call arbitrary_func();

label_0x1d45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1d4d:
t1_45 := RAX;
t2_46 := 4422bv64;
RAX := PLUS_64(RAX, t2_46);
CF := bool2bv(LT_64(RAX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d53:
R8 := (0bv32 ++ 1bv32);

label_0x1d59:
RDX := RAX;

label_0x1d5c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1d60:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7525bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d65"} true;
call arbitrary_func();

label_0x1d65:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1d6d:
t1_51 := RAX;
t2_52 := 4423bv64;
RAX := PLUS_64(RAX, t2_52);
CF := bool2bv(LT_64(RAX, t1_51));
OF := AND_1((bool2bv((t1_51[64:63]) == (t2_52[64:63]))), (XOR_1((t1_51[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_51)), t2_52)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d73:
R8 := (0bv32 ++ 1bv32);

label_0x1d79:
RDX := RAX;

label_0x1d7c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1d80:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7557bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d85"} true;
call arbitrary_func();

label_0x1d85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1d8d:
t1_57 := RAX;
t2_58 := 4416bv64;
RAX := PLUS_64(RAX, t2_58);
CF := bool2bv(LT_64(RAX, t1_57));
OF := AND_1((bool2bv((t1_57[64:63]) == (t2_58[64:63]))), (XOR_1((t1_57[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_57)), t2_58)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d93:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x1d98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1da0:
t1_63 := RAX;
t2_64 := 4424bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1da6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1dab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1db0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1db6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1dbb:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x1dbe:
if (bv2bool(ZF)) {
  goto label_0x1dc1;
}

label_0x1dc0:
assume false;

label_0x1dc1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1dc6:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_5);

label_0x1dca:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1dd1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1dd5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1dda:
origDEST_81 := RCX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_7);

label_0x1dde:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x1de2:
if (bv2bool(CF)) {
  goto label_0x1de5;
}

label_0x1de4:
assume false;

label_0x1de5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1dea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1def:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1df1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1df3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1dfb:
t1_87 := RAX;
t2_88 := 4420bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1e01:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x1e06:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1e0e:
t1_93 := RAX;
t2_94 := 4428bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1e14:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1e19:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1e1e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1e24:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1e29:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x1e2c:
if (bv2bool(ZF)) {
  goto label_0x1e2f;
}

label_0x1e2e:
assume false;

label_0x1e2f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1e34:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_15);

label_0x1e38:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1e3f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1e43:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1e48:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_17);

label_0x1e4c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x1e50:
if (bv2bool(CF)) {
  goto label_0x1e53;
}

label_0x1e52:
assume false;

label_0x1e53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1e58:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1e5d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1e5f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1e61:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x1e69:
goto label_0x1e75;

label_0x1e6b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x1e6f:
t_117 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_117[32:31]) == (1bv32[32:31]))), (XOR_1((t_117[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_117)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1e71:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x1e75:
t_121 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_121)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_121, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))))[1:0]));
SF := t_121[32:31];
ZF := bool2bv(0bv32 == t_121);

label_0x1e7d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1ea7;
}

label_0x1e7f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));

label_0x1e84:
t_125 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(16bv64[64:63]) ,(1bv64 ++ 16bv64) ,(0bv64 ++ 16bv64)))));
RAX := t_125[64:0];
OF := bool2bv(t_125 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_125 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_22;
SF := unconstrained_23;
ZF := unconstrained_24;
AF := unconstrained_25;

label_0x1e88:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1e90:
RAX := PLUS_64((PLUS_64(RCX, RAX)), 280bv64)[64:0];

label_0x1e98:
RDX := (0bv32 ++ 128bv32);

label_0x1e9d:
RCX := RAX;

label_0x1ea0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7845bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ea5"} true;
call arbitrary_func();

label_0x1ea5:
goto label_0x1e6b;

label_0x1ea7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1eaf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x1eb5:
t_127 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_127, 1bv32)), (XOR_32(t_127, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_127)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1eb7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0x1ebb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1ec3:
t1_131 := RAX;
t2_132 := 4408bv64;
RAX := PLUS_64(RAX, t2_132);
CF := bool2bv(LT_64(RAX, t1_131));
OF := AND_1((bool2bv((t1_131[64:63]) == (t2_132[64:63]))), (XOR_1((t1_131[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_131)), t2_132)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ec9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1ece:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1ed3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ed9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1ede:
t_139 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x1ee1:
if (bv2bool(ZF)) {
  goto label_0x1ee4;
}

label_0x1ee3:
assume false;

label_0x1ee4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1ee9:
origDEST_143 := RAX;
origCOUNT_144 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_29);

label_0x1eed:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1ef4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1ef8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1efd:
origDEST_149 := RCX;
origCOUNT_150 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_31);

label_0x1f01:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_32;
SF := unconstrained_33;
AF := unconstrained_34;
PF := unconstrained_35;

label_0x1f05:
if (bv2bool(CF)) {
  goto label_0x1f08;
}

label_0x1f07:
assume false;

label_0x1f08:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1f0d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x1f11:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1f13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1f1b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4428bv64)));

label_0x1f21:
t_155 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_155, 1bv32)), (XOR_32(t_155, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_155)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1f23:
mem := STORE_LE_32(mem, PLUS_64(RSP, 100bv64), RAX[32:0]);

label_0x1f27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1f2f:
t1_159 := RAX;
t2_160 := 4412bv64;
RAX := PLUS_64(RAX, t2_160);
CF := bool2bv(LT_64(RAX, t1_159));
OF := AND_1((bool2bv((t1_159[64:63]) == (t2_160[64:63]))), (XOR_1((t1_159[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_159)), t2_160)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1f35:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1f3a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1f3f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1f45:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1f4a:
t_167 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))))[1:0]));
SF := t_167[64:63];
ZF := bool2bv(0bv64 == t_167);

label_0x1f4d:
if (bv2bool(ZF)) {
  goto label_0x1f50;
}

label_0x1f4f:
assume false;

label_0x1f50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1f55:
origDEST_171 := RAX;
origCOUNT_172 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), CF, LSHIFT_64(origDEST_171, (MINUS_64(64bv64, origCOUNT_172)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_172 == 1bv64)), origDEST_171[64:63], unconstrained_38));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), AF, unconstrained_39);

label_0x1f59:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1f60:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1f64:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1f69:
origDEST_177 := RCX;
origCOUNT_178 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), CF, LSHIFT_64(origDEST_177, (MINUS_64(64bv64, origCOUNT_178)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_178 == 1bv64)), origDEST_177[64:63], unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), AF, unconstrained_41);

label_0x1f6d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_42;
SF := unconstrained_43;
AF := unconstrained_44;
PF := unconstrained_45;

label_0x1f71:
if (bv2bool(CF)) {
  goto label_0x1f74;
}

label_0x1f73:
assume false;

label_0x1f74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1f79:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 100bv64)));

label_0x1f7d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1f7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1f87:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1f8f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x1f95:
t_183 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_183[32:0]);
OF := bool2bv(t_183 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_183 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_46;
SF := unconstrained_47;
ZF := unconstrained_48;
AF := unconstrained_49;

label_0x1f9c:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x1f9e:
origDEST_185 := RAX;
origCOUNT_186 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), CF, RSHIFT_64(origDEST_185, (MINUS_64(64bv64, origCOUNT_186)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), AF, unconstrained_51);

label_0x1fa2:
RCX := RAX;

label_0x1fa5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8106bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1faa"} true;
call arbitrary_func();

label_0x1faa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x1faf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1fb7:
t1_191 := RAX;
t2_192 := 8bv64;
RAX := PLUS_64(RAX, t2_192);
CF := bool2bv(LT_64(RAX, t1_191));
OF := AND_1((bool2bv((t1_191[64:63]) == (t2_192[64:63]))), (XOR_1((t1_191[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_191)), t2_192)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1fbb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1fc0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1fc5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1fcb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1fd0:
t_199 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x1fd3:
if (bv2bool(ZF)) {
  goto label_0x1fd6;
}

label_0x1fd5:
assume false;

label_0x1fd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1fdb:
origDEST_203 := RAX;
origCOUNT_204 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), CF, LSHIFT_64(origDEST_203, (MINUS_64(64bv64, origCOUNT_204)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv64)), origDEST_203[64:63], unconstrained_54));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), AF, unconstrained_55);

label_0x1fdf:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1fe6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1fea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1fef:
origDEST_209 := RCX;
origCOUNT_210 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_57);

label_0x1ff3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_58;
SF := unconstrained_59;
AF := unconstrained_60;
PF := unconstrained_61;

label_0x1ff7:
if (bv2bool(CF)) {
  goto label_0x1ffa;
}

label_0x1ff9:
assume false;

label_0x1ffa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1fff:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x2004:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2007:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x200f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2017:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x201d:
t_215 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_215[32:0]);
OF := bool2bv(t_215 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_215 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_62;
SF := unconstrained_63;
ZF := unconstrained_64;
AF := unconstrained_65;

label_0x2024:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2026:
origDEST_217 := RAX;
origCOUNT_218 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), CF, RSHIFT_64(origDEST_217, (MINUS_64(64bv64, origCOUNT_218)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), AF, unconstrained_67);

label_0x202a:
R8 := RAX;

label_0x202d:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_68;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x202f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2037:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x203b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8256bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2040"} true;
call arbitrary_func();

label_0x2040:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2048:
t1_223 := RAX;
t2_224 := 16bv64;
RAX := PLUS_64(RAX, t2_224);
CF := bool2bv(LT_64(RAX, t1_223));
OF := AND_1((bool2bv((t1_223[64:63]) == (t2_224[64:63]))), (XOR_1((t1_223[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_223)), t2_224)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x204c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x2051:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2056:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x205c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2061:
t_231 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_70;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_231, 4bv64)), t_231)), 2bv64)), (XOR_64((RSHIFT_64(t_231, 4bv64)), t_231)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_231, 4bv64)), t_231)), 2bv64)), (XOR_64((RSHIFT_64(t_231, 4bv64)), t_231)))))[1:0]));
SF := t_231[64:63];
ZF := bool2bv(0bv64 == t_231);

label_0x2064:
if (bv2bool(ZF)) {
  goto label_0x2067;
}

label_0x2066:
assume false;

label_0x2067:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x206c:
origDEST_235 := RAX;
origCOUNT_236 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), CF, LSHIFT_64(origDEST_235, (MINUS_64(64bv64, origCOUNT_236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv64)), origDEST_235[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), AF, unconstrained_72);

label_0x2070:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2077:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x207b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2080:
origDEST_241 := RCX;
origCOUNT_242 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), CF, LSHIFT_64(origDEST_241, (MINUS_64(64bv64, origCOUNT_242)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_242 == 1bv64)), origDEST_241[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), AF, unconstrained_74);

label_0x2084:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_75;
SF := unconstrained_76;
AF := unconstrained_77;
PF := unconstrained_78;

label_0x2088:
if (bv2bool(CF)) {
  goto label_0x208b;
}

label_0x208a:
assume false;

label_0x208b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_79;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x208d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2092:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x2095:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x209d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x20a5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x20ab:
t_247 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_247[32:0]);
OF := bool2bv(t_247 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_247 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_80;
SF := unconstrained_81;
ZF := unconstrained_82;
AF := unconstrained_83;

label_0x20b2:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x20b4:
RCX := RAX;

label_0x20b7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8380bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x20bc"} true;
call arbitrary_func();

label_0x20bc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x20c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x20cc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x20d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x20d6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_84;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x20dc:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x20e1:
t_251 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_85;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))))[1:0]));
SF := t_251[64:63];
ZF := bool2bv(0bv64 == t_251);

label_0x20e4:
if (bv2bool(ZF)) {
  goto label_0x20e7;
}

label_0x20e6:
assume false;

label_0x20e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x20ec:
origDEST_255 := RAX;
origCOUNT_256 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), CF, LSHIFT_64(origDEST_255, (MINUS_64(64bv64, origCOUNT_256)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_256 == 1bv64)), origDEST_255[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), AF, unconstrained_87);

label_0x20f0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x20f7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x20fb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2100:
origDEST_261 := RCX;
origCOUNT_262 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_89);

label_0x2104:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_90;
SF := unconstrained_91;
AF := unconstrained_92;
PF := unconstrained_93;

label_0x2108:
if (bv2bool(CF)) {
  goto label_0x210b;
}

label_0x210a:
assume false;

label_0x210b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2110:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2118:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x211b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2123:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x212b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x2131:
t_267 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_267[32:0]);
OF := bool2bv(t_267 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_267 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_94;
SF := unconstrained_95;
ZF := unconstrained_96;
AF := unconstrained_97;

label_0x2138:
R8 := (0bv32 ++ RAX[32:0]);

label_0x213b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2143:
RDX := LOAD_LE_64(mem, RAX);

label_0x2146:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x214a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8527bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x214f"} true;
call arbitrary_func();

label_0x214f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2153:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8536bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2158"} true;
call arbitrary_func();

label_0x2158:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x215a:
t1_269 := RSP;
t2_270 := 152bv64;
RSP := PLUS_64(RSP, t2_270);
CF := bool2bv(LT_64(RSP, t1_269));
OF := AND_1((bool2bv((t1_269[64:63]) == (t2_270[64:63]))), (XOR_1((t1_269[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_269)), t2_270)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2161:

ra_275 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_144,origCOUNT_150,origCOUNT_172,origCOUNT_178,origCOUNT_186,origCOUNT_204,origCOUNT_210,origCOUNT_218,origCOUNT_236,origCOUNT_242,origCOUNT_256,origCOUNT_262,origCOUNT_76,origCOUNT_82,origDEST_105,origDEST_111,origDEST_143,origDEST_149,origDEST_171,origDEST_177,origDEST_185,origDEST_203,origDEST_209,origDEST_217,origDEST_235,origDEST_241,origDEST_255,origDEST_261,origDEST_75,origDEST_81,ra_275,t1_131,t1_15,t1_159,t1_191,t1_21,t1_223,t1_269,t1_27,t1_33,t1_39,t1_45,t1_51,t1_57,t1_63,t1_87,t1_9,t1_93,t2_10,t2_132,t2_16,t2_160,t2_192,t2_22,t2_224,t2_270,t2_28,t2_34,t2_40,t2_46,t2_52,t2_58,t2_64,t2_88,t2_94,t_1,t_101,t_117,t_121,t_125,t_127,t_139,t_155,t_167,t_183,t_199,t_215,t_231,t_247,t_251,t_267,t_5,t_71;

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
const unconstrained_53: bv1;
const unconstrained_54: bv1;
const unconstrained_55: bv1;
const unconstrained_56: bv1;
const unconstrained_57: bv1;
const unconstrained_58: bv1;
const unconstrained_59: bv1;
const unconstrained_6: bv1;
const unconstrained_60: bv1;
const unconstrained_61: bv1;
const unconstrained_62: bv1;
const unconstrained_63: bv1;
const unconstrained_64: bv1;
const unconstrained_65: bv1;
const unconstrained_66: bv1;
const unconstrained_67: bv1;
const unconstrained_68: bv1;
const unconstrained_69: bv1;
const unconstrained_7: bv1;
const unconstrained_70: bv1;
const unconstrained_71: bv1;
const unconstrained_72: bv1;
const unconstrained_73: bv1;
const unconstrained_74: bv1;
const unconstrained_75: bv1;
const unconstrained_76: bv1;
const unconstrained_77: bv1;
const unconstrained_78: bv1;
const unconstrained_79: bv1;
const unconstrained_8: bv1;
const unconstrained_80: bv1;
const unconstrained_81: bv1;
const unconstrained_82: bv1;
const unconstrained_83: bv1;
const unconstrained_84: bv1;
const unconstrained_85: bv1;
const unconstrained_86: bv1;
const unconstrained_87: bv1;
const unconstrained_88: bv1;
const unconstrained_89: bv1;
const unconstrained_9: bv1;
const unconstrained_90: bv1;
const unconstrained_91: bv1;
const unconstrained_92: bv1;
const unconstrained_93: bv1;
const unconstrained_94: bv1;
const unconstrained_95: bv1;
const unconstrained_96: bv1;
const unconstrained_97: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_106: bv64;
var origCOUNT_112: bv64;
var origCOUNT_144: bv64;
var origCOUNT_150: bv64;
var origCOUNT_172: bv64;
var origCOUNT_178: bv64;
var origCOUNT_186: bv64;
var origCOUNT_204: bv64;
var origCOUNT_210: bv64;
var origCOUNT_218: bv64;
var origCOUNT_236: bv64;
var origCOUNT_242: bv64;
var origCOUNT_256: bv64;
var origCOUNT_262: bv64;
var origCOUNT_76: bv64;
var origCOUNT_82: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_143: bv64;
var origDEST_149: bv64;
var origDEST_171: bv64;
var origDEST_177: bv64;
var origDEST_185: bv64;
var origDEST_203: bv64;
var origDEST_209: bv64;
var origDEST_217: bv64;
var origDEST_235: bv64;
var origDEST_241: bv64;
var origDEST_255: bv64;
var origDEST_261: bv64;
var origDEST_75: bv64;
var origDEST_81: bv64;
var ra_275: bv64;
var t1_131: bv64;
var t1_15: bv64;
var t1_159: bv64;
var t1_191: bv64;
var t1_21: bv64;
var t1_223: bv64;
var t1_269: bv64;
var t1_27: bv64;
var t1_33: bv64;
var t1_39: bv64;
var t1_45: bv64;
var t1_51: bv64;
var t1_57: bv64;
var t1_63: bv64;
var t1_87: bv64;
var t1_9: bv64;
var t1_93: bv64;
var t2_10: bv64;
var t2_132: bv64;
var t2_16: bv64;
var t2_160: bv64;
var t2_192: bv64;
var t2_22: bv64;
var t2_224: bv64;
var t2_270: bv64;
var t2_28: bv64;
var t2_34: bv64;
var t2_40: bv64;
var t2_46: bv64;
var t2_52: bv64;
var t2_58: bv64;
var t2_64: bv64;
var t2_88: bv64;
var t2_94: bv64;
var t_1: bv64;
var t_101: bv64;
var t_117: bv32;
var t_121: bv32;
var t_125: bv128;
var t_127: bv32;
var t_139: bv64;
var t_155: bv32;
var t_167: bv64;
var t_183: bv64;
var t_199: bv64;
var t_215: bv64;
var t_231: bv64;
var t_247: bv64;
var t_251: bv64;
var t_267: bv64;
var t_5: bv32;
var t_71: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(64bv64);
axiom policy(448bv64);
axiom policy(1680bv64);
axiom policy(2128bv64);
axiom policy(3744bv64);
axiom policy(6080bv64);
axiom policy(7248bv64);
axiom policy(8560bv64);
axiom policy(9472bv64);
axiom policy(9664bv64);
