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
axiom _function_addr_low == 2576bv64;
axiom _function_addr_high == 3104bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xa10:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0xa15:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0xa1a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0xa1e:
t_1 := RSP;
RSP := MINUS_64(RSP, 56bv64);
CF := bool2bv(LT_64(t_1, 56bv64));
OF := AND_64((XOR_64(t_1, 56bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 56bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xa22:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0xa2a:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2608bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2608bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2608bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2608bv64)), 1bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2608bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0xa31:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xa4d;
}

label_0xa33:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0xa38:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xa3d:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0xa41:
RCX := PLUS_64((PLUS_64(0bv64, 2632bv64)), 0bv64)[64:0];

label_0xa48:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2637bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa4d"} true;
call arbitrary_func();

label_0xa4d:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0xa52:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xa79;
}

label_0xa54:
RCX := (0bv32 ++ 2bv32);

label_0xa59:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2654bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa5e"} true;
call arbitrary_func();

label_0xa5e:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0xa63:
RDX := PLUS_64((PLUS_64(0bv64, 2666bv64)), 0bv64)[64:0];

label_0xa6a:
RCX := RAX;

label_0xa6d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2674bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa72"} true;
call arbitrary_func();

label_0xa72:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xa74:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2681bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa79"} true;
call arbitrary_func();

label_0xa79:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xa7e:
t_13 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_13[64:0];
OF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_2;
SF := unconstrained_3;
ZF := unconstrained_4;
AF := unconstrained_5;

label_0xa82:
RCX := PLUS_64((PLUS_64(0bv64, 2697bv64)), 0bv64)[64:0];

label_0xa89:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xa8e:
t_15 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RDX := t_15[64:0];
OF := bool2bv(t_15 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_15 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_6;
SF := unconstrained_7;
ZF := unconstrained_8;
AF := unconstrained_9;

label_0xa92:
R8 := PLUS_64((PLUS_64(0bv64, 2713bv64)), 0bv64)[64:0];

label_0xa99:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R8, RDX)), 4bv64)));

label_0xa9e:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), (RDX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), (RDX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), (RDX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))))), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0xaa2:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0xac3;
}

label_0xaa4:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2730bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2730bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2730bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2730bv64)), 1bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2730bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0xaab:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xab9;
}

label_0xaad:
RCX := PLUS_64((PLUS_64(0bv64, 2740bv64)), 0bv64)[64:0];

label_0xab4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2745bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xab9"} true;
call arbitrary_func();

label_0xab9:
RAX := (0bv32 ++ 4294967295bv32);

label_0xabe:
goto label_0xc0b;

label_0xac3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xac8:
t_25 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_25[64:0];
OF := bool2bv(t_25 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_25 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_10;
SF := unconstrained_11;
ZF := unconstrained_12;
AF := unconstrained_13;

label_0xacc:
RCX := PLUS_64((PLUS_64(0bv64, 2771bv64)), 0bv64)[64:0];

label_0xad3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64)));

label_0xad7:
t1_27 := RAX[32:0];
t2_28 := LOAD_LE_32(mem, PLUS_64(RSP, 80bv64));
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_28));
CF := bool2bv(LT_32((RAX[32:0]), t1_27));
OF := AND_1((bool2bv((t1_27[32:31]) == (t2_28[32:31]))), (XOR_1((t1_27[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_27)), t2_28)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xadb:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xae0:
t_33 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RCX := t_33[64:0];
OF := bool2bv(t_33 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_33 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_14;
SF := unconstrained_15;
ZF := unconstrained_16;
AF := unconstrained_17;

label_0xae4:
RDX := PLUS_64((PLUS_64(0bv64, 2795bv64)), 0bv64)[64:0];

label_0xaeb:
t_35 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64((PLUS_64(RDX, RCX)), 4bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64((PLUS_64(RDX, RCX)), 4bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64((PLUS_64(RDX, RCX)), 4bv64))))), (XOR_32((RAX[32:0]), t_35)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_35, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64((PLUS_64(RDX, RCX)), 4bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)), 2bv32)), (XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)), 2bv32)), (XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)))))[1:0]));
SF := t_35[32:31];
ZF := bool2bv(0bv32 == t_35);

label_0xaef:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0xb22;
}

label_0xaf1:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xaf6:
t_39 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_39[64:0];
OF := bool2bv(t_39 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_39 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_18;
SF := unconstrained_19;
ZF := unconstrained_20;
AF := unconstrained_21;

label_0xafa:
RCX := PLUS_64((PLUS_64(0bv64, 2817bv64)), 0bv64)[64:0];

label_0xb01:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xb06:
t_41 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RDX := t_41[64:0];
OF := bool2bv(t_41 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_41 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_22;
SF := unconstrained_23;
ZF := unconstrained_24;
AF := unconstrained_25;

label_0xb0a:
R8 := PLUS_64((PLUS_64(0bv64, 2833bv64)), 0bv64)[64:0];

label_0xb11:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R8, RDX)), 8bv64)));

label_0xb16:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0xb1a:
t_43 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_43, (RDX[32:0])));
OF := AND_32((XOR_32(t_43, (RDX[32:0]))), (XOR_32(t_43, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_43)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb1c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xb20:
goto label_0xb2a;

label_0xb22:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0xb26:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xb2a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0xb2f:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xb34:
t_47 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RCX := t_47[64:0];
OF := bool2bv(t_47 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_47 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_26;
SF := unconstrained_27;
ZF := unconstrained_28;
AF := unconstrained_29;

label_0xb38:
RDX := PLUS_64((PLUS_64(0bv64, 2879bv64)), 0bv64)[64:0];

label_0xb3f:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xb44:
t_49 := TIMES_128(((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
R8 := t_49[64:0];
OF := bool2bv(t_49 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
CF := bool2bv(t_49 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
PF := unconstrained_30;
SF := unconstrained_31;
ZF := unconstrained_32;
AF := unconstrained_33;

label_0xb48:
R9 := PLUS_64((PLUS_64(0bv64, 2895bv64)), 0bv64)[64:0];

label_0xb4f:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64)))));

label_0xb54:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RDX, RCX)), 16bv64));

label_0xb59:
t1_51 := RCX;
t2_52 := R8;
RCX := PLUS_64(RCX, t2_52);
CF := bool2bv(LT_64(RCX, t1_51));
OF := AND_1((bool2bv((t1_51[64:63]) == (t2_52[64:63]))), (XOR_1((t1_51[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_51)), t2_52)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xb5c:
R8 := RAX;

label_0xb5f:
RDX := RCX;

label_0xb62:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xb67:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2924bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb6c"} true;
call arbitrary_func();

label_0xb6c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xb71:
t_57 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_57[64:0];
OF := bool2bv(t_57 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_57 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_34;
SF := unconstrained_35;
ZF := unconstrained_36;
AF := unconstrained_37;

label_0xb75:
RCX := PLUS_64((PLUS_64(0bv64, 2940bv64)), 0bv64)[64:0];

label_0xb7c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xb80:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64)));

label_0xb84:
t1_59 := RAX[32:0];
t2_60 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_60));
CF := bool2bv(LT_32((RAX[32:0]), t1_59));
OF := AND_1((bool2bv((t1_59[32:31]) == (t2_60[32:31]))), (XOR_1((t1_59[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_59)), t2_60)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb86:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0xb8a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));

label_0xb8f:
t_65 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_65[64:0];
OF := bool2bv(t_65 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_65 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_38;
SF := unconstrained_39;
ZF := unconstrained_40;
AF := unconstrained_41;

label_0xb93:
RCX := PLUS_64((PLUS_64(0bv64, 2970bv64)), 0bv64)[64:0];

label_0xb9a:
t1_67 := RCX;
t2_68 := RAX;
RCX := PLUS_64(RCX, t2_68);
CF := bool2bv(LT_64(RCX, t1_67));
OF := AND_1((bool2bv((t1_67[64:63]) == (t2_68[64:63]))), (XOR_1((t1_67[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_67)), t2_68)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xb9d:
RAX := RCX;

label_0xba0:
t1_73 := RAX;
t2_74 := 8bv64;
RAX := PLUS_64(RAX, t2_74);
CF := bool2bv(LT_64(RAX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xba4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0xba9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xbae:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbb4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbb9:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0xbbc:
if (bv2bool(ZF)) {
  goto label_0xbbf;
}

label_0xbbe:
assume false;

label_0xbbf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xbc4:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_45);

label_0xbc8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbcf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbd3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xbd8:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_47);

label_0xbdc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0xbe0:
if (bv2bool(CF)) {
  goto label_0xbe3;
}

label_0xbe2:
assume false;

label_0xbe3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xbe8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0xbec:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbee:
t_97 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3060bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3060bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3060bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3060bv64)), 1bv64))), t_97)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_97, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3060bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))))[1:0]));
SF := t_97[32:31];
ZF := bool2bv(0bv32 == t_97);

label_0xbf5:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xc07;
}

label_0xbf7:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xbfb:
RCX := PLUS_64((PLUS_64(0bv64, 3074bv64)), 0bv64)[64:0];

label_0xc02:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3079bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc07"} true;
call arbitrary_func();

label_0xc07:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xc0b:
t1_101 := RSP;
t2_102 := 56bv64;
RSP := PLUS_64(RSP, t2_102);
CF := bool2bv(LT_64(RSP, t1_101));
OF := AND_1((bool2bv((t1_101[64:63]) == (t2_102[64:63]))), (XOR_1((t1_101[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_101)), t2_102)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xc0f:

ra_107 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_86,origCOUNT_92,origDEST_85,origDEST_91,ra_107,t1_101,t1_27,t1_51,t1_59,t1_67,t1_73,t2_102,t2_28,t2_52,t2_60,t2_68,t2_74,t_1,t_13,t_15,t_17,t_21,t_25,t_33,t_35,t_39,t_41,t_43,t_47,t_49,t_5,t_57,t_65,t_81,t_9,t_97;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_85: bv64;
var origDEST_91: bv64;
var ra_107: bv64;
var t1_101: bv64;
var t1_27: bv32;
var t1_51: bv64;
var t1_59: bv32;
var t1_67: bv64;
var t1_73: bv64;
var t2_102: bv64;
var t2_28: bv32;
var t2_52: bv64;
var t2_60: bv32;
var t2_68: bv64;
var t2_74: bv64;
var t_1: bv64;
var t_13: bv128;
var t_15: bv128;
var t_17: bv32;
var t_21: bv32;
var t_25: bv128;
var t_33: bv128;
var t_35: bv32;
var t_39: bv128;
var t_41: bv128;
var t_43: bv32;
var t_47: bv128;
var t_49: bv128;
var t_5: bv32;
var t_57: bv128;
var t_65: bv128;
var t_81: bv64;
var t_9: bv32;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(48bv64);
axiom policy(112bv64);
axiom policy(176bv64);
axiom policy(720bv64);
axiom policy(1504bv64);
axiom policy(2576bv64);
axiom policy(3104bv64);
axiom policy(3392bv64);
axiom policy(3856bv64);
axiom policy(4240bv64);
axiom policy(4672bv64);
axiom policy(5232bv64);
axiom policy(5728bv64);
axiom policy(5856bv64);
axiom policy(6336bv64);
axiom policy(6352bv64);
axiom policy(6480bv64);
