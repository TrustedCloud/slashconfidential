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
axiom _function_addr_low == 31152bv64;
axiom _function_addr_high == 34640bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x79b0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x79b5:
t_1 := RSP;
RSP := MINUS_64(RSP, 328bv64);
CF := bool2bv(LT_64(t_1, 328bv64));
OF := AND_64((XOR_64(t_1, 328bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 328bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x79bc:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x79c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x79c9:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x79cd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8079;
}

label_0x79d3:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x79d5:
t_9 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x79d8:
if (bv2bool(ZF)) {
  goto label_0x8074;
}

label_0x79de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x79e6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x79ee:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 112bv64)));

label_0x79f1:
t_13 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x79f4:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x79fb;
}

label_0x79f6:
goto label_0x8074;

label_0x79fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a03:
RAX := LOAD_LE_64(mem, RAX);

label_0x7a06:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x7a0a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x7a11;
}

label_0x7a0c:
goto label_0x8074;

label_0x7a11:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x7a16:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a1e:
RAX := LOAD_LE_64(mem, RAX);

label_0x7a21:
RAX := LOAD_LE_64(mem, RAX);

label_0x7a24:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x7a27:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x7a2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a33:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x7a36:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x7a3a:
if (bv2bool(ZF)) {
  goto label_0x7cd5;
}

label_0x7a40:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a48:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x7a4c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x7cd5;
}

label_0x7a52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a5a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 92bv64))));

label_0x7a5e:
mem := STORE_LE_8(mem, PLUS_64(RSP, 33bv64), RAX[32:0][8:0]);

label_0x7a62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a6a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 648bv64)));

label_0x7a70:
origDEST_29 := RAX[32:0];
origCOUNT_30 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), CF, RSHIFT_32(origDEST_29, (MINUS_32(32bv32, origCOUNT_30)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv32)), AF, unconstrained_3);

label_0x7a73:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7a7b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 648bv64)));

label_0x7a81:
origDEST_35 := RCX[32:0];
origCOUNT_36 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), CF, LSHIFT_32(origDEST_35, (MINUS_32(32bv32, origCOUNT_36)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv32)), origDEST_35[32:31], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv32)), AF, unconstrained_5);

label_0x7a84:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 33bv64))));

label_0x7a89:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x7a8b:
RCX := (0bv32 ++ RCX[32:0]);

label_0x7a8d:
RDX := PLUS_64((PLUS_64(0bv64, 31380bv64)), 0bv64)[64:0];

label_0x7a94:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7a97:
mem := STORE_LE_32(mem, PLUS_64(RSP, 292bv64), RAX[32:0]);

label_0x7a9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7aa6:
t1_45 := RAX;
t2_46 := 648bv64;
RAX := PLUS_64(RAX, t2_46);
CF := bool2bv(LT_64(RAX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7aac:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x7ab4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7abc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7ac2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7ac7:
t_53 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))))[1:0]));
SF := t_53[64:63];
ZF := bool2bv(0bv64 == t_53);

label_0x7aca:
if (bv2bool(ZF)) {
  goto label_0x7acd;
}

label_0x7acc:
assume false;

label_0x7acd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7ad5:
origDEST_57 := RAX;
origCOUNT_58 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_11);

label_0x7ad9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7ae0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7ae4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7aec:
origDEST_63 := RCX;
origCOUNT_64 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), CF, LSHIFT_64(origDEST_63, (MINUS_64(64bv64, origCOUNT_64)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_64 == 1bv64)), origDEST_63[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), AF, unconstrained_13);

label_0x7af0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_14;
SF := unconstrained_15;
AF := unconstrained_16;
PF := unconstrained_17;

label_0x7af4:
if (bv2bool(CF)) {
  goto label_0x7af7;
}

label_0x7af6:
assume false;

label_0x7af7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7aff:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 292bv64)));

label_0x7b06:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7b08:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7b10:
t1_69 := RAX;
t2_70 := 128bv64;
RAX := PLUS_64(RAX, t2_70);
CF := bool2bv(LT_64(RAX, t1_69));
OF := AND_1((bool2bv((t1_69[64:63]) == (t2_70[64:63]))), (XOR_1((t1_69[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_69)), t2_70)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7b16:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7b1e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 92bv64)));

label_0x7b21:
t1_75 := RAX;
t2_76 := RCX;
RAX := PLUS_64(RAX, t2_76);
CF := bool2bv(LT_64(RAX, t1_75));
OF := AND_1((bool2bv((t1_75[64:63]) == (t2_76[64:63]))), (XOR_1((t1_75[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_75)), t2_76)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7b24:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x7b2c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x7b34:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7b3a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7b3f:
t_83 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0x7b42:
if (bv2bool(ZF)) {
  goto label_0x7b45;
}

label_0x7b44:
assume false;

label_0x7b45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x7b4d:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, LSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), origDEST_87[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_21);

label_0x7b51:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7b58:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7b5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x7b64:
origDEST_93 := RCX;
origCOUNT_94 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_23);

label_0x7b68:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_24;
SF := unconstrained_25;
AF := unconstrained_26;
PF := unconstrained_27;

label_0x7b6c:
if (bv2bool(CF)) {
  goto label_0x7b6f;
}

label_0x7b6e:
assume false;

label_0x7b6f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x7b77:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x7b7a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7b82:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7b86:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7b8e:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7b92:
t1_99 := RCX;
t2_100 := RAX;
RCX := PLUS_64(RCX, t2_100);
CF := bool2bv(LT_64(RCX, t1_99));
OF := AND_1((bool2bv((t1_99[64:63]) == (t2_100[64:63]))), (XOR_1((t1_99[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_99)), t2_100)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7b95:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RCX);

label_0x7b9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7ba5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7bab:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7bb0:
t_107 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)), 2bv64)), (XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)), 2bv64)), (XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)))))[1:0]));
SF := t_107[64:63];
ZF := bool2bv(0bv64 == t_107);

label_0x7bb3:
if (bv2bool(ZF)) {
  goto label_0x7bb6;
}

label_0x7bb5:
assume false;

label_0x7bb6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7bbe:
origDEST_111 := RAX;
origCOUNT_112 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_31);

label_0x7bc2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7bc9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7bcd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7bd5:
origDEST_117 := RCX;
origCOUNT_118 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_33);

label_0x7bd9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_34;
SF := unconstrained_35;
AF := unconstrained_36;
PF := unconstrained_37;

label_0x7bdd:
if (bv2bool(CF)) {
  goto label_0x7be0;
}

label_0x7bdf:
assume false;

label_0x7be0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7be8:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 33bv64))));

label_0x7bed:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7bef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7bf7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x7bfa:
t_123 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_123[32:31]) == (1bv32[32:31]))), (XOR_1((t_123[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_123)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7bfc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 248bv64), RAX[32:0]);

label_0x7c03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7c0b:
t1_127 := RAX;
t2_128 := 108bv64;
RAX := PLUS_64(RAX, t2_128);
CF := bool2bv(LT_64(RAX, t1_127));
OF := AND_1((bool2bv((t1_127[64:63]) == (t2_128[64:63]))), (XOR_1((t1_127[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_127)), t2_128)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7c0f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x7c17:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x7c1f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7c25:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7c2a:
t_135 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_39;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)), 2bv64)), (XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)), 2bv64)), (XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)))))[1:0]));
SF := t_135[64:63];
ZF := bool2bv(0bv64 == t_135);

label_0x7c2d:
if (bv2bool(ZF)) {
  goto label_0x7c30;
}

label_0x7c2f:
assume false;

label_0x7c30:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x7c38:
origDEST_139 := RAX;
origCOUNT_140 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_41);

label_0x7c3c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7c43:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7c47:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x7c4f:
origDEST_145 := RCX;
origCOUNT_146 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), CF, LSHIFT_64(origDEST_145, (MINUS_64(64bv64, origCOUNT_146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_146 == 1bv64)), origDEST_145[64:63], unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), AF, unconstrained_43);

label_0x7c53:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_44;
SF := unconstrained_45;
AF := unconstrained_46;
PF := unconstrained_47;

label_0x7c57:
if (bv2bool(CF)) {
  goto label_0x7c5a;
}

label_0x7c59:
assume false;

label_0x7c5a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x7c62:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 248bv64)));

label_0x7c69:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7c6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7c73:
t1_151 := RAX;
t2_152 := 92bv64;
RAX := PLUS_64(RAX, t2_152);
CF := bool2bv(LT_64(RAX, t1_151));
OF := AND_1((bool2bv((t1_151[64:63]) == (t2_152[64:63]))), (XOR_1((t1_151[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_151)), t2_152)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7c77:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x7c7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7c87:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7c8d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7c92:
t_159 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))))[1:0]));
SF := t_159[64:63];
ZF := bool2bv(0bv64 == t_159);

label_0x7c95:
if (bv2bool(ZF)) {
  goto label_0x7c98;
}

label_0x7c97:
assume false;

label_0x7c98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7ca0:
origDEST_163 := RAX;
origCOUNT_164 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_51);

label_0x7ca4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7cab:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7caf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7cb7:
origDEST_169 := RCX;
origCOUNT_170 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), CF, LSHIFT_64(origDEST_169, (MINUS_64(64bv64, origCOUNT_170)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv64)), origDEST_169[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), AF, unconstrained_53);

label_0x7cbb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x7cbf:
if (bv2bool(CF)) {
  goto label_0x7cc2;
}

label_0x7cc1:
assume false;

label_0x7cc2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7cca:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x7cce:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7cd0:
goto label_0x7e61;

label_0x7cd5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7cdd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x7ce0:
t_175 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_175)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_175, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))))[1:0]));
SF := t_175[32:31];
ZF := bool2bv(0bv32 == t_175);

label_0x7ce4:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x7cfb;
}

label_0x7ce6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7cee:
t_179 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), t_179)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_179, (LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))))), 255bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))))[1:0]));
SF := t_179[32:31];
ZF := bool2bv(0bv32 == t_179);

label_0x7cf5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x7de5;
}

label_0x7cfb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7d03:
t_183 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), t_183)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_183, (LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))))[1:0]));
SF := t_183[32:31];
ZF := bool2bv(0bv32 == t_183);

label_0x7d0a:
if (bv2bool(NOT_1(CF))) {
  goto label_0x7d19;
}

label_0x7d0c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7d14:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 32025bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7d19"} true;
call arbitrary_func();

label_0x7d19:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7d21:
t1_187 := RAX;
t2_188 := 92bv64;
RAX := PLUS_64(RAX, t2_188);
CF := bool2bv(LT_64(RAX, t1_187));
OF := AND_1((bool2bv((t1_187[64:63]) == (t2_188[64:63]))), (XOR_1((t1_187[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_187)), t2_188)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7d25:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x7d2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x7d35:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7d3b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7d40:
t_195 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))))[1:0]));
SF := t_195[64:63];
ZF := bool2bv(0bv64 == t_195);

label_0x7d43:
if (bv2bool(ZF)) {
  goto label_0x7d46;
}

label_0x7d45:
assume false;

label_0x7d46:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x7d4e:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_61);

label_0x7d52:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7d59:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7d5d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x7d65:
origDEST_205 := RCX;
origCOUNT_206 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_62));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_63);

label_0x7d69:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_64;
SF := unconstrained_65;
AF := unconstrained_66;
PF := unconstrained_67;

label_0x7d6d:
if (bv2bool(CF)) {
  goto label_0x7d70;
}

label_0x7d6f:
assume false;

label_0x7d70:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x7d78:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x7d7c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7d7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7d86:
t1_211 := RAX;
t2_212 := 96bv64;
RAX := PLUS_64(RAX, t2_212);
CF := bool2bv(LT_64(RAX, t1_211));
OF := AND_1((bool2bv((t1_211[64:63]) == (t2_212[64:63]))), (XOR_1((t1_211[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_211)), t2_212)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7d8a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x7d92:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7d9a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7da0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7da5:
t_219 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)), 2bv64)), (XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)), 2bv64)), (XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)))))[1:0]));
SF := t_219[64:63];
ZF := bool2bv(0bv64 == t_219);

label_0x7da8:
if (bv2bool(ZF)) {
  goto label_0x7dab;
}

label_0x7daa:
assume false;

label_0x7dab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7db3:
origDEST_223 := RAX;
origCOUNT_224 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), CF, LSHIFT_64(origDEST_223, (MINUS_64(64bv64, origCOUNT_224)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_224 == 1bv64)), origDEST_223[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), AF, unconstrained_71);

label_0x7db7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7dbe:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7dc2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7dca:
origDEST_229 := RCX;
origCOUNT_230 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), CF, LSHIFT_64(origDEST_229, (MINUS_64(64bv64, origCOUNT_230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_230 == 1bv64)), origDEST_229[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), AF, unconstrained_73);

label_0x7dce:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x7dd2:
if (bv2bool(CF)) {
  goto label_0x7dd5;
}

label_0x7dd4:
assume false;

label_0x7dd5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7ddd:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x7de3:
goto label_0x7e61;

label_0x7de5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7ded:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 96bv64)));

label_0x7df0:
t_235 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_235[32:31]) == (1bv32[32:31]))), (XOR_1((t_235[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_235)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7df2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 252bv64), RAX[32:0]);

label_0x7df9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7e01:
t1_239 := RAX;
t2_240 := 96bv64;
RAX := PLUS_64(RAX, t2_240);
CF := bool2bv(LT_64(RAX, t1_239));
OF := AND_1((bool2bv((t1_239[64:63]) == (t2_240[64:63]))), (XOR_1((t1_239[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_239)), t2_240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7e05:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x7e0d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x7e15:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7e1b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7e20:
t_247 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))))[1:0]));
SF := t_247[64:63];
ZF := bool2bv(0bv64 == t_247);

label_0x7e23:
if (bv2bool(ZF)) {
  goto label_0x7e26;
}

label_0x7e25:
assume false;

label_0x7e26:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x7e2e:
origDEST_251 := RAX;
origCOUNT_252 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), CF, LSHIFT_64(origDEST_251, (MINUS_64(64bv64, origCOUNT_252)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv64)), origDEST_251[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), AF, unconstrained_81);

label_0x7e32:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7e39:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7e3d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x7e45:
origDEST_257 := RCX;
origCOUNT_258 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_83);

label_0x7e49:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_84;
SF := unconstrained_85;
AF := unconstrained_86;
PF := unconstrained_87;

label_0x7e4d:
if (bv2bool(CF)) {
  goto label_0x7e50;
}

label_0x7e4f:
assume false;

label_0x7e50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x7e58:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 252bv64)));

label_0x7e5f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7e61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7e69:
RAX := LOAD_LE_64(mem, RAX);

label_0x7e6c:
RAX := LOAD_LE_64(mem, RAX);

label_0x7e6f:
t_263 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_263[64:63]) == (1bv64[64:63]))), (XOR_1((t_263[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_263)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7e72:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0x7e7a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7e82:
RAX := LOAD_LE_64(mem, RAX);

label_0x7e85:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x7e8d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x7e95:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_88;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7e9b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7ea0:
t_269 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_89;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_269, 4bv64)), t_269)), 2bv64)), (XOR_64((RSHIFT_64(t_269, 4bv64)), t_269)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_269, 4bv64)), t_269)), 2bv64)), (XOR_64((RSHIFT_64(t_269, 4bv64)), t_269)))))[1:0]));
SF := t_269[64:63];
ZF := bool2bv(0bv64 == t_269);

label_0x7ea3:
if (bv2bool(ZF)) {
  goto label_0x7ea6;
}

label_0x7ea5:
assume false;

label_0x7ea6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x7eae:
origDEST_273 := RAX;
origCOUNT_274 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), CF, LSHIFT_64(origDEST_273, (MINUS_64(64bv64, origCOUNT_274)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_274 == 1bv64)), origDEST_273[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), AF, unconstrained_91);

label_0x7eb2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7eb9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7ebd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x7ec5:
origDEST_279 := RCX;
origCOUNT_280 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), CF, LSHIFT_64(origDEST_279, (MINUS_64(64bv64, origCOUNT_280)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_280 == 1bv64)), origDEST_279[64:63], unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), AF, unconstrained_93);

label_0x7ec9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_94;
SF := unconstrained_95;
AF := unconstrained_96;
PF := unconstrained_97;

label_0x7ecd:
if (bv2bool(CF)) {
  goto label_0x7ed0;
}

label_0x7ecf:
assume false;

label_0x7ed0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x7ed8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x7ee0:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x7ee3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7eeb:
RAX := LOAD_LE_64(mem, RAX);

label_0x7eee:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x7ef1:
t_285 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_285, 1bv32)), (XOR_32(t_285, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_285)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7ef3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 256bv64), RAX[32:0]);

label_0x7efa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7f02:
RAX := LOAD_LE_64(mem, RAX);

label_0x7f05:
t1_289 := RAX;
t2_290 := 8bv64;
RAX := PLUS_64(RAX, t2_290);
CF := bool2bv(LT_64(RAX, t1_289));
OF := AND_1((bool2bv((t1_289[64:63]) == (t2_290[64:63]))), (XOR_1((t1_289[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_289)), t2_290)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7f09:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x7f0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x7f13:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_98;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7f19:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7f1e:
t_297 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_99;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)), 2bv64)), (XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)), 2bv64)), (XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)))))[1:0]));
SF := t_297[64:63];
ZF := bool2bv(0bv64 == t_297);

label_0x7f21:
if (bv2bool(ZF)) {
  goto label_0x7f24;
}

label_0x7f23:
assume false;

label_0x7f24:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x7f29:
origDEST_301 := RAX;
origCOUNT_302 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), CF, LSHIFT_64(origDEST_301, (MINUS_64(64bv64, origCOUNT_302)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_302 == 1bv64)), origDEST_301[64:63], unconstrained_100));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), AF, unconstrained_101);

label_0x7f2d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7f34:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7f38:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x7f3d:
origDEST_307 := RCX;
origCOUNT_308 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), CF, LSHIFT_64(origDEST_307, (MINUS_64(64bv64, origCOUNT_308)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_308 == 1bv64)), origDEST_307[64:63], unconstrained_102));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), AF, unconstrained_103);

label_0x7f41:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_104;
SF := unconstrained_105;
AF := unconstrained_106;
PF := unconstrained_107;

label_0x7f45:
if (bv2bool(CF)) {
  goto label_0x7f48;
}

label_0x7f47:
assume false;

label_0x7f48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x7f4d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 256bv64)));

label_0x7f54:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7f56:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7f5e:
RAX := LOAD_LE_64(mem, RAX);

label_0x7f61:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 12bv64)));

label_0x7f64:
t_313 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_313[32:31]) == (1bv32[32:31]))), (XOR_1((t_313[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_313)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7f66:
mem := STORE_LE_32(mem, PLUS_64(RSP, 260bv64), RAX[32:0]);

label_0x7f6d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7f75:
RAX := LOAD_LE_64(mem, RAX);

label_0x7f78:
t1_317 := RAX;
t2_318 := 12bv64;
RAX := PLUS_64(RAX, t2_318);
CF := bool2bv(LT_64(RAX, t1_317));
OF := AND_1((bool2bv((t1_317[64:63]) == (t2_318[64:63]))), (XOR_1((t1_317[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_317)), t2_318)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7f7c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x7f84:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x7f8c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_108;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7f92:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7f97:
t_325 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_109;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)), 2bv64)), (XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)), 2bv64)), (XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)))))[1:0]));
SF := t_325[64:63];
ZF := bool2bv(0bv64 == t_325);

label_0x7f9a:
if (bv2bool(ZF)) {
  goto label_0x7f9d;
}

label_0x7f9c:
assume false;

label_0x7f9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x7fa5:
origDEST_329 := RAX;
origCOUNT_330 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), CF, LSHIFT_64(origDEST_329, (MINUS_64(64bv64, origCOUNT_330)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_330 == 1bv64)), origDEST_329[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), AF, unconstrained_111);

label_0x7fa9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7fb0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7fb4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x7fbc:
origDEST_335 := RCX;
origCOUNT_336 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), CF, LSHIFT_64(origDEST_335, (MINUS_64(64bv64, origCOUNT_336)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_336 == 1bv64)), origDEST_335[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), AF, unconstrained_113);

label_0x7fc0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_114;
SF := unconstrained_115;
AF := unconstrained_116;
PF := unconstrained_117;

label_0x7fc4:
if (bv2bool(CF)) {
  goto label_0x7fc7;
}

label_0x7fc6:
assume false;

label_0x7fc7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x7fcf:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 260bv64)));

label_0x7fd6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7fd8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7fe0:
RAX := LOAD_LE_64(mem, RAX);

label_0x7fe3:
t_341 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), t_341)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_341, (LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)), 2bv32)), (XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)), 2bv32)), (XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)))))[1:0]));
SF := t_341[32:31];
ZF := bool2bv(0bv32 == t_341);

label_0x7fe7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x806f;
}

label_0x7fed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x7ff5:
RAX := LOAD_LE_64(mem, RAX);

label_0x7ff8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0x7ffb:
t_345 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_345[32:31]) == (1bv32[32:31]))), (XOR_1((t_345[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_345)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7ffd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 264bv64), RAX[32:0]);

label_0x8004:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x800c:
RAX := LOAD_LE_64(mem, RAX);

label_0x800f:
t1_349 := RAX;
t2_350 := 16bv64;
RAX := PLUS_64(RAX, t2_350);
CF := bool2bv(LT_64(RAX, t1_349));
OF := AND_1((bool2bv((t1_349[64:63]) == (t2_350[64:63]))), (XOR_1((t1_349[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_349)), t2_350)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8013:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0x801b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x8023:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8029:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x802e:
t_357 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_119;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))))[1:0]));
SF := t_357[64:63];
ZF := bool2bv(0bv64 == t_357);

label_0x8031:
if (bv2bool(ZF)) {
  goto label_0x8034;
}

label_0x8033:
assume false;

label_0x8034:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x803c:
origDEST_361 := RAX;
origCOUNT_362 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), CF, LSHIFT_64(origDEST_361, (MINUS_64(64bv64, origCOUNT_362)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_362 == 1bv64)), origDEST_361[64:63], unconstrained_120));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), AF, unconstrained_121);

label_0x8040:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8047:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x804b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x8053:
origDEST_367 := RCX;
origCOUNT_368 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, LSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), origDEST_367[64:63], unconstrained_122));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_123);

label_0x8057:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_124;
SF := unconstrained_125;
AF := unconstrained_126;
PF := unconstrained_127;

label_0x805b:
if (bv2bool(CF)) {
  goto label_0x805e;
}

label_0x805d:
assume false;

label_0x805e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x8066:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 264bv64)));

label_0x806d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x806f:
goto label_0x79d3;

label_0x8074:
goto label_0x8731;

label_0x8079:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_128;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x807b:
t_373 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_373)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_373, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_373, 4bv32)), t_373)), 2bv32)), (XOR_32((RSHIFT_32(t_373, 4bv32)), t_373)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_373, 4bv32)), t_373)), 2bv32)), (XOR_32((RSHIFT_32(t_373, 4bv32)), t_373)))))[1:0]));
SF := t_373[32:31];
ZF := bool2bv(0bv32 == t_373);

label_0x807e:
if (bv2bool(ZF)) {
  goto label_0x8731;
}

label_0x8084:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x808c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8094:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 112bv64)));

label_0x8097:
t_377 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), t_377)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_377, (LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))))[1:0]));
SF := t_377[32:31];
ZF := bool2bv(0bv32 == t_377);

label_0x809a:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x80a1;
}

label_0x809c:
goto label_0x8731;

label_0x80a1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x80a9:
RAX := LOAD_LE_64(mem, RAX);

label_0x80ac:
t_381 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_381)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_381, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))))[1:0]));
SF := t_381[32:31];
ZF := bool2bv(0bv32 == t_381);

label_0x80b0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x80b7;
}

label_0x80b2:
goto label_0x8731;

label_0x80b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x80bf:
t_385 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_385)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_385, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))))[1:0]));
SF := t_385[32:31];
ZF := bool2bv(0bv32 == t_385);

label_0x80c3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x80ca;
}

label_0x80c5:
goto label_0x8731;

label_0x80ca:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x80cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x80d7:
RAX := LOAD_LE_64(mem, RAX);

label_0x80da:
RAX := LOAD_LE_64(mem, RAX);

label_0x80dd:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x80e0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x80e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x80ec:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x80ef:
t_389 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_389)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_389, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_389, 4bv32)), t_389)), 2bv32)), (XOR_32((RSHIFT_32(t_389, 4bv32)), t_389)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_389, 4bv32)), t_389)), 2bv32)), (XOR_32((RSHIFT_32(t_389, 4bv32)), t_389)))))[1:0]));
SF := t_389[32:31];
ZF := bool2bv(0bv32 == t_389);

label_0x80f3:
if (bv2bool(ZF)) {
  goto label_0x8352;
}

label_0x80f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8101:
t_393 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), t_393)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_393, (LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_393, 4bv32)), t_393)), 2bv32)), (XOR_32((RSHIFT_32(t_393, 4bv32)), t_393)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_393, 4bv32)), t_393)), 2bv32)), (XOR_32((RSHIFT_32(t_393, 4bv32)), t_393)))))[1:0]));
SF := t_393[32:31];
ZF := bool2bv(0bv32 == t_393);

label_0x8105:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8352;
}

label_0x810b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8113:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 92bv64))));

label_0x8117:
mem := STORE_LE_8(mem, PLUS_64(RSP, 34bv64), RAX[32:0][8:0]);

label_0x811b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8123:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 648bv64)));

label_0x8129:
origDEST_397 := RAX[32:0];
origCOUNT_398 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), CF, RSHIFT_32(origDEST_397, (MINUS_32(32bv32, origCOUNT_398)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_398 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv32)), AF, unconstrained_130);

label_0x812c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8134:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 648bv64)));

label_0x813a:
origDEST_403 := RCX[32:0];
origCOUNT_404 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), CF, LSHIFT_32(origDEST_403, (MINUS_32(32bv32, origCOUNT_404)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_404 == 1bv32)), origDEST_403[32:31], unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv32)), AF, unconstrained_132);

label_0x813d:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 34bv64))));

label_0x8142:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x8144:
RCX := (0bv32 ++ RCX[32:0]);

label_0x8146:
RDX := PLUS_64((PLUS_64(0bv64, 33101bv64)), 0bv64)[64:0];

label_0x814d:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_134;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8150:
mem := STORE_LE_32(mem, PLUS_64(RSP, 268bv64), RAX[32:0]);

label_0x8157:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x815f:
t1_413 := RAX;
t2_414 := 648bv64;
RAX := PLUS_64(RAX, t2_414);
CF := bool2bv(LT_64(RAX, t1_413));
OF := AND_1((bool2bv((t1_413[64:63]) == (t2_414[64:63]))), (XOR_1((t1_413[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_413)), t2_414)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8165:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0x816d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x8175:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x817b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8180:
t_421 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)), 2bv64)), (XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)), 2bv64)), (XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)))))[1:0]));
SF := t_421[64:63];
ZF := bool2bv(0bv64 == t_421);

label_0x8183:
if (bv2bool(ZF)) {
  goto label_0x8186;
}

label_0x8185:
assume false;

label_0x8186:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x818e:
origDEST_425 := RAX;
origCOUNT_426 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), CF, LSHIFT_64(origDEST_425, (MINUS_64(64bv64, origCOUNT_426)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_426 == 1bv64)), origDEST_425[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), AF, unconstrained_138);

label_0x8192:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8199:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x819d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x81a5:
origDEST_431 := RCX;
origCOUNT_432 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), CF, LSHIFT_64(origDEST_431, (MINUS_64(64bv64, origCOUNT_432)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_432 == 1bv64)), origDEST_431[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), AF, unconstrained_140);

label_0x81a9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_141;
SF := unconstrained_142;
AF := unconstrained_143;
PF := unconstrained_144;

label_0x81ad:
if (bv2bool(CF)) {
  goto label_0x81b0;
}

label_0x81af:
assume false;

label_0x81b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x81b8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 268bv64)));

label_0x81bf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x81c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x81c9:
t1_437 := RAX;
t2_438 := 128bv64;
RAX := PLUS_64(RAX, t2_438);
CF := bool2bv(LT_64(RAX, t1_437));
OF := AND_1((bool2bv((t1_437[64:63]) == (t2_438[64:63]))), (XOR_1((t1_437[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_437)), t2_438)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x81cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x81d7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 92bv64)));

label_0x81da:
t1_443 := RAX;
t2_444 := RCX;
RAX := PLUS_64(RAX, t2_444);
CF := bool2bv(LT_64(RAX, t1_443));
OF := AND_1((bool2bv((t1_443[64:63]) == (t2_444[64:63]))), (XOR_1((t1_443[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_443)), t2_444)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x81dd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x81e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x81e7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_145;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x81ed:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x81f2:
t_451 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)), 2bv64)), (XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)), 2bv64)), (XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)))))[1:0]));
SF := t_451[64:63];
ZF := bool2bv(0bv64 == t_451);

label_0x81f5:
if (bv2bool(ZF)) {
  goto label_0x81f8;
}

label_0x81f7:
assume false;

label_0x81f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x81fd:
origDEST_455 := RAX;
origCOUNT_456 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), CF, LSHIFT_64(origDEST_455, (MINUS_64(64bv64, origCOUNT_456)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_456 == 1bv64)), origDEST_455[64:63], unconstrained_147));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), AF, unconstrained_148);

label_0x8201:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8208:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x820c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8211:
origDEST_461 := RCX;
origCOUNT_462 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), CF, LSHIFT_64(origDEST_461, (MINUS_64(64bv64, origCOUNT_462)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_462 == 1bv64)), origDEST_461[64:63], unconstrained_149));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), AF, unconstrained_150);

label_0x8215:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_151;
SF := unconstrained_152;
AF := unconstrained_153;
PF := unconstrained_154;

label_0x8219:
if (bv2bool(CF)) {
  goto label_0x821c;
}

label_0x821b:
assume false;

label_0x821c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8221:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x8224:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x822c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x8230:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8238:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x823c:
t1_467 := RCX;
t2_468 := RAX;
RCX := PLUS_64(RCX, t2_468);
CF := bool2bv(LT_64(RCX, t1_467));
OF := AND_1((bool2bv((t1_467[64:63]) == (t2_468[64:63]))), (XOR_1((t1_467[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_467)), t2_468)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x823f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0x8244:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8249:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_155;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x824f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8254:
t_475 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_475, 4bv64)), t_475)), 2bv64)), (XOR_64((RSHIFT_64(t_475, 4bv64)), t_475)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_475, 4bv64)), t_475)), 2bv64)), (XOR_64((RSHIFT_64(t_475, 4bv64)), t_475)))))[1:0]));
SF := t_475[64:63];
ZF := bool2bv(0bv64 == t_475);

label_0x8257:
if (bv2bool(ZF)) {
  goto label_0x825a;
}

label_0x8259:
assume false;

label_0x825a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x825f:
origDEST_479 := RAX;
origCOUNT_480 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), CF, LSHIFT_64(origDEST_479, (MINUS_64(64bv64, origCOUNT_480)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_480 == 1bv64)), origDEST_479[64:63], unconstrained_157));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_480 == 0bv64)), AF, unconstrained_158);

label_0x8263:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x826a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x826e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8273:
origDEST_485 := RCX;
origCOUNT_486 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), CF, LSHIFT_64(origDEST_485, (MINUS_64(64bv64, origCOUNT_486)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_486 == 1bv64)), origDEST_485[64:63], unconstrained_159));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_486 == 0bv64)), AF, unconstrained_160);

label_0x8277:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_161;
SF := unconstrained_162;
AF := unconstrained_163;
PF := unconstrained_164;

label_0x827b:
if (bv2bool(CF)) {
  goto label_0x827e;
}

label_0x827d:
assume false;

label_0x827e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8283:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 34bv64))));

label_0x8288:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x828a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8292:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x8295:
t_491 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_491[32:31]) == (1bv32[32:31]))), (XOR_1((t_491[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_491)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8297:
mem := STORE_LE_32(mem, PLUS_64(RSP, 272bv64), RAX[32:0]);

label_0x829e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x82a6:
t1_495 := RAX;
t2_496 := 108bv64;
RAX := PLUS_64(RAX, t2_496);
CF := bool2bv(LT_64(RAX, t1_495));
OF := AND_1((bool2bv((t1_495[64:63]) == (t2_496[64:63]))), (XOR_1((t1_495[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_495)), t2_496)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x82aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x82af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x82b4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_165;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x82ba:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x82bf:
t_503 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_166;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))))[1:0]));
SF := t_503[64:63];
ZF := bool2bv(0bv64 == t_503);

label_0x82c2:
if (bv2bool(ZF)) {
  goto label_0x82c5;
}

label_0x82c4:
assume false;

label_0x82c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x82ca:
origDEST_507 := RAX;
origCOUNT_508 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), CF, LSHIFT_64(origDEST_507, (MINUS_64(64bv64, origCOUNT_508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_508 == 1bv64)), origDEST_507[64:63], unconstrained_167));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), AF, unconstrained_168);

label_0x82ce:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x82d5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x82d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x82de:
origDEST_513 := RCX;
origCOUNT_514 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), CF, LSHIFT_64(origDEST_513, (MINUS_64(64bv64, origCOUNT_514)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_514 == 1bv64)), origDEST_513[64:63], unconstrained_169));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), AF, unconstrained_170);

label_0x82e2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_171;
SF := unconstrained_172;
AF := unconstrained_173;
PF := unconstrained_174;

label_0x82e6:
if (bv2bool(CF)) {
  goto label_0x82e9;
}

label_0x82e8:
assume false;

label_0x82e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x82ee:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 272bv64)));

label_0x82f5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x82f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x82ff:
t1_519 := RAX;
t2_520 := 92bv64;
RAX := PLUS_64(RAX, t2_520);
CF := bool2bv(LT_64(RAX, t1_519));
OF := AND_1((bool2bv((t1_519[64:63]) == (t2_520[64:63]))), (XOR_1((t1_519[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_519)), t2_520)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8303:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x8308:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x830d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_175;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8313:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8318:
t_527 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)), 2bv64)), (XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)), 2bv64)), (XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)))))[1:0]));
SF := t_527[64:63];
ZF := bool2bv(0bv64 == t_527);

label_0x831b:
if (bv2bool(ZF)) {
  goto label_0x831e;
}

label_0x831d:
assume false;

label_0x831e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x8323:
origDEST_531 := RAX;
origCOUNT_532 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), CF, LSHIFT_64(origDEST_531, (MINUS_64(64bv64, origCOUNT_532)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_532 == 1bv64)), origDEST_531[64:63], unconstrained_177));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), AF, unconstrained_178);

label_0x8327:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x832e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8332:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x8337:
origDEST_537 := RCX;
origCOUNT_538 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), CF, LSHIFT_64(origDEST_537, (MINUS_64(64bv64, origCOUNT_538)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_538 == 1bv64)), origDEST_537[64:63], unconstrained_179));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), AF, unconstrained_180);

label_0x833b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_181;
SF := unconstrained_182;
AF := unconstrained_183;
PF := unconstrained_184;

label_0x833f:
if (bv2bool(CF)) {
  goto label_0x8342;
}

label_0x8341:
assume false;

label_0x8342:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x8347:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x834b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x834d:
goto label_0x84b1;

label_0x8352:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x835a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x835d:
t_543 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_543)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_543, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_543, 4bv32)), t_543)), 2bv32)), (XOR_32((RSHIFT_32(t_543, 4bv32)), t_543)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_543, 4bv32)), t_543)), 2bv32)), (XOR_32((RSHIFT_32(t_543, 4bv32)), t_543)))))[1:0]));
SF := t_543[32:31];
ZF := bool2bv(0bv32 == t_543);

label_0x8361:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8378;
}

label_0x8363:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x836b:
t_547 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), 255bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))), t_547)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_547, (LOAD_LE_32(mem, PLUS_64(RAX, 96bv64))))), 255bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))))[1:0]));
SF := t_547[32:31];
ZF := bool2bv(0bv32 == t_547);

label_0x8372:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8444;
}

label_0x8378:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8380:
t_551 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))), t_551)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_551, (LOAD_LE_32(mem, PLUS_64(RAX, 92bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)), 2bv32)), (XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)), 2bv32)), (XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)))))[1:0]));
SF := t_551[32:31];
ZF := bool2bv(0bv32 == t_551);

label_0x8387:
if (bv2bool(NOT_1(CF))) {
  goto label_0x8396;
}

label_0x8389:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8391:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 33686bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8396"} true;
call arbitrary_func();

label_0x8396:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x839e:
t1_555 := RAX;
t2_556 := 92bv64;
RAX := PLUS_64(RAX, t2_556);
CF := bool2bv(LT_64(RAX, t1_555));
OF := AND_1((bool2bv((t1_555[64:63]) == (t2_556[64:63]))), (XOR_1((t1_555[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_555)), t2_556)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x83a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x83a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x83ac:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_185;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x83b2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x83b7:
t_563 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))))[1:0]));
SF := t_563[64:63];
ZF := bool2bv(0bv64 == t_563);

label_0x83ba:
if (bv2bool(ZF)) {
  goto label_0x83bd;
}

label_0x83bc:
assume false;

label_0x83bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x83c2:
origDEST_567 := RAX;
origCOUNT_568 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), CF, LSHIFT_64(origDEST_567, (MINUS_64(64bv64, origCOUNT_568)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_568 == 1bv64)), origDEST_567[64:63], unconstrained_187));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), AF, unconstrained_188);

label_0x83c6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x83cd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x83d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x83d6:
origDEST_573 := RCX;
origCOUNT_574 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), CF, LSHIFT_64(origDEST_573, (MINUS_64(64bv64, origCOUNT_574)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_574 == 1bv64)), origDEST_573[64:63], unconstrained_189));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), AF, unconstrained_190);

label_0x83da:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_191;
SF := unconstrained_192;
AF := unconstrained_193;
PF := unconstrained_194;

label_0x83de:
if (bv2bool(CF)) {
  goto label_0x83e1;
}

label_0x83e0:
assume false;

label_0x83e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x83e6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x83ea:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x83ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x83f4:
t1_579 := RAX;
t2_580 := 96bv64;
RAX := PLUS_64(RAX, t2_580);
CF := bool2bv(LT_64(RAX, t1_579));
OF := AND_1((bool2bv((t1_579[64:63]) == (t2_580[64:63]))), (XOR_1((t1_579[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_579)), t2_580)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x83f8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x83fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x8402:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_195;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8408:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x840d:
t_587 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_196;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)), 2bv64)), (XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)), 2bv64)), (XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)))))[1:0]));
SF := t_587[64:63];
ZF := bool2bv(0bv64 == t_587);

label_0x8410:
if (bv2bool(ZF)) {
  goto label_0x8413;
}

label_0x8412:
assume false;

label_0x8413:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x8418:
origDEST_591 := RAX;
origCOUNT_592 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), CF, LSHIFT_64(origDEST_591, (MINUS_64(64bv64, origCOUNT_592)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_592 == 1bv64)), origDEST_591[64:63], unconstrained_197));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), AF, unconstrained_198);

label_0x841c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8423:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8427:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x842c:
origDEST_597 := RCX;
origCOUNT_598 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), CF, LSHIFT_64(origDEST_597, (MINUS_64(64bv64, origCOUNT_598)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_598 == 1bv64)), origDEST_597[64:63], unconstrained_199));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), AF, unconstrained_200);

label_0x8430:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_201;
SF := unconstrained_202;
AF := unconstrained_203;
PF := unconstrained_204;

label_0x8434:
if (bv2bool(CF)) {
  goto label_0x8437;
}

label_0x8436:
assume false;

label_0x8437:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x843c:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x8442:
goto label_0x84b1;

label_0x8444:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x844c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 96bv64)));

label_0x844f:
t_603 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_603[32:31]) == (1bv32[32:31]))), (XOR_1((t_603[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_603)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8451:
mem := STORE_LE_32(mem, PLUS_64(RSP, 276bv64), RAX[32:0]);

label_0x8458:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8460:
t1_607 := RAX;
t2_608 := 96bv64;
RAX := PLUS_64(RAX, t2_608);
CF := bool2bv(LT_64(RAX, t1_607));
OF := AND_1((bool2bv((t1_607[64:63]) == (t2_608[64:63]))), (XOR_1((t1_607[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_607)), t2_608)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8464:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x8469:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x846e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_205;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8474:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8479:
t_615 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_206;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)), 2bv64)), (XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)), 2bv64)), (XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)))))[1:0]));
SF := t_615[64:63];
ZF := bool2bv(0bv64 == t_615);

label_0x847c:
if (bv2bool(ZF)) {
  goto label_0x847f;
}

label_0x847e:
assume false;

label_0x847f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x8484:
origDEST_619 := RAX;
origCOUNT_620 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), CF, LSHIFT_64(origDEST_619, (MINUS_64(64bv64, origCOUNT_620)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_620 == 1bv64)), origDEST_619[64:63], unconstrained_207));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), AF, unconstrained_208);

label_0x8488:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x848f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8493:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x8498:
origDEST_625 := RCX;
origCOUNT_626 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), CF, LSHIFT_64(origDEST_625, (MINUS_64(64bv64, origCOUNT_626)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_626 == 1bv64)), origDEST_625[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), AF, unconstrained_210);

label_0x849c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_211;
SF := unconstrained_212;
AF := unconstrained_213;
PF := unconstrained_214;

label_0x84a0:
if (bv2bool(CF)) {
  goto label_0x84a3;
}

label_0x84a2:
assume false;

label_0x84a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x84a8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 276bv64)));

label_0x84af:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x84b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x84b9:
RAX := LOAD_LE_64(mem, RAX);

label_0x84bc:
RAX := LOAD_LE_64(mem, RAX);

label_0x84bf:
t_631 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_631[64:63]) == (1bv64[64:63]))), (XOR_1((t_631[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_631)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x84c2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RAX);

label_0x84ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x84d2:
RAX := LOAD_LE_64(mem, RAX);

label_0x84d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x84da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x84df:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_215;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x84e5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x84ea:
t_637 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_216;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_637, 4bv64)), t_637)), 2bv64)), (XOR_64((RSHIFT_64(t_637, 4bv64)), t_637)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_637, 4bv64)), t_637)), 2bv64)), (XOR_64((RSHIFT_64(t_637, 4bv64)), t_637)))))[1:0]));
SF := t_637[64:63];
ZF := bool2bv(0bv64 == t_637);

label_0x84ed:
if (bv2bool(ZF)) {
  goto label_0x84f0;
}

label_0x84ef:
assume false;

label_0x84f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x84f5:
origDEST_641 := RAX;
origCOUNT_642 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), CF, LSHIFT_64(origDEST_641, (MINUS_64(64bv64, origCOUNT_642)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_642 == 1bv64)), origDEST_641[64:63], unconstrained_217));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), AF, unconstrained_218);

label_0x84f9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8500:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8504:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x8509:
origDEST_647 := RCX;
origCOUNT_648 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), CF, LSHIFT_64(origDEST_647, (MINUS_64(64bv64, origCOUNT_648)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_648 == 1bv64)), origDEST_647[64:63], unconstrained_219));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_648 == 0bv64)), AF, unconstrained_220);

label_0x850d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_221;
SF := unconstrained_222;
AF := unconstrained_223;
PF := unconstrained_224;

label_0x8511:
if (bv2bool(CF)) {
  goto label_0x8514;
}

label_0x8513:
assume false;

label_0x8514:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x8519:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x8521:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x8524:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x852c:
RAX := LOAD_LE_64(mem, RAX);

label_0x852f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x8532:
t_653 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_653, 1bv32)), (XOR_32(t_653, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_653)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8534:
mem := STORE_LE_32(mem, PLUS_64(RSP, 280bv64), RAX[32:0]);

label_0x853b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8543:
RAX := LOAD_LE_64(mem, RAX);

label_0x8546:
t1_657 := RAX;
t2_658 := 8bv64;
RAX := PLUS_64(RAX, t2_658);
CF := bool2bv(LT_64(RAX, t1_657));
OF := AND_1((bool2bv((t1_657[64:63]) == (t2_658[64:63]))), (XOR_1((t1_657[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_657)), t2_658)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x854a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x8552:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x855a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_225;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8560:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8565:
t_665 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_226;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)), 2bv64)), (XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)), 2bv64)), (XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)))))[1:0]));
SF := t_665[64:63];
ZF := bool2bv(0bv64 == t_665);

label_0x8568:
if (bv2bool(ZF)) {
  goto label_0x856b;
}

label_0x856a:
assume false;

label_0x856b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x8573:
origDEST_669 := RAX;
origCOUNT_670 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), CF, LSHIFT_64(origDEST_669, (MINUS_64(64bv64, origCOUNT_670)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_670 == 1bv64)), origDEST_669[64:63], unconstrained_227));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), AF, unconstrained_228);

label_0x8577:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x857e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8582:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x858a:
origDEST_675 := RCX;
origCOUNT_676 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), CF, LSHIFT_64(origDEST_675, (MINUS_64(64bv64, origCOUNT_676)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_676 == 1bv64)), origDEST_675[64:63], unconstrained_229));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), AF, unconstrained_230);

label_0x858e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_231;
SF := unconstrained_232;
AF := unconstrained_233;
PF := unconstrained_234;

label_0x8592:
if (bv2bool(CF)) {
  goto label_0x8595;
}

label_0x8594:
assume false;

label_0x8595:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x859d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x85a4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x85a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x85ae:
RAX := LOAD_LE_64(mem, RAX);

label_0x85b1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 12bv64)));

label_0x85b4:
t_681 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_681[32:31]) == (1bv32[32:31]))), (XOR_1((t_681[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_681)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x85b6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 284bv64), RAX[32:0]);

label_0x85bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x85c5:
RAX := LOAD_LE_64(mem, RAX);

label_0x85c8:
t1_685 := RAX;
t2_686 := 12bv64;
RAX := PLUS_64(RAX, t2_686);
CF := bool2bv(LT_64(RAX, t1_685));
OF := AND_1((bool2bv((t1_685[64:63]) == (t2_686[64:63]))), (XOR_1((t1_685[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_685)), t2_686)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x85cc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x85d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x85d6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_235;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x85dc:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x85e1:
t_693 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_236;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)), 2bv64)), (XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)), 2bv64)), (XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)))))[1:0]));
SF := t_693[64:63];
ZF := bool2bv(0bv64 == t_693);

label_0x85e4:
if (bv2bool(ZF)) {
  goto label_0x85e7;
}

label_0x85e6:
assume false;

label_0x85e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x85ec:
origDEST_697 := RAX;
origCOUNT_698 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), CF, LSHIFT_64(origDEST_697, (MINUS_64(64bv64, origCOUNT_698)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_698 == 1bv64)), origDEST_697[64:63], unconstrained_237));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), AF, unconstrained_238);

label_0x85f0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x85f7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x85fb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x8600:
origDEST_703 := RCX;
origCOUNT_704 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), CF, LSHIFT_64(origDEST_703, (MINUS_64(64bv64, origCOUNT_704)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_704 == 1bv64)), origDEST_703[64:63], unconstrained_239));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), AF, unconstrained_240);

label_0x8604:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_241;
SF := unconstrained_242;
AF := unconstrained_243;
PF := unconstrained_244;

label_0x8608:
if (bv2bool(CF)) {
  goto label_0x860b;
}

label_0x860a:
assume false;

label_0x860b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x8610:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 284bv64)));

label_0x8617:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8619:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8621:
RAX := LOAD_LE_64(mem, RAX);

label_0x8624:
t_709 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), t_709)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_709, (LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)), 2bv32)), (XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)), 2bv32)), (XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)))))[1:0]));
SF := t_709[32:31];
ZF := bool2bv(0bv32 == t_709);

label_0x8628:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x86b0;
}

label_0x862e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x8636:
RAX := LOAD_LE_64(mem, RAX);

label_0x8639:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0x863c:
t_713 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_713[32:31]) == (1bv32[32:31]))), (XOR_1((t_713[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_713)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x863e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 288bv64), RAX[32:0]);

label_0x8645:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x864d:
RAX := LOAD_LE_64(mem, RAX);

label_0x8650:
t1_717 := RAX;
t2_718 := 16bv64;
RAX := PLUS_64(RAX, t2_718);
CF := bool2bv(LT_64(RAX, t1_717));
OF := AND_1((bool2bv((t1_717[64:63]) == (t2_718[64:63]))), (XOR_1((t1_717[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_717)), t2_718)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8654:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x865c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x8664:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_245;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x866a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x866f:
t_725 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_246;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_725, 4bv64)), t_725)), 2bv64)), (XOR_64((RSHIFT_64(t_725, 4bv64)), t_725)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_725, 4bv64)), t_725)), 2bv64)), (XOR_64((RSHIFT_64(t_725, 4bv64)), t_725)))))[1:0]));
SF := t_725[64:63];
ZF := bool2bv(0bv64 == t_725);

label_0x8672:
if (bv2bool(ZF)) {
  goto label_0x8675;
}

label_0x8674:
assume false;

label_0x8675:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x867d:
origDEST_729 := RAX;
origCOUNT_730 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), CF, LSHIFT_64(origDEST_729, (MINUS_64(64bv64, origCOUNT_730)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_730 == 1bv64)), origDEST_729[64:63], unconstrained_247));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_730 == 0bv64)), AF, unconstrained_248);

label_0x8681:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8688:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x868c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x8694:
origDEST_735 := RCX;
origCOUNT_736 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), CF, LSHIFT_64(origDEST_735, (MINUS_64(64bv64, origCOUNT_736)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_736 == 1bv64)), origDEST_735[64:63], unconstrained_249));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_736 == 0bv64)), AF, unconstrained_250);

label_0x8698:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_251;
SF := unconstrained_252;
AF := unconstrained_253;
PF := unconstrained_254;

label_0x869c:
if (bv2bool(CF)) {
  goto label_0x869f;
}

label_0x869e:
assume false;

label_0x869f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x86a7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x86ae:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x86b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x86b8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0x86bb:
t_741 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_741, 1bv32)), (XOR_32(t_741, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_741)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x86bd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 296bv64), RAX[32:0]);

label_0x86c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x86cc:
t1_745 := RAX;
t2_746 := 16bv64;
RAX := PLUS_64(RAX, t2_746);
CF := bool2bv(LT_64(RAX, t1_745));
OF := AND_1((bool2bv((t1_745[64:63]) == (t2_746[64:63]))), (XOR_1((t1_745[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_745)), t2_746)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x86d0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x86d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x86e0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_255;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x86e6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x86eb:
t_753 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_256;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_753, 4bv64)), t_753)), 2bv64)), (XOR_64((RSHIFT_64(t_753, 4bv64)), t_753)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_753, 4bv64)), t_753)), 2bv64)), (XOR_64((RSHIFT_64(t_753, 4bv64)), t_753)))))[1:0]));
SF := t_753[64:63];
ZF := bool2bv(0bv64 == t_753);

label_0x86ee:
if (bv2bool(ZF)) {
  goto label_0x86f1;
}

label_0x86f0:
assume false;

label_0x86f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x86f9:
origDEST_757 := RAX;
origCOUNT_758 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), CF, LSHIFT_64(origDEST_757, (MINUS_64(64bv64, origCOUNT_758)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_758 == 1bv64)), origDEST_757[64:63], unconstrained_257));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_758 == 0bv64)), AF, unconstrained_258);

label_0x86fd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8704:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8708:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x8710:
origDEST_763 := RCX;
origCOUNT_764 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), CF, LSHIFT_64(origDEST_763, (MINUS_64(64bv64, origCOUNT_764)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_764 == 1bv64)), origDEST_763[64:63], unconstrained_259));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_764 == 0bv64)), AF, unconstrained_260);

label_0x8714:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_261;
SF := unconstrained_262;
AF := unconstrained_263;
PF := unconstrained_264;

label_0x8718:
if (bv2bool(CF)) {
  goto label_0x871b;
}

label_0x871a:
assume false;

label_0x871b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x8723:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 296bv64)));

label_0x872a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x872c:
goto label_0x8079;

label_0x8731:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x8736:
t1_769 := RSP;
t2_770 := 328bv64;
RSP := PLUS_64(RSP, t2_770);
CF := bool2bv(LT_64(RSP, t1_769));
OF := AND_1((bool2bv((t1_769[64:63]) == (t2_770[64:63]))), (XOR_1((t1_769[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_769)), t2_770)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x873d:

ra_775 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_112,origCOUNT_118,origCOUNT_140,origCOUNT_146,origCOUNT_164,origCOUNT_170,origCOUNT_200,origCOUNT_206,origCOUNT_224,origCOUNT_230,origCOUNT_252,origCOUNT_258,origCOUNT_274,origCOUNT_280,origCOUNT_30,origCOUNT_302,origCOUNT_308,origCOUNT_330,origCOUNT_336,origCOUNT_36,origCOUNT_362,origCOUNT_368,origCOUNT_398,origCOUNT_404,origCOUNT_426,origCOUNT_432,origCOUNT_456,origCOUNT_462,origCOUNT_480,origCOUNT_486,origCOUNT_508,origCOUNT_514,origCOUNT_532,origCOUNT_538,origCOUNT_568,origCOUNT_574,origCOUNT_58,origCOUNT_592,origCOUNT_598,origCOUNT_620,origCOUNT_626,origCOUNT_64,origCOUNT_642,origCOUNT_648,origCOUNT_670,origCOUNT_676,origCOUNT_698,origCOUNT_704,origCOUNT_730,origCOUNT_736,origCOUNT_758,origCOUNT_764,origCOUNT_88,origCOUNT_94,origDEST_111,origDEST_117,origDEST_139,origDEST_145,origDEST_163,origDEST_169,origDEST_199,origDEST_205,origDEST_223,origDEST_229,origDEST_251,origDEST_257,origDEST_273,origDEST_279,origDEST_29,origDEST_301,origDEST_307,origDEST_329,origDEST_335,origDEST_35,origDEST_361,origDEST_367,origDEST_397,origDEST_403,origDEST_425,origDEST_431,origDEST_455,origDEST_461,origDEST_479,origDEST_485,origDEST_507,origDEST_513,origDEST_531,origDEST_537,origDEST_567,origDEST_57,origDEST_573,origDEST_591,origDEST_597,origDEST_619,origDEST_625,origDEST_63,origDEST_641,origDEST_647,origDEST_669,origDEST_675,origDEST_697,origDEST_703,origDEST_729,origDEST_735,origDEST_757,origDEST_763,origDEST_87,origDEST_93,ra_775,t1_127,t1_151,t1_187,t1_211,t1_239,t1_289,t1_317,t1_349,t1_413,t1_437,t1_443,t1_45,t1_467,t1_495,t1_519,t1_555,t1_579,t1_607,t1_657,t1_685,t1_69,t1_717,t1_745,t1_75,t1_769,t1_99,t2_100,t2_128,t2_152,t2_188,t2_212,t2_240,t2_290,t2_318,t2_350,t2_414,t2_438,t2_444,t2_46,t2_468,t2_496,t2_520,t2_556,t2_580,t2_608,t2_658,t2_686,t2_70,t2_718,t2_746,t2_76,t2_770,t_1,t_107,t_123,t_13,t_135,t_159,t_17,t_175,t_179,t_183,t_195,t_21,t_219,t_235,t_247,t_25,t_263,t_269,t_285,t_297,t_313,t_325,t_341,t_345,t_357,t_373,t_377,t_381,t_385,t_389,t_393,t_421,t_451,t_475,t_491,t_5,t_503,t_527,t_53,t_543,t_547,t_551,t_563,t_587,t_603,t_615,t_631,t_637,t_653,t_665,t_681,t_693,t_709,t_713,t_725,t_741,t_753,t_83,t_9;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_100: bv1;
const unconstrained_101: bv1;
const unconstrained_102: bv1;
const unconstrained_103: bv1;
const unconstrained_104: bv1;
const unconstrained_105: bv1;
const unconstrained_106: bv1;
const unconstrained_107: bv1;
const unconstrained_108: bv1;
const unconstrained_109: bv1;
const unconstrained_11: bv1;
const unconstrained_110: bv1;
const unconstrained_111: bv1;
const unconstrained_112: bv1;
const unconstrained_113: bv1;
const unconstrained_114: bv1;
const unconstrained_115: bv1;
const unconstrained_116: bv1;
const unconstrained_117: bv1;
const unconstrained_118: bv1;
const unconstrained_119: bv1;
const unconstrained_12: bv1;
const unconstrained_120: bv1;
const unconstrained_121: bv1;
const unconstrained_122: bv1;
const unconstrained_123: bv1;
const unconstrained_124: bv1;
const unconstrained_125: bv1;
const unconstrained_126: bv1;
const unconstrained_127: bv1;
const unconstrained_128: bv1;
const unconstrained_129: bv1;
const unconstrained_13: bv1;
const unconstrained_130: bv1;
const unconstrained_131: bv1;
const unconstrained_132: bv1;
const unconstrained_133: bv1;
const unconstrained_134: bv1;
const unconstrained_135: bv1;
const unconstrained_136: bv1;
const unconstrained_137: bv1;
const unconstrained_138: bv1;
const unconstrained_139: bv1;
const unconstrained_14: bv1;
const unconstrained_140: bv1;
const unconstrained_141: bv1;
const unconstrained_142: bv1;
const unconstrained_143: bv1;
const unconstrained_144: bv1;
const unconstrained_145: bv1;
const unconstrained_146: bv1;
const unconstrained_147: bv1;
const unconstrained_148: bv1;
const unconstrained_149: bv1;
const unconstrained_15: bv1;
const unconstrained_150: bv1;
const unconstrained_151: bv1;
const unconstrained_152: bv1;
const unconstrained_153: bv1;
const unconstrained_154: bv1;
const unconstrained_155: bv1;
const unconstrained_156: bv1;
const unconstrained_157: bv1;
const unconstrained_158: bv1;
const unconstrained_159: bv1;
const unconstrained_16: bv1;
const unconstrained_160: bv1;
const unconstrained_161: bv1;
const unconstrained_162: bv1;
const unconstrained_163: bv1;
const unconstrained_164: bv1;
const unconstrained_165: bv1;
const unconstrained_166: bv1;
const unconstrained_167: bv1;
const unconstrained_168: bv1;
const unconstrained_169: bv1;
const unconstrained_17: bv1;
const unconstrained_170: bv1;
const unconstrained_171: bv1;
const unconstrained_172: bv1;
const unconstrained_173: bv1;
const unconstrained_174: bv1;
const unconstrained_175: bv1;
const unconstrained_176: bv1;
const unconstrained_177: bv1;
const unconstrained_178: bv1;
const unconstrained_179: bv1;
const unconstrained_18: bv1;
const unconstrained_180: bv1;
const unconstrained_181: bv1;
const unconstrained_182: bv1;
const unconstrained_183: bv1;
const unconstrained_184: bv1;
const unconstrained_185: bv1;
const unconstrained_186: bv1;
const unconstrained_187: bv1;
const unconstrained_188: bv1;
const unconstrained_189: bv1;
const unconstrained_19: bv1;
const unconstrained_190: bv1;
const unconstrained_191: bv1;
const unconstrained_192: bv1;
const unconstrained_193: bv1;
const unconstrained_194: bv1;
const unconstrained_195: bv1;
const unconstrained_196: bv1;
const unconstrained_197: bv1;
const unconstrained_198: bv1;
const unconstrained_199: bv1;
const unconstrained_2: bv1;
const unconstrained_20: bv1;
const unconstrained_200: bv1;
const unconstrained_201: bv1;
const unconstrained_202: bv1;
const unconstrained_203: bv1;
const unconstrained_204: bv1;
const unconstrained_205: bv1;
const unconstrained_206: bv1;
const unconstrained_207: bv1;
const unconstrained_208: bv1;
const unconstrained_209: bv1;
const unconstrained_21: bv1;
const unconstrained_210: bv1;
const unconstrained_211: bv1;
const unconstrained_212: bv1;
const unconstrained_213: bv1;
const unconstrained_214: bv1;
const unconstrained_215: bv1;
const unconstrained_216: bv1;
const unconstrained_217: bv1;
const unconstrained_218: bv1;
const unconstrained_219: bv1;
const unconstrained_22: bv1;
const unconstrained_220: bv1;
const unconstrained_221: bv1;
const unconstrained_222: bv1;
const unconstrained_223: bv1;
const unconstrained_224: bv1;
const unconstrained_225: bv1;
const unconstrained_226: bv1;
const unconstrained_227: bv1;
const unconstrained_228: bv1;
const unconstrained_229: bv1;
const unconstrained_23: bv1;
const unconstrained_230: bv1;
const unconstrained_231: bv1;
const unconstrained_232: bv1;
const unconstrained_233: bv1;
const unconstrained_234: bv1;
const unconstrained_235: bv1;
const unconstrained_236: bv1;
const unconstrained_237: bv1;
const unconstrained_238: bv1;
const unconstrained_239: bv1;
const unconstrained_24: bv1;
const unconstrained_240: bv1;
const unconstrained_241: bv1;
const unconstrained_242: bv1;
const unconstrained_243: bv1;
const unconstrained_244: bv1;
const unconstrained_245: bv1;
const unconstrained_246: bv1;
const unconstrained_247: bv1;
const unconstrained_248: bv1;
const unconstrained_249: bv1;
const unconstrained_25: bv1;
const unconstrained_250: bv1;
const unconstrained_251: bv1;
const unconstrained_252: bv1;
const unconstrained_253: bv1;
const unconstrained_254: bv1;
const unconstrained_255: bv1;
const unconstrained_256: bv1;
const unconstrained_257: bv1;
const unconstrained_258: bv1;
const unconstrained_259: bv1;
const unconstrained_26: bv1;
const unconstrained_260: bv1;
const unconstrained_261: bv1;
const unconstrained_262: bv1;
const unconstrained_263: bv1;
const unconstrained_264: bv1;
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
const unconstrained_98: bv1;
const unconstrained_99: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_112: bv64;
var origCOUNT_118: bv64;
var origCOUNT_140: bv64;
var origCOUNT_146: bv64;
var origCOUNT_164: bv64;
var origCOUNT_170: bv64;
var origCOUNT_200: bv64;
var origCOUNT_206: bv64;
var origCOUNT_224: bv64;
var origCOUNT_230: bv64;
var origCOUNT_252: bv64;
var origCOUNT_258: bv64;
var origCOUNT_274: bv64;
var origCOUNT_280: bv64;
var origCOUNT_30: bv32;
var origCOUNT_302: bv64;
var origCOUNT_308: bv64;
var origCOUNT_330: bv64;
var origCOUNT_336: bv64;
var origCOUNT_36: bv32;
var origCOUNT_362: bv64;
var origCOUNT_368: bv64;
var origCOUNT_398: bv32;
var origCOUNT_404: bv32;
var origCOUNT_426: bv64;
var origCOUNT_432: bv64;
var origCOUNT_456: bv64;
var origCOUNT_462: bv64;
var origCOUNT_480: bv64;
var origCOUNT_486: bv64;
var origCOUNT_508: bv64;
var origCOUNT_514: bv64;
var origCOUNT_532: bv64;
var origCOUNT_538: bv64;
var origCOUNT_568: bv64;
var origCOUNT_574: bv64;
var origCOUNT_58: bv64;
var origCOUNT_592: bv64;
var origCOUNT_598: bv64;
var origCOUNT_620: bv64;
var origCOUNT_626: bv64;
var origCOUNT_64: bv64;
var origCOUNT_642: bv64;
var origCOUNT_648: bv64;
var origCOUNT_670: bv64;
var origCOUNT_676: bv64;
var origCOUNT_698: bv64;
var origCOUNT_704: bv64;
var origCOUNT_730: bv64;
var origCOUNT_736: bv64;
var origCOUNT_758: bv64;
var origCOUNT_764: bv64;
var origCOUNT_88: bv64;
var origCOUNT_94: bv64;
var origDEST_111: bv64;
var origDEST_117: bv64;
var origDEST_139: bv64;
var origDEST_145: bv64;
var origDEST_163: bv64;
var origDEST_169: bv64;
var origDEST_199: bv64;
var origDEST_205: bv64;
var origDEST_223: bv64;
var origDEST_229: bv64;
var origDEST_251: bv64;
var origDEST_257: bv64;
var origDEST_273: bv64;
var origDEST_279: bv64;
var origDEST_29: bv32;
var origDEST_301: bv64;
var origDEST_307: bv64;
var origDEST_329: bv64;
var origDEST_335: bv64;
var origDEST_35: bv32;
var origDEST_361: bv64;
var origDEST_367: bv64;
var origDEST_397: bv32;
var origDEST_403: bv32;
var origDEST_425: bv64;
var origDEST_431: bv64;
var origDEST_455: bv64;
var origDEST_461: bv64;
var origDEST_479: bv64;
var origDEST_485: bv64;
var origDEST_507: bv64;
var origDEST_513: bv64;
var origDEST_531: bv64;
var origDEST_537: bv64;
var origDEST_567: bv64;
var origDEST_57: bv64;
var origDEST_573: bv64;
var origDEST_591: bv64;
var origDEST_597: bv64;
var origDEST_619: bv64;
var origDEST_625: bv64;
var origDEST_63: bv64;
var origDEST_641: bv64;
var origDEST_647: bv64;
var origDEST_669: bv64;
var origDEST_675: bv64;
var origDEST_697: bv64;
var origDEST_703: bv64;
var origDEST_729: bv64;
var origDEST_735: bv64;
var origDEST_757: bv64;
var origDEST_763: bv64;
var origDEST_87: bv64;
var origDEST_93: bv64;
var ra_775: bv64;
var t1_127: bv64;
var t1_151: bv64;
var t1_187: bv64;
var t1_211: bv64;
var t1_239: bv64;
var t1_289: bv64;
var t1_317: bv64;
var t1_349: bv64;
var t1_413: bv64;
var t1_437: bv64;
var t1_443: bv64;
var t1_45: bv64;
var t1_467: bv64;
var t1_495: bv64;
var t1_519: bv64;
var t1_555: bv64;
var t1_579: bv64;
var t1_607: bv64;
var t1_657: bv64;
var t1_685: bv64;
var t1_69: bv64;
var t1_717: bv64;
var t1_745: bv64;
var t1_75: bv64;
var t1_769: bv64;
var t1_99: bv64;
var t2_100: bv64;
var t2_128: bv64;
var t2_152: bv64;
var t2_188: bv64;
var t2_212: bv64;
var t2_240: bv64;
var t2_290: bv64;
var t2_318: bv64;
var t2_350: bv64;
var t2_414: bv64;
var t2_438: bv64;
var t2_444: bv64;
var t2_46: bv64;
var t2_468: bv64;
var t2_496: bv64;
var t2_520: bv64;
var t2_556: bv64;
var t2_580: bv64;
var t2_608: bv64;
var t2_658: bv64;
var t2_686: bv64;
var t2_70: bv64;
var t2_718: bv64;
var t2_746: bv64;
var t2_76: bv64;
var t2_770: bv64;
var t_1: bv64;
var t_107: bv64;
var t_123: bv32;
var t_13: bv32;
var t_135: bv64;
var t_159: bv64;
var t_17: bv32;
var t_175: bv32;
var t_179: bv32;
var t_183: bv32;
var t_195: bv64;
var t_21: bv32;
var t_219: bv64;
var t_235: bv32;
var t_247: bv64;
var t_25: bv32;
var t_263: bv64;
var t_269: bv64;
var t_285: bv32;
var t_297: bv64;
var t_313: bv32;
var t_325: bv64;
var t_341: bv32;
var t_345: bv32;
var t_357: bv64;
var t_373: bv32;
var t_377: bv32;
var t_381: bv32;
var t_385: bv32;
var t_389: bv32;
var t_393: bv32;
var t_421: bv64;
var t_451: bv64;
var t_475: bv64;
var t_491: bv32;
var t_5: bv32;
var t_503: bv64;
var t_527: bv64;
var t_53: bv64;
var t_543: bv32;
var t_547: bv32;
var t_551: bv32;
var t_563: bv64;
var t_587: bv64;
var t_603: bv32;
var t_615: bv64;
var t_631: bv64;
var t_637: bv64;
var t_653: bv32;
var t_665: bv64;
var t_681: bv32;
var t_693: bv64;
var t_709: bv32;
var t_713: bv32;
var t_725: bv64;
var t_741: bv32;
var t_753: bv64;
var t_83: bv64;
var t_9: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3456bv64);
axiom policy(4592bv64);
axiom policy(5008bv64);
axiom policy(6912bv64);
axiom policy(7904bv64);
axiom policy(8336bv64);
axiom policy(11024bv64);
axiom policy(11664bv64);
axiom policy(12624bv64);
axiom policy(15504bv64);
axiom policy(17728bv64);
axiom policy(19952bv64);
axiom policy(20048bv64);
axiom policy(22784bv64);
axiom policy(24016bv64);
axiom policy(25328bv64);
axiom policy(25344bv64);
axiom policy(25392bv64);
axiom policy(25440bv64);
axiom policy(25968bv64);
axiom policy(26352bv64);
axiom policy(26368bv64);
axiom policy(26736bv64);
axiom policy(26880bv64);
axiom policy(26992bv64);
axiom policy(27104bv64);
axiom policy(27152bv64);
axiom policy(27216bv64);
axiom policy(27264bv64);
axiom policy(27840bv64);
axiom policy(28032bv64);
axiom policy(28080bv64);
axiom policy(31088bv64);
axiom policy(31152bv64);
axiom policy(34640bv64);
axiom policy(35376bv64);
axiom policy(36064bv64);
axiom policy(45632bv64);
axiom policy(57008bv64);
axiom policy(57072bv64);
