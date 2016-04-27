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
axiom _function_addr_low == 36064bv64;
axiom _function_addr_high == 43770bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x8ce0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x8ce5:
t_1 := RSP;
RSP := MINUS_64(RSP, 840bv64);
CF := bool2bv(LT_64(t_1, 840bv64));
OF := AND_64((XOR_64(t_1, 840bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 840bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x8cec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8cf4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 20bv64))));

label_0x8cf8:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x8cfa:
if (bv2bool(ZF)) {
  goto label_0xa976;
}

label_0x8d00:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_2;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x8d02:
t_9 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x8d05:
if (bv2bool(ZF)) {
  goto label_0xa971;
}

label_0x8d0b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x8d0d:
t_13 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x8d10:
if (bv2bool(ZF)) {
  goto label_0x9114;
}

label_0x8d16:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8d1e:
RAX := LOAD_LE_64(mem, RAX);

label_0x8d21:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x8d25:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8d2e;
}

label_0x8d27:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x8d29:
goto label_0xb22f;

label_0x8d2e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8d36:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x8d3a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8d41;
}

label_0x8d3c:
goto label_0x9114;

label_0x8d41:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8d49:
t1_25 := RAX;
t2_26 := 12bv64;
RAX := PLUS_64(RAX, t2_26);
CF := bool2bv(LT_64(RAX, t1_25));
OF := AND_1((bool2bv((t1_25[64:63]) == (t2_26[64:63]))), (XOR_1((t1_25[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_25)), t2_26)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8d4d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 728bv64), RAX);

label_0x8d55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8d5d:
RAX := LOAD_LE_64(mem, RAX);

label_0x8d60:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0x8d64:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0x8d6c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x8d74:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8d7a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8d7f:
t_33 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x8d82:
if (bv2bool(ZF)) {
  goto label_0x8d85;
}

label_0x8d84:
assume false;

label_0x8d85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x8d8d:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_8);

label_0x8d91:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8d98:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8d9c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x8da4:
origDEST_43 := RCX;
origCOUNT_44 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_10);

label_0x8da8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_11;
SF := unconstrained_12;
AF := unconstrained_13;
PF := unconstrained_14;

label_0x8dac:
if (bv2bool(CF)) {
  goto label_0x8daf;
}

label_0x8dae:
assume false;

label_0x8daf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x8db7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 728bv64));

label_0x8dbf:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x8dc2:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x8dc4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8dcc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64)));

label_0x8dd2:
origDEST_49 := RAX[32:0];
origCOUNT_50 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), CF, RSHIFT_32(origDEST_49, (MINUS_32(32bv32, origCOUNT_50)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), AF, unconstrained_16);

label_0x8dd5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8ddd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3184bv64)));

label_0x8de3:
origDEST_55 := RCX[32:0];
origCOUNT_56 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), CF, LSHIFT_32(origDEST_55, (MINUS_32(32bv32, origCOUNT_56)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv32)), origDEST_55[32:31], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), AF, unconstrained_18);

label_0x8de6:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8dee:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, 12bv64))));

label_0x8df2:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x8df4:
RCX := (0bv32 ++ RCX[32:0]);

label_0x8df6:
RDX := PLUS_64((PLUS_64(0bv64, 36349bv64)), 0bv64)[64:0];

label_0x8dfd:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8e00:
mem := STORE_LE_32(mem, PLUS_64(RSP, 584bv64), RAX[32:0]);

label_0x8e07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8e0f:
t1_65 := RAX;
t2_66 := 3184bv64;
RAX := PLUS_64(RAX, t2_66);
CF := bool2bv(LT_64(RAX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8e15:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RAX);

label_0x8e1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x8e25:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8e2b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8e30:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0x8e33:
if (bv2bool(ZF)) {
  goto label_0x8e36;
}

label_0x8e35:
assume false;

label_0x8e36:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x8e3e:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_24);

label_0x8e42:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8e49:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8e4d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x8e55:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_26);

label_0x8e59:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x8e5d:
if (bv2bool(CF)) {
  goto label_0x8e60;
}

label_0x8e5f:
assume false;

label_0x8e60:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x8e68:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 584bv64)));

label_0x8e6f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8e71:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8e79:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0x8e7c:
t_89 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_89, 1bv32)), (XOR_32(t_89, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_89)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8e7e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 720bv64), RAX[32:0]);

label_0x8e85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8e8d:
t1_93 := RAX;
t2_94 := 16bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8e91:
mem := STORE_LE_64(mem, PLUS_64(RSP, 376bv64), RAX);

label_0x8e99:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0x8ea1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8ea7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8eac:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x8eaf:
if (bv2bool(ZF)) {
  goto label_0x8eb2;
}

label_0x8eb1:
assume false;

label_0x8eb2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0x8eba:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_34);

label_0x8ebe:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8ec5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8ec9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0x8ed1:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_36);

label_0x8ed5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x8ed9:
if (bv2bool(CF)) {
  goto label_0x8edc;
}

label_0x8edb:
assume false;

label_0x8edc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0x8ee4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 720bv64)));

label_0x8eeb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8eed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8ef5:
RAX := LOAD_LE_64(mem, RAX);

label_0x8ef8:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0x8efc:
t_117 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_117[64:63]) == (1bv64[64:63]))), (XOR_1((t_117[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_117)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8eff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 736bv64), RAX);

label_0x8f07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8f0f:
RAX := LOAD_LE_64(mem, RAX);

label_0x8f12:
t1_121 := RAX;
t2_122 := 24bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8f16:
mem := STORE_LE_64(mem, PLUS_64(RSP, 384bv64), RAX);

label_0x8f1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x8f26:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8f2c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8f31:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x8f34:
if (bv2bool(ZF)) {
  goto label_0x8f37;
}

label_0x8f36:
assume false;

label_0x8f37:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x8f3f:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_44);

label_0x8f43:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8f4a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8f4e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x8f56:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_46);

label_0x8f5a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x8f5e:
if (bv2bool(CF)) {
  goto label_0x8f61;
}

label_0x8f60:
assume false;

label_0x8f61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x8f69:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 736bv64));

label_0x8f71:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x8f74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8f7c:
RAX := LOAD_LE_64(mem, RAX);

label_0x8f7f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0x8f82:
t_145 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_145, 1bv32)), (XOR_32(t_145, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8f84:
mem := STORE_LE_32(mem, PLUS_64(RSP, 588bv64), RAX[32:0]);

label_0x8f8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8f93:
RAX := LOAD_LE_64(mem, RAX);

label_0x8f96:
t1_149 := RAX;
t2_150 := 32bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8f9a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 392bv64), RAX);

label_0x8fa2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x8faa:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8fb0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8fb5:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x8fb8:
if (bv2bool(ZF)) {
  goto label_0x8fbb;
}

label_0x8fba:
assume false;

label_0x8fbb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x8fc3:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_54);

label_0x8fc7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8fce:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8fd2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x8fda:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_56);

label_0x8fde:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x8fe2:
if (bv2bool(CF)) {
  goto label_0x8fe5;
}

label_0x8fe4:
assume false;

label_0x8fe5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x8fed:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 588bv64)));

label_0x8ff4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8ff6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x8ffe:
RAX := LOAD_LE_64(mem, RAX);

label_0x9001:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 36bv64)));

label_0x9004:
t_173 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_173[32:31]) == (1bv32[32:31]))), (XOR_1((t_173[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_173)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9006:
mem := STORE_LE_32(mem, PLUS_64(RSP, 592bv64), RAX[32:0]);

label_0x900d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9015:
RAX := LOAD_LE_64(mem, RAX);

label_0x9018:
t1_177 := RAX;
t2_178 := 36bv64;
RAX := PLUS_64(RAX, t2_178);
CF := bool2bv(LT_64(RAX, t1_177));
OF := AND_1((bool2bv((t1_177[64:63]) == (t2_178[64:63]))), (XOR_1((t1_177[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_177)), t2_178)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x901c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 400bv64), RAX);

label_0x9024:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x902c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9032:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9037:
t_185 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))))[1:0]));
SF := t_185[64:63];
ZF := bool2bv(0bv64 == t_185);

label_0x903a:
if (bv2bool(ZF)) {
  goto label_0x903d;
}

label_0x903c:
assume false;

label_0x903d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x9045:
origDEST_189 := RAX;
origCOUNT_190 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_64);

label_0x9049:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9050:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9054:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x905c:
origDEST_195 := RCX;
origCOUNT_196 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), CF, LSHIFT_64(origDEST_195, (MINUS_64(64bv64, origCOUNT_196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_196 == 1bv64)), origDEST_195[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), AF, unconstrained_66);

label_0x9060:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x9064:
if (bv2bool(CF)) {
  goto label_0x9067;
}

label_0x9066:
assume false;

label_0x9067:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x906f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 592bv64)));

label_0x9076:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9078:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9080:
RAX := LOAD_LE_64(mem, RAX);

label_0x9083:
t_201 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), t_201)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_201, (LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))))[1:0]));
SF := t_201[32:31];
ZF := bool2bv(0bv32 == t_201);

label_0x9087:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x910f;
}

label_0x908d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9095:
RAX := LOAD_LE_64(mem, RAX);

label_0x9098:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 40bv64)));

label_0x909b:
t_205 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_205[32:31]) == (1bv32[32:31]))), (XOR_1((t_205[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_205)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x909d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 596bv64), RAX[32:0]);

label_0x90a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x90ac:
RAX := LOAD_LE_64(mem, RAX);

label_0x90af:
t1_209 := RAX;
t2_210 := 40bv64;
RAX := PLUS_64(RAX, t2_210);
CF := bool2bv(LT_64(RAX, t1_209));
OF := AND_1((bool2bv((t1_209[64:63]) == (t2_210[64:63]))), (XOR_1((t1_209[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_209)), t2_210)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x90b3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 408bv64), RAX);

label_0x90bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x90c3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x90c9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x90ce:
t_217 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))))[1:0]));
SF := t_217[64:63];
ZF := bool2bv(0bv64 == t_217);

label_0x90d1:
if (bv2bool(ZF)) {
  goto label_0x90d4;
}

label_0x90d3:
assume false;

label_0x90d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x90dc:
origDEST_221 := RAX;
origCOUNT_222 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), CF, LSHIFT_64(origDEST_221, (MINUS_64(64bv64, origCOUNT_222)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_222 == 1bv64)), origDEST_221[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), AF, unconstrained_74);

label_0x90e0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x90e7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x90eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x90f3:
origDEST_227 := RCX;
origCOUNT_228 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_76);

label_0x90f7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_77;
SF := unconstrained_78;
AF := unconstrained_79;
PF := unconstrained_80;

label_0x90fb:
if (bv2bool(CF)) {
  goto label_0x90fe;
}

label_0x90fd:
assume false;

label_0x90fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x9106:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 596bv64)));

label_0x910d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x910f:
goto label_0x8d0b;

label_0x9114:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x911c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x9122:
t_233 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_233[32:31]) == (1bv32[32:31]))), (XOR_1((t_233[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_233)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9124:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x912c:
t_237 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_237)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_237, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))))[1:0]));
SF := t_237[32:31];
ZF := bool2bv(0bv32 == t_237);

label_0x9132:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x913b;
}

label_0x9134:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_81;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x9136:
goto label_0xb22f;

label_0x913b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9143:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x9149:
t_241 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_241[32:31]) == (1bv32[32:31]))), (XOR_1((t_241[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_241)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x914b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9153:
t_245 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_245)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_245, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))))[1:0]));
SF := t_245[32:31];
ZF := bool2bv(0bv32 == t_245);

label_0x9159:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x9162;
}

label_0x915b:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x915d:
goto label_0xb22f;

label_0x9162:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x916a:
t1_249 := RAX;
t2_250 := 16bv64;
RAX := PLUS_64(RAX, t2_250);
CF := bool2bv(LT_64(RAX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x916e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 416bv64), RAX);

label_0x9176:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x917e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9184:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9189:
t_257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_83;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))))[1:0]));
SF := t_257[64:63];
ZF := bool2bv(0bv64 == t_257);

label_0x918c:
if (bv2bool(ZF)) {
  goto label_0x918f;
}

label_0x918e:
assume false;

label_0x918f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x9197:
origDEST_261 := RAX;
origCOUNT_262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_85);

label_0x919b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x91a2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x91a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x91ae:
origDEST_267 := RCX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_87);

label_0x91b2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_88;
SF := unconstrained_89;
AF := unconstrained_90;
PF := unconstrained_91;

label_0x91b6:
if (bv2bool(CF)) {
  goto label_0x91b9;
}

label_0x91b8:
assume false;

label_0x91b9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x91c1:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x91c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x91cf:
t1_273 := RAX;
t2_274 := 64bv64;
RAX := PLUS_64(RAX, t2_274);
CF := bool2bv(LT_64(RAX, t1_273));
OF := AND_1((bool2bv((t1_273[64:63]) == (t2_274[64:63]))), (XOR_1((t1_273[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_273)), t2_274)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x91d3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 744bv64), RAX);

label_0x91db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x91e3:
t1_279 := RAX;
t2_280 := 12bv64;
RAX := PLUS_64(RAX, t2_280);
CF := bool2bv(LT_64(RAX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x91e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 424bv64), RAX);

label_0x91ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x91f7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x91fd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9202:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_93;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x9205:
if (bv2bool(ZF)) {
  goto label_0x9208;
}

label_0x9207:
assume false;

label_0x9208:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x9210:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_95);

label_0x9214:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x921b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x921f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x9227:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_97);

label_0x922b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_98;
SF := unconstrained_99;
AF := unconstrained_100;
PF := unconstrained_101;

label_0x922f:
if (bv2bool(CF)) {
  goto label_0x9232;
}

label_0x9231:
assume false;

label_0x9232:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x923a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 744bv64));

label_0x9242:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x9245:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x9247:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x924f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x9252:
origDEST_303 := RAX;
origCOUNT_304 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), CF, RSHIFT_64(origDEST_303, (MINUS_64(64bv64, origCOUNT_304)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_304 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_102));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), AF, unconstrained_103);

label_0x9256:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x925e:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3152bv64));

label_0x9265:
t1_309 := RCX;
t2_310 := RAX;
RCX := PLUS_64(RCX, t2_310);
CF := bool2bv(LT_64(RCX, t1_309));
OF := AND_1((bool2bv((t1_309[64:63]) == (t2_310[64:63]))), (XOR_1((t1_309[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_309)), t2_310)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9268:
mem := STORE_LE_64(mem, PLUS_64(RSP, 752bv64), RCX);

label_0x9270:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9278:
t1_315 := RAX;
t2_316 := 60bv64;
RAX := PLUS_64(RAX, t2_316);
CF := bool2bv(LT_64(RAX, t1_315));
OF := AND_1((bool2bv((t1_315[64:63]) == (t2_316[64:63]))), (XOR_1((t1_315[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_315)), t2_316)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x927c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 432bv64), RAX);

label_0x9284:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x928c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_104;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9292:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9297:
t_323 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)), 2bv64)), (XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)), 2bv64)), (XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)))))[1:0]));
SF := t_323[64:63];
ZF := bool2bv(0bv64 == t_323);

label_0x929a:
if (bv2bool(ZF)) {
  goto label_0x929d;
}

label_0x929c:
assume false;

label_0x929d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x92a5:
origDEST_327 := RAX;
origCOUNT_328 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), CF, LSHIFT_64(origDEST_327, (MINUS_64(64bv64, origCOUNT_328)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_328 == 1bv64)), origDEST_327[64:63], unconstrained_106));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), AF, unconstrained_107);

label_0x92a9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x92b0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x92b4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x92bc:
origDEST_333 := RCX;
origCOUNT_334 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), CF, LSHIFT_64(origDEST_333, (MINUS_64(64bv64, origCOUNT_334)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_334 == 1bv64)), origDEST_333[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), AF, unconstrained_109);

label_0x92c0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_110;
SF := unconstrained_111;
AF := unconstrained_112;
PF := unconstrained_113;

label_0x92c4:
if (bv2bool(CF)) {
  goto label_0x92c7;
}

label_0x92c6:
assume false;

label_0x92c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x92cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 752bv64));

label_0x92d7:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x92d9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x92db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x92e3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x92e6:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_114;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x92eb:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x92ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x92f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x92f9:
origDEST_341 := RAX[32:0];
origCOUNT_342 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), CF, LSHIFT_32(origDEST_341, (MINUS_32(32bv32, origCOUNT_342)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_342 == 1bv32)), origDEST_341[32:31], unconstrained_115));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv32)), AF, unconstrained_116);

label_0x92fc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 600bv64), RAX[32:0]);

label_0x9303:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x930b:
t1_347 := RAX;
t2_348 := 60bv64;
RAX := PLUS_64(RAX, t2_348);
CF := bool2bv(LT_64(RAX, t1_347));
OF := AND_1((bool2bv((t1_347[64:63]) == (t2_348[64:63]))), (XOR_1((t1_347[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_347)), t2_348)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x930f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 440bv64), RAX);

label_0x9317:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x931f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9325:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x932a:
t_355 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)), 2bv64)), (XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)), 2bv64)), (XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)))))[1:0]));
SF := t_355[64:63];
ZF := bool2bv(0bv64 == t_355);

label_0x932d:
if (bv2bool(ZF)) {
  goto label_0x9330;
}

label_0x932f:
assume false;

label_0x9330:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x9338:
origDEST_359 := RAX;
origCOUNT_360 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), CF, LSHIFT_64(origDEST_359, (MINUS_64(64bv64, origCOUNT_360)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_360 == 1bv64)), origDEST_359[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), AF, unconstrained_120);

label_0x933c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9343:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9347:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x934f:
origDEST_365 := RCX;
origCOUNT_366 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), CF, LSHIFT_64(origDEST_365, (MINUS_64(64bv64, origCOUNT_366)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_366 == 1bv64)), origDEST_365[64:63], unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), AF, unconstrained_122);

label_0x9353:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_123;
SF := unconstrained_124;
AF := unconstrained_125;
PF := unconstrained_126;

label_0x9357:
if (bv2bool(CF)) {
  goto label_0x935a;
}

label_0x9359:
assume false;

label_0x935a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x9362:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 600bv64)));

label_0x9369:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x936b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9373:
t_371 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_371)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_371, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)), 2bv32)), (XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)), 2bv32)), (XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)))))[1:0]));
SF := t_371[32:31];
ZF := bool2bv(0bv32 == t_371);

label_0x9377:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x94fc;
}

label_0x937d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9385:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0x9389:
origDEST_375 := RAX;
origCOUNT_376 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), CF, RSHIFT_64(origDEST_375, (MINUS_64(64bv64, origCOUNT_376)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_376 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), AF, unconstrained_128);

label_0x938d:
RCX := PLUS_64((PLUS_64(0bv64, 37780bv64)), 0bv64)[64:0];

label_0x9394:
t1_381 := RCX;
t2_382 := RAX;
RCX := PLUS_64(RCX, t2_382);
CF := bool2bv(LT_64(RCX, t1_381));
OF := AND_1((bool2bv((t1_381[64:63]) == (t2_382[64:63]))), (XOR_1((t1_381[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_381)), t2_382)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9397:
mem := STORE_LE_64(mem, PLUS_64(RSP, 760bv64), RCX);

label_0x939f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x93a7:
t1_387 := RAX;
t2_388 := 24bv64;
RAX := PLUS_64(RAX, t2_388);
CF := bool2bv(LT_64(RAX, t1_387));
OF := AND_1((bool2bv((t1_387[64:63]) == (t2_388[64:63]))), (XOR_1((t1_387[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_387)), t2_388)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x93ab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 448bv64), RAX);

label_0x93b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0x93bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_129;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x93c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x93c6:
t_395 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_130;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)), 2bv64)), (XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)), 2bv64)), (XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)))))[1:0]));
SF := t_395[64:63];
ZF := bool2bv(0bv64 == t_395);

label_0x93c9:
if (bv2bool(ZF)) {
  goto label_0x93cc;
}

label_0x93cb:
assume false;

label_0x93cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0x93d4:
origDEST_399 := RAX;
origCOUNT_400 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), CF, LSHIFT_64(origDEST_399, (MINUS_64(64bv64, origCOUNT_400)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_400 == 1bv64)), origDEST_399[64:63], unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), AF, unconstrained_132);

label_0x93d8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x93df:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x93e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0x93eb:
origDEST_405 := RCX;
origCOUNT_406 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), CF, LSHIFT_64(origDEST_405, (MINUS_64(64bv64, origCOUNT_406)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_406 == 1bv64)), origDEST_405[64:63], unconstrained_133));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), AF, unconstrained_134);

label_0x93ef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_135;
SF := unconstrained_136;
AF := unconstrained_137;
PF := unconstrained_138;

label_0x93f3:
if (bv2bool(CF)) {
  goto label_0x93f6;
}

label_0x93f5:
assume false;

label_0x93f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0x93fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 760bv64));

label_0x9406:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x9408:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x940a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9412:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0x9415:
t_411 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_411[32:31]) == (1bv32[32:31]))), (XOR_1((t_411[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_411)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9417:
mem := STORE_LE_32(mem, PLUS_64(RSP, 604bv64), RAX[32:0]);

label_0x941e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9426:
t1_415 := RAX;
t2_416 := 28bv64;
RAX := PLUS_64(RAX, t2_416);
CF := bool2bv(LT_64(RAX, t1_415));
OF := AND_1((bool2bv((t1_415[64:63]) == (t2_416[64:63]))), (XOR_1((t1_415[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_415)), t2_416)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x942a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RAX);

label_0x9432:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x943a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_139;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9440:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9445:
t_423 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_140;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)), 2bv64)), (XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)), 2bv64)), (XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)))))[1:0]));
SF := t_423[64:63];
ZF := bool2bv(0bv64 == t_423);

label_0x9448:
if (bv2bool(ZF)) {
  goto label_0x944b;
}

label_0x944a:
assume false;

label_0x944b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x9453:
origDEST_427 := RAX;
origCOUNT_428 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), CF, LSHIFT_64(origDEST_427, (MINUS_64(64bv64, origCOUNT_428)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_428 == 1bv64)), origDEST_427[64:63], unconstrained_141));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), AF, unconstrained_142);

label_0x9457:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x945e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9462:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x946a:
origDEST_433 := RCX;
origCOUNT_434 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), CF, LSHIFT_64(origDEST_433, (MINUS_64(64bv64, origCOUNT_434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_434 == 1bv64)), origDEST_433[64:63], unconstrained_143));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), AF, unconstrained_144);

label_0x946e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_145;
SF := unconstrained_146;
AF := unconstrained_147;
PF := unconstrained_148;

label_0x9472:
if (bv2bool(CF)) {
  goto label_0x9475;
}

label_0x9474:
assume false;

label_0x9475:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x947d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 604bv64)));

label_0x9484:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9486:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x948e:
t_439 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_439)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_439, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)), 2bv32)), (XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)), 2bv32)), (XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)))))[1:0]));
SF := t_439[32:31];
ZF := bool2bv(0bv32 == t_439);

label_0x9495:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x94fc;
}

label_0x9497:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x949f:
t1_443 := RAX;
t2_444 := 28bv64;
RAX := PLUS_64(RAX, t2_444);
CF := bool2bv(LT_64(RAX, t1_443));
OF := AND_1((bool2bv((t1_443[64:63]) == (t2_444[64:63]))), (XOR_1((t1_443[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_443)), t2_444)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x94a3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 464bv64), RAX);

label_0x94ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0x94b3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_149;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x94b9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x94be:
t_451 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_150;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)), 2bv64)), (XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)), 2bv64)), (XOR_64((RSHIFT_64(t_451, 4bv64)), t_451)))))[1:0]));
SF := t_451[64:63];
ZF := bool2bv(0bv64 == t_451);

label_0x94c1:
if (bv2bool(ZF)) {
  goto label_0x94c4;
}

label_0x94c3:
assume false;

label_0x94c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0x94cc:
origDEST_455 := RAX;
origCOUNT_456 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), CF, LSHIFT_64(origDEST_455, (MINUS_64(64bv64, origCOUNT_456)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_456 == 1bv64)), origDEST_455[64:63], unconstrained_151));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_456 == 0bv64)), AF, unconstrained_152);

label_0x94d0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x94d7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x94db:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0x94e3:
origDEST_461 := RCX;
origCOUNT_462 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), CF, LSHIFT_64(origDEST_461, (MINUS_64(64bv64, origCOUNT_462)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_462 == 1bv64)), origDEST_461[64:63], unconstrained_153));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_462 == 0bv64)), AF, unconstrained_154);

label_0x94e7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_155;
SF := unconstrained_156;
AF := unconstrained_157;
PF := unconstrained_158;

label_0x94eb:
if (bv2bool(CF)) {
  goto label_0x94ee;
}

label_0x94ed:
assume false;

label_0x94ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0x94f6:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x94fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9504:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0x9507:
t_467 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_467, 1bv32)), (XOR_32(t_467, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_467)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9509:
mem := STORE_LE_32(mem, PLUS_64(RSP, 608bv64), RAX[32:0]);

label_0x9510:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9518:
t1_471 := RAX;
t2_472 := 24bv64;
RAX := PLUS_64(RAX, t2_472);
CF := bool2bv(LT_64(RAX, t1_471));
OF := AND_1((bool2bv((t1_471[64:63]) == (t2_472[64:63]))), (XOR_1((t1_471[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_471)), t2_472)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x951c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 472bv64), RAX);

label_0x9524:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0x952c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_159;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9532:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9537:
t_479 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_160;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)), 2bv64)), (XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)), 2bv64)), (XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)))))[1:0]));
SF := t_479[64:63];
ZF := bool2bv(0bv64 == t_479);

label_0x953a:
if (bv2bool(ZF)) {
  goto label_0x953d;
}

label_0x953c:
assume false;

label_0x953d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0x9545:
origDEST_483 := RAX;
origCOUNT_484 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), CF, LSHIFT_64(origDEST_483, (MINUS_64(64bv64, origCOUNT_484)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_484 == 1bv64)), origDEST_483[64:63], unconstrained_161));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), AF, unconstrained_162);

label_0x9549:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9550:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9554:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0x955c:
origDEST_489 := RCX;
origCOUNT_490 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), CF, LSHIFT_64(origDEST_489, (MINUS_64(64bv64, origCOUNT_490)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_490 == 1bv64)), origDEST_489[64:63], unconstrained_163));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), AF, unconstrained_164);

label_0x9560:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_165;
SF := unconstrained_166;
AF := unconstrained_167;
PF := unconstrained_168;

label_0x9564:
if (bv2bool(CF)) {
  goto label_0x9567;
}

label_0x9566:
assume false;

label_0x9567:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0x956f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 608bv64)));

label_0x9576:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9578:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9580:
t_495 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_495)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_495, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_495, 4bv32)), t_495)), 2bv32)), (XOR_32((RSHIFT_32(t_495, 4bv32)), t_495)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_495, 4bv32)), t_495)), 2bv32)), (XOR_32((RSHIFT_32(t_495, 4bv32)), t_495)))))[1:0]));
SF := t_495[32:31];
ZF := bool2bv(0bv32 == t_495);

label_0x9584:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9590;
}

label_0x9586:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 1bv32);

label_0x958e:
goto label_0x9598;

label_0x9590:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 0bv32);

label_0x9598:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x959c:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_169;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x95a0:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x95a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x95ab:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0x95b1:
t_501 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_501[32:31]) == (1bv32[32:31]))), (XOR_1((t_501[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_501)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x95b3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 612bv64), RAX[32:0]);

label_0x95ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x95c2:
t1_505 := RAX;
t2_506 := 1092bv64;
RAX := PLUS_64(RAX, t2_506);
CF := bool2bv(LT_64(RAX, t1_505));
OF := AND_1((bool2bv((t1_505[64:63]) == (t2_506[64:63]))), (XOR_1((t1_505[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_505)), t2_506)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x95c8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 480bv64), RAX);

label_0x95d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0x95d8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_170;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x95de:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x95e3:
t_513 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_171;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))))[1:0]));
SF := t_513[64:63];
ZF := bool2bv(0bv64 == t_513);

label_0x95e6:
if (bv2bool(ZF)) {
  goto label_0x95e9;
}

label_0x95e8:
assume false;

label_0x95e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0x95f1:
origDEST_517 := RAX;
origCOUNT_518 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), CF, LSHIFT_64(origDEST_517, (MINUS_64(64bv64, origCOUNT_518)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_518 == 1bv64)), origDEST_517[64:63], unconstrained_172));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), AF, unconstrained_173);

label_0x95f5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x95fc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9600:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0x9608:
origDEST_523 := RCX;
origCOUNT_524 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), CF, LSHIFT_64(origDEST_523, (MINUS_64(64bv64, origCOUNT_524)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_524 == 1bv64)), origDEST_523[64:63], unconstrained_174));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), AF, unconstrained_175);

label_0x960c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_176;
SF := unconstrained_177;
AF := unconstrained_178;
PF := unconstrained_179;

label_0x9610:
if (bv2bool(CF)) {
  goto label_0x9613;
}

label_0x9612:
assume false;

label_0x9613:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0x961b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 612bv64)));

label_0x9622:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9624:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x962c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x9632:
t_529 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_529[32:31]) == (1bv32[32:31]))), (XOR_1((t_529[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_529)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9634:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x963c:
t_533 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_533)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_533, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_533, 4bv32)), t_533)), 2bv32)), (XOR_32((RSHIFT_32(t_533, 4bv32)), t_533)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_533, 4bv32)), t_533)), 2bv32)), (XOR_32((RSHIFT_32(t_533, 4bv32)), t_533)))))[1:0]));
SF := t_533[32:31];
ZF := bool2bv(0bv32 == t_533);

label_0x9642:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9649;
}

label_0x9644:
goto label_0x8d00;

label_0x9649:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x964d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9655:
t_537 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_537)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_537, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))))[1:0]));
SF := t_537[32:31];
ZF := bool2bv(0bv32 == t_537);

label_0x9658:
if (bv2bool(ZF)) {
  goto label_0x96d2;
}

label_0x965a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9662:
t1_541 := RAX;
t2_542 := 64bv64;
RAX := PLUS_64(RAX, t2_542);
CF := bool2bv(LT_64(RAX, t1_541));
OF := AND_1((bool2bv((t1_541[64:63]) == (t2_542[64:63]))), (XOR_1((t1_541[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_541)), t2_542)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9666:
mem := STORE_LE_64(mem, PLUS_64(RSP, 488bv64), RAX);

label_0x966e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9672:
mem := STORE_LE_32(mem, PLUS_64(RSP, 616bv64), RAX[32:0]);

label_0x9679:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0x9681:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_180;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9687:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x968c:
t_549 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_181;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)), 2bv64)), (XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)), 2bv64)), (XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)))))[1:0]));
SF := t_549[64:63];
ZF := bool2bv(0bv64 == t_549);

label_0x968f:
if (bv2bool(ZF)) {
  goto label_0x9692;
}

label_0x9691:
assume false;

label_0x9692:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0x969a:
origDEST_553 := RAX;
origCOUNT_554 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), CF, LSHIFT_64(origDEST_553, (MINUS_64(64bv64, origCOUNT_554)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_554 == 1bv64)), origDEST_553[64:63], unconstrained_182));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), AF, unconstrained_183);

label_0x969e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x96a5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x96a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0x96b1:
origDEST_559 := RCX;
origCOUNT_560 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), CF, LSHIFT_64(origDEST_559, (MINUS_64(64bv64, origCOUNT_560)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_560 == 1bv64)), origDEST_559[64:63], unconstrained_184));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), AF, unconstrained_185);

label_0x96b5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_186;
SF := unconstrained_187;
AF := unconstrained_188;
PF := unconstrained_189;

label_0x96b9:
if (bv2bool(CF)) {
  goto label_0x96bc;
}

label_0x96bb:
assume false;

label_0x96bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0x96c4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 616bv64)));

label_0x96cb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x96cd:
goto label_0x8d00;

label_0x96d2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x96da:
t1_565 := RAX;
t2_566 := 16bv64;
RAX := PLUS_64(RAX, t2_566);
CF := bool2bv(LT_64(RAX, t1_565));
OF := AND_1((bool2bv((t1_565[64:63]) == (t2_566[64:63]))), (XOR_1((t1_565[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_565)), t2_566)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x96de:
mem := STORE_LE_64(mem, PLUS_64(RSP, 496bv64), RAX);

label_0x96e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x96ee:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_190;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x96f4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x96f9:
t_573 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_191;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_573, 4bv64)), t_573)), 2bv64)), (XOR_64((RSHIFT_64(t_573, 4bv64)), t_573)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_573, 4bv64)), t_573)), 2bv64)), (XOR_64((RSHIFT_64(t_573, 4bv64)), t_573)))))[1:0]));
SF := t_573[64:63];
ZF := bool2bv(0bv64 == t_573);

label_0x96fc:
if (bv2bool(ZF)) {
  goto label_0x96ff;
}

label_0x96fe:
assume false;

label_0x96ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x9707:
origDEST_577 := RAX;
origCOUNT_578 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), CF, LSHIFT_64(origDEST_577, (MINUS_64(64bv64, origCOUNT_578)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_578 == 1bv64)), origDEST_577[64:63], unconstrained_192));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), AF, unconstrained_193);

label_0x970b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9712:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9716:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x971e:
origDEST_583 := RCX;
origCOUNT_584 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), CF, LSHIFT_64(origDEST_583, (MINUS_64(64bv64, origCOUNT_584)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_584 == 1bv64)), origDEST_583[64:63], unconstrained_194));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), AF, unconstrained_195);

label_0x9722:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_196;
SF := unconstrained_197;
AF := unconstrained_198;
PF := unconstrained_199;

label_0x9726:
if (bv2bool(CF)) {
  goto label_0x9729;
}

label_0x9728:
assume false;

label_0x9729:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x9731:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0x9737:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x973f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x9742:
origDEST_589 := RAX;
origCOUNT_590 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, RSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_200));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_201);

label_0x9746:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x974e:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3152bv64));

label_0x9755:
t1_595 := RCX;
t2_596 := RAX;
RCX := PLUS_64(RCX, t2_596);
CF := bool2bv(LT_64(RCX, t1_595));
OF := AND_1((bool2bv((t1_595[64:63]) == (t2_596[64:63]))), (XOR_1((t1_595[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_595)), t2_596)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9758:
mem := STORE_LE_64(mem, PLUS_64(RSP, 768bv64), RCX);

label_0x9760:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9768:
t1_601 := RAX;
t2_602 := 60bv64;
RAX := PLUS_64(RAX, t2_602);
CF := bool2bv(LT_64(RAX, t1_601));
OF := AND_1((bool2bv((t1_601[64:63]) == (t2_602[64:63]))), (XOR_1((t1_601[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_601)), t2_602)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x976c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 504bv64), RAX);

label_0x9774:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0x977c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_202;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9782:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9787:
t_609 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_203;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)), 2bv64)), (XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)), 2bv64)), (XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)))))[1:0]));
SF := t_609[64:63];
ZF := bool2bv(0bv64 == t_609);

label_0x978a:
if (bv2bool(ZF)) {
  goto label_0x978d;
}

label_0x978c:
assume false;

label_0x978d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0x9795:
origDEST_613 := RAX;
origCOUNT_614 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), CF, LSHIFT_64(origDEST_613, (MINUS_64(64bv64, origCOUNT_614)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_614 == 1bv64)), origDEST_613[64:63], unconstrained_204));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), AF, unconstrained_205);

label_0x9799:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x97a0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x97a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0x97ac:
origDEST_619 := RCX;
origCOUNT_620 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), CF, LSHIFT_64(origDEST_619, (MINUS_64(64bv64, origCOUNT_620)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_620 == 1bv64)), origDEST_619[64:63], unconstrained_206));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), AF, unconstrained_207);

label_0x97b0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_208;
SF := unconstrained_209;
AF := unconstrained_210;
PF := unconstrained_211;

label_0x97b4:
if (bv2bool(CF)) {
  goto label_0x97b7;
}

label_0x97b6:
assume false;

label_0x97b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0x97bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 768bv64));

label_0x97c7:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x97c9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x97cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x97d3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x97d6:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_212;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x97db:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x97de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x97e6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x97e9:
origDEST_627 := RAX[32:0];
origCOUNT_628 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), CF, LSHIFT_32(origDEST_627, (MINUS_32(32bv32, origCOUNT_628)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_628 == 1bv32)), origDEST_627[32:31], unconstrained_213));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv32)), AF, unconstrained_214);

label_0x97ec:
mem := STORE_LE_32(mem, PLUS_64(RSP, 620bv64), RAX[32:0]);

label_0x97f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x97fb:
t1_633 := RAX;
t2_634 := 60bv64;
RAX := PLUS_64(RAX, t2_634);
CF := bool2bv(LT_64(RAX, t1_633));
OF := AND_1((bool2bv((t1_633[64:63]) == (t2_634[64:63]))), (XOR_1((t1_633[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_633)), t2_634)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x97ff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 512bv64), RAX);

label_0x9807:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0x980f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_215;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9815:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x981a:
t_641 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_216;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)), 2bv64)), (XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)), 2bv64)), (XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)))))[1:0]));
SF := t_641[64:63];
ZF := bool2bv(0bv64 == t_641);

label_0x981d:
if (bv2bool(ZF)) {
  goto label_0x9820;
}

label_0x981f:
assume false;

label_0x9820:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0x9828:
origDEST_645 := RAX;
origCOUNT_646 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), CF, LSHIFT_64(origDEST_645, (MINUS_64(64bv64, origCOUNT_646)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_646 == 1bv64)), origDEST_645[64:63], unconstrained_217));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), AF, unconstrained_218);

label_0x982c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9833:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9837:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0x983f:
origDEST_651 := RCX;
origCOUNT_652 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), CF, LSHIFT_64(origDEST_651, (MINUS_64(64bv64, origCOUNT_652)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_652 == 1bv64)), origDEST_651[64:63], unconstrained_219));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), AF, unconstrained_220);

label_0x9843:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_221;
SF := unconstrained_222;
AF := unconstrained_223;
PF := unconstrained_224;

label_0x9847:
if (bv2bool(CF)) {
  goto label_0x984a;
}

label_0x9849:
assume false;

label_0x984a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0x9852:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 620bv64)));

label_0x9859:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x985b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9863:
t_657 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_657)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_657, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_657, 4bv32)), t_657)), 2bv32)), (XOR_32((RSHIFT_32(t_657, 4bv32)), t_657)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_657, 4bv32)), t_657)), 2bv32)), (XOR_32((RSHIFT_32(t_657, 4bv32)), t_657)))))[1:0]));
SF := t_657[32:31];
ZF := bool2bv(0bv32 == t_657);

label_0x9867:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x99ec;
}

label_0x986d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9875:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0x9879:
origDEST_661 := RAX;
origCOUNT_662 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), CF, RSHIFT_64(origDEST_661, (MINUS_64(64bv64, origCOUNT_662)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_662 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_225));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), AF, unconstrained_226);

label_0x987d:
RCX := PLUS_64((PLUS_64(0bv64, 39044bv64)), 0bv64)[64:0];

label_0x9884:
t1_667 := RCX;
t2_668 := RAX;
RCX := PLUS_64(RCX, t2_668);
CF := bool2bv(LT_64(RCX, t1_667));
OF := AND_1((bool2bv((t1_667[64:63]) == (t2_668[64:63]))), (XOR_1((t1_667[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_667)), t2_668)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9887:
mem := STORE_LE_64(mem, PLUS_64(RSP, 776bv64), RCX);

label_0x988f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9897:
t1_673 := RAX;
t2_674 := 24bv64;
RAX := PLUS_64(RAX, t2_674);
CF := bool2bv(LT_64(RAX, t1_673));
OF := AND_1((bool2bv((t1_673[64:63]) == (t2_674[64:63]))), (XOR_1((t1_673[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_673)), t2_674)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x989b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 520bv64), RAX);

label_0x98a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x98ab:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_227;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x98b1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x98b6:
t_681 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_228;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)), 2bv64)), (XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)), 2bv64)), (XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)))))[1:0]));
SF := t_681[64:63];
ZF := bool2bv(0bv64 == t_681);

label_0x98b9:
if (bv2bool(ZF)) {
  goto label_0x98bc;
}

label_0x98bb:
assume false;

label_0x98bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x98c4:
origDEST_685 := RAX;
origCOUNT_686 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), CF, LSHIFT_64(origDEST_685, (MINUS_64(64bv64, origCOUNT_686)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_686 == 1bv64)), origDEST_685[64:63], unconstrained_229));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), AF, unconstrained_230);

label_0x98c8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x98cf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x98d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x98db:
origDEST_691 := RCX;
origCOUNT_692 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), CF, LSHIFT_64(origDEST_691, (MINUS_64(64bv64, origCOUNT_692)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_692 == 1bv64)), origDEST_691[64:63], unconstrained_231));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), AF, unconstrained_232);

label_0x98df:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_233;
SF := unconstrained_234;
AF := unconstrained_235;
PF := unconstrained_236;

label_0x98e3:
if (bv2bool(CF)) {
  goto label_0x98e6;
}

label_0x98e5:
assume false;

label_0x98e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x98ee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 776bv64));

label_0x98f6:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x98f8:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x98fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9902:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0x9905:
t_697 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_697[32:31]) == (1bv32[32:31]))), (XOR_1((t_697[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_697)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9907:
mem := STORE_LE_32(mem, PLUS_64(RSP, 624bv64), RAX[32:0]);

label_0x990e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9916:
t1_701 := RAX;
t2_702 := 28bv64;
RAX := PLUS_64(RAX, t2_702);
CF := bool2bv(LT_64(RAX, t1_701));
OF := AND_1((bool2bv((t1_701[64:63]) == (t2_702[64:63]))), (XOR_1((t1_701[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_701)), t2_702)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x991a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 528bv64), RAX);

label_0x9922:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0x992a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_237;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9930:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9935:
t_709 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_238;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)), 2bv64)), (XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)), 2bv64)), (XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)))))[1:0]));
SF := t_709[64:63];
ZF := bool2bv(0bv64 == t_709);

label_0x9938:
if (bv2bool(ZF)) {
  goto label_0x993b;
}

label_0x993a:
assume false;

label_0x993b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0x9943:
origDEST_713 := RAX;
origCOUNT_714 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), CF, LSHIFT_64(origDEST_713, (MINUS_64(64bv64, origCOUNT_714)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_714 == 1bv64)), origDEST_713[64:63], unconstrained_239));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), AF, unconstrained_240);

label_0x9947:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x994e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9952:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0x995a:
origDEST_719 := RCX;
origCOUNT_720 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), CF, LSHIFT_64(origDEST_719, (MINUS_64(64bv64, origCOUNT_720)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_720 == 1bv64)), origDEST_719[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), AF, unconstrained_242);

label_0x995e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_243;
SF := unconstrained_244;
AF := unconstrained_245;
PF := unconstrained_246;

label_0x9962:
if (bv2bool(CF)) {
  goto label_0x9965;
}

label_0x9964:
assume false;

label_0x9965:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0x996d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 624bv64)));

label_0x9974:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9976:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x997e:
t_725 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_725)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_725, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_725, 4bv32)), t_725)), 2bv32)), (XOR_32((RSHIFT_32(t_725, 4bv32)), t_725)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_725, 4bv32)), t_725)), 2bv32)), (XOR_32((RSHIFT_32(t_725, 4bv32)), t_725)))))[1:0]));
SF := t_725[32:31];
ZF := bool2bv(0bv32 == t_725);

label_0x9985:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x99ec;
}

label_0x9987:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x998f:
t1_729 := RAX;
t2_730 := 28bv64;
RAX := PLUS_64(RAX, t2_730);
CF := bool2bv(LT_64(RAX, t1_729));
OF := AND_1((bool2bv((t1_729[64:63]) == (t2_730[64:63]))), (XOR_1((t1_729[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_729)), t2_730)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9993:
mem := STORE_LE_64(mem, PLUS_64(RSP, 536bv64), RAX);

label_0x999b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0x99a3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_247;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x99a9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x99ae:
t_737 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_248;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_737, 4bv64)), t_737)), 2bv64)), (XOR_64((RSHIFT_64(t_737, 4bv64)), t_737)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_737, 4bv64)), t_737)), 2bv64)), (XOR_64((RSHIFT_64(t_737, 4bv64)), t_737)))))[1:0]));
SF := t_737[64:63];
ZF := bool2bv(0bv64 == t_737);

label_0x99b1:
if (bv2bool(ZF)) {
  goto label_0x99b4;
}

label_0x99b3:
assume false;

label_0x99b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0x99bc:
origDEST_741 := RAX;
origCOUNT_742 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), CF, LSHIFT_64(origDEST_741, (MINUS_64(64bv64, origCOUNT_742)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_742 == 1bv64)), origDEST_741[64:63], unconstrained_249));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_742 == 0bv64)), AF, unconstrained_250);

label_0x99c0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x99c7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x99cb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0x99d3:
origDEST_747 := RCX;
origCOUNT_748 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), CF, LSHIFT_64(origDEST_747, (MINUS_64(64bv64, origCOUNT_748)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_748 == 1bv64)), origDEST_747[64:63], unconstrained_251));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_748 == 0bv64)), AF, unconstrained_252);

label_0x99d7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_253;
SF := unconstrained_254;
AF := unconstrained_255;
PF := unconstrained_256;

label_0x99db:
if (bv2bool(CF)) {
  goto label_0x99de;
}

label_0x99dd:
assume false;

label_0x99de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0x99e6:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x99ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x99f4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0x99f7:
t_753 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_753, 1bv32)), (XOR_32(t_753, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_753)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x99f9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 628bv64), RAX[32:0]);

label_0x9a00:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9a08:
t1_757 := RAX;
t2_758 := 24bv64;
RAX := PLUS_64(RAX, t2_758);
CF := bool2bv(LT_64(RAX, t1_757));
OF := AND_1((bool2bv((t1_757[64:63]) == (t2_758[64:63]))), (XOR_1((t1_757[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_757)), t2_758)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9a0c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 544bv64), RAX);

label_0x9a14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0x9a1c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_257;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9a22:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9a27:
t_765 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_258;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)), 2bv64)), (XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)), 2bv64)), (XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)))))[1:0]));
SF := t_765[64:63];
ZF := bool2bv(0bv64 == t_765);

label_0x9a2a:
if (bv2bool(ZF)) {
  goto label_0x9a2d;
}

label_0x9a2c:
assume false;

label_0x9a2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0x9a35:
origDEST_769 := RAX;
origCOUNT_770 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), CF, LSHIFT_64(origDEST_769, (MINUS_64(64bv64, origCOUNT_770)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_770 == 1bv64)), origDEST_769[64:63], unconstrained_259));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), AF, unconstrained_260);

label_0x9a39:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9a40:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9a44:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0x9a4c:
origDEST_775 := RCX;
origCOUNT_776 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), CF, LSHIFT_64(origDEST_775, (MINUS_64(64bv64, origCOUNT_776)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_776 == 1bv64)), origDEST_775[64:63], unconstrained_261));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), AF, unconstrained_262);

label_0x9a50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_263;
SF := unconstrained_264;
AF := unconstrained_265;
PF := unconstrained_266;

label_0x9a54:
if (bv2bool(CF)) {
  goto label_0x9a57;
}

label_0x9a56:
assume false;

label_0x9a57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0x9a5f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 628bv64)));

label_0x9a66:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9a68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9a70:
t_781 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_781)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_781, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)), 2bv32)), (XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)), 2bv32)), (XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)))))[1:0]));
SF := t_781[32:31];
ZF := bool2bv(0bv32 == t_781);

label_0x9a74:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9a80;
}

label_0x9a76:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), 1bv32);

label_0x9a7e:
goto label_0x9a88;

label_0x9a80:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), 0bv32);

label_0x9a88:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9a8c:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_267;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9a90:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x9a93:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9a9b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0x9aa1:
t_787 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_787[32:31]) == (1bv32[32:31]))), (XOR_1((t_787[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_787)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9aa3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 632bv64), RAX[32:0]);

label_0x9aaa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9ab2:
t1_791 := RAX;
t2_792 := 1092bv64;
RAX := PLUS_64(RAX, t2_792);
CF := bool2bv(LT_64(RAX, t1_791));
OF := AND_1((bool2bv((t1_791[64:63]) == (t2_792[64:63]))), (XOR_1((t1_791[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_791)), t2_792)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ab8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 552bv64), RAX);

label_0x9ac0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0x9ac8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_268;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ace:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9ad3:
t_799 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_269;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_799, 4bv64)), t_799)), 2bv64)), (XOR_64((RSHIFT_64(t_799, 4bv64)), t_799)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_799, 4bv64)), t_799)), 2bv64)), (XOR_64((RSHIFT_64(t_799, 4bv64)), t_799)))))[1:0]));
SF := t_799[64:63];
ZF := bool2bv(0bv64 == t_799);

label_0x9ad6:
if (bv2bool(ZF)) {
  goto label_0x9ad9;
}

label_0x9ad8:
assume false;

label_0x9ad9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0x9ae1:
origDEST_803 := RAX;
origCOUNT_804 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), CF, LSHIFT_64(origDEST_803, (MINUS_64(64bv64, origCOUNT_804)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_804 == 1bv64)), origDEST_803[64:63], unconstrained_270));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_804 == 0bv64)), AF, unconstrained_271);

label_0x9ae5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9aec:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9af0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0x9af8:
origDEST_809 := RCX;
origCOUNT_810 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), CF, LSHIFT_64(origDEST_809, (MINUS_64(64bv64, origCOUNT_810)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_810 == 1bv64)), origDEST_809[64:63], unconstrained_272));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), AF, unconstrained_273);

label_0x9afc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_274;
SF := unconstrained_275;
AF := unconstrained_276;
PF := unconstrained_277;

label_0x9b00:
if (bv2bool(CF)) {
  goto label_0x9b03;
}

label_0x9b02:
assume false;

label_0x9b03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0x9b0b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 632bv64)));

label_0x9b12:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9b14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9b1c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x9b22:
t_815 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_815[32:31]) == (1bv32[32:31]))), (XOR_1((t_815[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_815)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9b24:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9b2c:
t_819 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_819)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_819, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_819, 4bv32)), t_819)), 2bv32)), (XOR_32((RSHIFT_32(t_819, 4bv32)), t_819)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_819, 4bv32)), t_819)), 2bv32)), (XOR_32((RSHIFT_32(t_819, 4bv32)), t_819)))))[1:0]));
SF := t_819[32:31];
ZF := bool2bv(0bv32 == t_819);

label_0x9b32:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9b39;
}

label_0x9b34:
goto label_0x8d00;

label_0x9b39:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9b3d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9b45:
t_823 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_823)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_823, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_823, 4bv32)), t_823)), 2bv32)), (XOR_32((RSHIFT_32(t_823, 4bv32)), t_823)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_823, 4bv32)), t_823)), 2bv32)), (XOR_32((RSHIFT_32(t_823, 4bv32)), t_823)))))[1:0]));
SF := t_823[32:31];
ZF := bool2bv(0bv32 == t_823);

label_0x9b48:
if (bv2bool(ZF)) {
  goto label_0x9bc2;
}

label_0x9b4a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9b52:
t1_827 := RAX;
t2_828 := 64bv64;
RAX := PLUS_64(RAX, t2_828);
CF := bool2bv(LT_64(RAX, t1_827));
OF := AND_1((bool2bv((t1_827[64:63]) == (t2_828[64:63]))), (XOR_1((t1_827[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_827)), t2_828)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9b56:
mem := STORE_LE_64(mem, PLUS_64(RSP, 560bv64), RAX);

label_0x9b5e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9b62:
mem := STORE_LE_32(mem, PLUS_64(RSP, 636bv64), RAX[32:0]);

label_0x9b69:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0x9b71:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_278;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9b77:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9b7c:
t_835 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_279;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_835, 4bv64)), t_835)), 2bv64)), (XOR_64((RSHIFT_64(t_835, 4bv64)), t_835)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_835, 4bv64)), t_835)), 2bv64)), (XOR_64((RSHIFT_64(t_835, 4bv64)), t_835)))))[1:0]));
SF := t_835[64:63];
ZF := bool2bv(0bv64 == t_835);

label_0x9b7f:
if (bv2bool(ZF)) {
  goto label_0x9b82;
}

label_0x9b81:
assume false;

label_0x9b82:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0x9b8a:
origDEST_839 := RAX;
origCOUNT_840 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), CF, LSHIFT_64(origDEST_839, (MINUS_64(64bv64, origCOUNT_840)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_840 == 1bv64)), origDEST_839[64:63], unconstrained_280));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_840 == 0bv64)), AF, unconstrained_281);

label_0x9b8e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9b95:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9b99:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0x9ba1:
origDEST_845 := RCX;
origCOUNT_846 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), CF, LSHIFT_64(origDEST_845, (MINUS_64(64bv64, origCOUNT_846)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_846 == 1bv64)), origDEST_845[64:63], unconstrained_282));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), AF, unconstrained_283);

label_0x9ba5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_284;
SF := unconstrained_285;
AF := unconstrained_286;
PF := unconstrained_287;

label_0x9ba9:
if (bv2bool(CF)) {
  goto label_0x9bac;
}

label_0x9bab:
assume false;

label_0x9bac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0x9bb4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 636bv64)));

label_0x9bbb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9bbd:
goto label_0x8d00;

label_0x9bc2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9bca:
t1_851 := RAX;
t2_852 := 16bv64;
RAX := PLUS_64(RAX, t2_852);
CF := bool2bv(LT_64(RAX, t1_851));
OF := AND_1((bool2bv((t1_851[64:63]) == (t2_852[64:63]))), (XOR_1((t1_851[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_851)), t2_852)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9bce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 568bv64), RAX);

label_0x9bd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0x9bde:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_288;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9be4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9be9:
t_859 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_289;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_859, 4bv64)), t_859)), 2bv64)), (XOR_64((RSHIFT_64(t_859, 4bv64)), t_859)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_859, 4bv64)), t_859)), 2bv64)), (XOR_64((RSHIFT_64(t_859, 4bv64)), t_859)))))[1:0]));
SF := t_859[64:63];
ZF := bool2bv(0bv64 == t_859);

label_0x9bec:
if (bv2bool(ZF)) {
  goto label_0x9bef;
}

label_0x9bee:
assume false;

label_0x9bef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0x9bf7:
origDEST_863 := RAX;
origCOUNT_864 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), CF, LSHIFT_64(origDEST_863, (MINUS_64(64bv64, origCOUNT_864)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_864 == 1bv64)), origDEST_863[64:63], unconstrained_290));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_864 == 0bv64)), AF, unconstrained_291);

label_0x9bfb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9c02:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9c06:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0x9c0e:
origDEST_869 := RCX;
origCOUNT_870 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), CF, LSHIFT_64(origDEST_869, (MINUS_64(64bv64, origCOUNT_870)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_870 == 1bv64)), origDEST_869[64:63], unconstrained_292));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_870 == 0bv64)), AF, unconstrained_293);

label_0x9c12:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_294;
SF := unconstrained_295;
AF := unconstrained_296;
PF := unconstrained_297;

label_0x9c16:
if (bv2bool(CF)) {
  goto label_0x9c19;
}

label_0x9c18:
assume false;

label_0x9c19:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0x9c21:
mem := STORE_LE_32(mem, RAX, 3bv32);

label_0x9c27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9c2f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x9c32:
origDEST_875 := RAX;
origCOUNT_876 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), CF, RSHIFT_64(origDEST_875, (MINUS_64(64bv64, origCOUNT_876)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_876 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_298));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), AF, unconstrained_299);

label_0x9c36:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9c3e:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3152bv64));

label_0x9c45:
t1_881 := RCX;
t2_882 := RAX;
RCX := PLUS_64(RCX, t2_882);
CF := bool2bv(LT_64(RCX, t1_881));
OF := AND_1((bool2bv((t1_881[64:63]) == (t2_882[64:63]))), (XOR_1((t1_881[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_881)), t2_882)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9c48:
mem := STORE_LE_64(mem, PLUS_64(RSP, 784bv64), RCX);

label_0x9c50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9c58:
t1_887 := RAX;
t2_888 := 60bv64;
RAX := PLUS_64(RAX, t2_888);
CF := bool2bv(LT_64(RAX, t1_887));
OF := AND_1((bool2bv((t1_887[64:63]) == (t2_888[64:63]))), (XOR_1((t1_887[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_887)), t2_888)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9c5c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x9c61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x9c66:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_300;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9c6c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9c71:
t_895 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_301;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_895, 4bv64)), t_895)), 2bv64)), (XOR_64((RSHIFT_64(t_895, 4bv64)), t_895)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_895, 4bv64)), t_895)), 2bv64)), (XOR_64((RSHIFT_64(t_895, 4bv64)), t_895)))))[1:0]));
SF := t_895[64:63];
ZF := bool2bv(0bv64 == t_895);

label_0x9c74:
if (bv2bool(ZF)) {
  goto label_0x9c77;
}

label_0x9c76:
assume false;

label_0x9c77:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x9c7c:
origDEST_899 := RAX;
origCOUNT_900 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), CF, LSHIFT_64(origDEST_899, (MINUS_64(64bv64, origCOUNT_900)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_900 == 1bv64)), origDEST_899[64:63], unconstrained_302));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), AF, unconstrained_303);

label_0x9c80:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9c87:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9c8b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x9c90:
origDEST_905 := RCX;
origCOUNT_906 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), CF, LSHIFT_64(origDEST_905, (MINUS_64(64bv64, origCOUNT_906)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_906 == 1bv64)), origDEST_905[64:63], unconstrained_304));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_906 == 0bv64)), AF, unconstrained_305);

label_0x9c94:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_306;
SF := unconstrained_307;
AF := unconstrained_308;
PF := unconstrained_309;

label_0x9c98:
if (bv2bool(CF)) {
  goto label_0x9c9b;
}

label_0x9c9a:
assume false;

label_0x9c9b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x9ca0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 784bv64));

label_0x9ca8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x9caa:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9cac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9cb4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x9cb7:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_310;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9cbc:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x9cbf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9cc7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0x9cca:
origDEST_913 := RAX[32:0];
origCOUNT_914 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), CF, LSHIFT_32(origDEST_913, (MINUS_32(32bv32, origCOUNT_914)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_914 == 1bv32)), origDEST_913[32:31], unconstrained_311));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv32)), AF, unconstrained_312);

label_0x9ccd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 640bv64), RAX[32:0]);

label_0x9cd4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9cdc:
t1_919 := RAX;
t2_920 := 60bv64;
RAX := PLUS_64(RAX, t2_920);
CF := bool2bv(LT_64(RAX, t1_919));
OF := AND_1((bool2bv((t1_919[64:63]) == (t2_920[64:63]))), (XOR_1((t1_919[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_919)), t2_920)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ce0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 576bv64), RAX);

label_0x9ce8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0x9cf0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_313;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9cf6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9cfb:
t_927 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_314;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_927, 4bv64)), t_927)), 2bv64)), (XOR_64((RSHIFT_64(t_927, 4bv64)), t_927)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_927, 4bv64)), t_927)), 2bv64)), (XOR_64((RSHIFT_64(t_927, 4bv64)), t_927)))))[1:0]));
SF := t_927[64:63];
ZF := bool2bv(0bv64 == t_927);

label_0x9cfe:
if (bv2bool(ZF)) {
  goto label_0x9d01;
}

label_0x9d00:
assume false;

label_0x9d01:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0x9d09:
origDEST_931 := RAX;
origCOUNT_932 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), CF, LSHIFT_64(origDEST_931, (MINUS_64(64bv64, origCOUNT_932)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_932 == 1bv64)), origDEST_931[64:63], unconstrained_315));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_932 == 0bv64)), AF, unconstrained_316);

label_0x9d0d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9d14:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9d18:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0x9d20:
origDEST_937 := RCX;
origCOUNT_938 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), CF, LSHIFT_64(origDEST_937, (MINUS_64(64bv64, origCOUNT_938)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_938 == 1bv64)), origDEST_937[64:63], unconstrained_317));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_938 == 0bv64)), AF, unconstrained_318);

label_0x9d24:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_319;
SF := unconstrained_320;
AF := unconstrained_321;
PF := unconstrained_322;

label_0x9d28:
if (bv2bool(CF)) {
  goto label_0x9d2b;
}

label_0x9d2a:
assume false;

label_0x9d2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0x9d33:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 640bv64)));

label_0x9d3a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9d3c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9d44:
t_943 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_943)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_943, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_943, 4bv32)), t_943)), 2bv32)), (XOR_32((RSHIFT_32(t_943, 4bv32)), t_943)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_943, 4bv32)), t_943)), 2bv32)), (XOR_32((RSHIFT_32(t_943, 4bv32)), t_943)))))[1:0]));
SF := t_943[32:31];
ZF := bool2bv(0bv32 == t_943);

label_0x9d48:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9ea0;
}

label_0x9d4e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9d56:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0x9d5a:
origDEST_947 := RAX;
origCOUNT_948 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), CF, RSHIFT_64(origDEST_947, (MINUS_64(64bv64, origCOUNT_948)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_948 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_323));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), AF, unconstrained_324);

label_0x9d5e:
RCX := PLUS_64((PLUS_64(0bv64, 40293bv64)), 0bv64)[64:0];

label_0x9d65:
t1_953 := RCX;
t2_954 := RAX;
RCX := PLUS_64(RCX, t2_954);
CF := bool2bv(LT_64(RCX, t1_953));
OF := AND_1((bool2bv((t1_953[64:63]) == (t2_954[64:63]))), (XOR_1((t1_953[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_953)), t2_954)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9d68:
mem := STORE_LE_64(mem, PLUS_64(RSP, 792bv64), RCX);

label_0x9d70:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9d78:
t1_959 := RAX;
t2_960 := 24bv64;
RAX := PLUS_64(RAX, t2_960);
CF := bool2bv(LT_64(RAX, t1_959));
OF := AND_1((bool2bv((t1_959[64:63]) == (t2_960[64:63]))), (XOR_1((t1_959[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_959)), t2_960)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9d7c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x9d81:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x9d86:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_325;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9d8c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9d91:
t_967 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_326;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_967, 4bv64)), t_967)), 2bv64)), (XOR_64((RSHIFT_64(t_967, 4bv64)), t_967)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_967, 4bv64)), t_967)), 2bv64)), (XOR_64((RSHIFT_64(t_967, 4bv64)), t_967)))))[1:0]));
SF := t_967[64:63];
ZF := bool2bv(0bv64 == t_967);

label_0x9d94:
if (bv2bool(ZF)) {
  goto label_0x9d97;
}

label_0x9d96:
assume false;

label_0x9d97:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x9d9c:
origDEST_971 := RAX;
origCOUNT_972 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), CF, LSHIFT_64(origDEST_971, (MINUS_64(64bv64, origCOUNT_972)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_972 == 1bv64)), origDEST_971[64:63], unconstrained_327));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_972 == 0bv64)), AF, unconstrained_328);

label_0x9da0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9da7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9dab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x9db0:
origDEST_977 := RCX;
origCOUNT_978 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), CF, LSHIFT_64(origDEST_977, (MINUS_64(64bv64, origCOUNT_978)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_978 == 1bv64)), origDEST_977[64:63], unconstrained_329));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_978 == 0bv64)), AF, unconstrained_330);

label_0x9db4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_331;
SF := unconstrained_332;
AF := unconstrained_333;
PF := unconstrained_334;

label_0x9db8:
if (bv2bool(CF)) {
  goto label_0x9dbb;
}

label_0x9dba:
assume false;

label_0x9dbb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x9dc0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 792bv64));

label_0x9dc8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x9dca:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9dcc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9dd4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0x9dd7:
t_983 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_983[32:31]) == (1bv32[32:31]))), (XOR_1((t_983[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_983)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9dd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 644bv64), RAX[32:0]);

label_0x9de0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9de8:
t1_987 := RAX;
t2_988 := 28bv64;
RAX := PLUS_64(RAX, t2_988);
CF := bool2bv(LT_64(RAX, t1_987));
OF := AND_1((bool2bv((t1_987[64:63]) == (t2_988[64:63]))), (XOR_1((t1_987[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_987)), t2_988)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9dec:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x9df1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9df6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_335;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9dfc:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9e01:
t_995 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_336;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)), 2bv64)), (XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)), 2bv64)), (XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)))))[1:0]));
SF := t_995[64:63];
ZF := bool2bv(0bv64 == t_995);

label_0x9e04:
if (bv2bool(ZF)) {
  goto label_0x9e07;
}

label_0x9e06:
assume false;

label_0x9e07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9e0c:
origDEST_999 := RAX;
origCOUNT_1000 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), CF, LSHIFT_64(origDEST_999, (MINUS_64(64bv64, origCOUNT_1000)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 1bv64)), origDEST_999[64:63], unconstrained_337));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), AF, unconstrained_338);

label_0x9e10:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9e17:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9e1b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9e20:
origDEST_1005 := RCX;
origCOUNT_1006 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), CF, LSHIFT_64(origDEST_1005, (MINUS_64(64bv64, origCOUNT_1006)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 1bv64)), origDEST_1005[64:63], unconstrained_339));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), AF, unconstrained_340);

label_0x9e24:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_341;
SF := unconstrained_342;
AF := unconstrained_343;
PF := unconstrained_344;

label_0x9e28:
if (bv2bool(CF)) {
  goto label_0x9e2b;
}

label_0x9e2a:
assume false;

label_0x9e2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9e30:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 644bv64)));

label_0x9e37:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9e39:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9e41:
t_1011 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_1011)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1011, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)), 2bv32)), (XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)), 2bv32)), (XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)))))[1:0]));
SF := t_1011[32:31];
ZF := bool2bv(0bv32 == t_1011);

label_0x9e48:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9ea0;
}

label_0x9e4a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9e52:
t1_1015 := RAX;
t2_1016 := 28bv64;
RAX := PLUS_64(RAX, t2_1016);
CF := bool2bv(LT_64(RAX, t1_1015));
OF := AND_1((bool2bv((t1_1015[64:63]) == (t2_1016[64:63]))), (XOR_1((t1_1015[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1015)), t2_1016)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9e56:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x9e5b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x9e60:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_345;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9e66:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9e6b:
t_1023 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_346;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)), 2bv64)), (XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)), 2bv64)), (XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)))))[1:0]));
SF := t_1023[64:63];
ZF := bool2bv(0bv64 == t_1023);

label_0x9e6e:
if (bv2bool(ZF)) {
  goto label_0x9e71;
}

label_0x9e70:
assume false;

label_0x9e71:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x9e76:
origDEST_1027 := RAX;
origCOUNT_1028 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), CF, LSHIFT_64(origDEST_1027, (MINUS_64(64bv64, origCOUNT_1028)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 1bv64)), origDEST_1027[64:63], unconstrained_347));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), AF, unconstrained_348);

label_0x9e7a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9e81:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9e85:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x9e8a:
origDEST_1033 := RCX;
origCOUNT_1034 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), CF, LSHIFT_64(origDEST_1033, (MINUS_64(64bv64, origCOUNT_1034)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 1bv64)), origDEST_1033[64:63], unconstrained_349));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), AF, unconstrained_350);

label_0x9e8e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_351;
SF := unconstrained_352;
AF := unconstrained_353;
PF := unconstrained_354;

label_0x9e92:
if (bv2bool(CF)) {
  goto label_0x9e95;
}

label_0x9e94:
assume false;

label_0x9e95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x9e9a:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x9ea0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9ea8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0x9eab:
t_1039 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1039, 1bv32)), (XOR_32(t_1039, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1039)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9ead:
mem := STORE_LE_32(mem, PLUS_64(RSP, 648bv64), RAX[32:0]);

label_0x9eb4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9ebc:
t1_1043 := RAX;
t2_1044 := 24bv64;
RAX := PLUS_64(RAX, t2_1044);
CF := bool2bv(LT_64(RAX, t1_1043));
OF := AND_1((bool2bv((t1_1043[64:63]) == (t2_1044[64:63]))), (XOR_1((t1_1043[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1043)), t2_1044)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ec0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x9ec5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x9eca:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_355;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ed0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9ed5:
t_1051 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_356;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1051, 4bv64)), t_1051)), 2bv64)), (XOR_64((RSHIFT_64(t_1051, 4bv64)), t_1051)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1051, 4bv64)), t_1051)), 2bv64)), (XOR_64((RSHIFT_64(t_1051, 4bv64)), t_1051)))))[1:0]));
SF := t_1051[64:63];
ZF := bool2bv(0bv64 == t_1051);

label_0x9ed8:
if (bv2bool(ZF)) {
  goto label_0x9edb;
}

label_0x9eda:
assume false;

label_0x9edb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x9ee0:
origDEST_1055 := RAX;
origCOUNT_1056 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), CF, LSHIFT_64(origDEST_1055, (MINUS_64(64bv64, origCOUNT_1056)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 1bv64)), origDEST_1055[64:63], unconstrained_357));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1056 == 0bv64)), AF, unconstrained_358);

label_0x9ee4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9eeb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9eef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x9ef4:
origDEST_1061 := RCX;
origCOUNT_1062 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), CF, LSHIFT_64(origDEST_1061, (MINUS_64(64bv64, origCOUNT_1062)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 1bv64)), origDEST_1061[64:63], unconstrained_359));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1062 == 0bv64)), AF, unconstrained_360);

label_0x9ef8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_361;
SF := unconstrained_362;
AF := unconstrained_363;
PF := unconstrained_364;

label_0x9efc:
if (bv2bool(CF)) {
  goto label_0x9eff;
}

label_0x9efe:
assume false;

label_0x9eff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x9f04:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 648bv64)));

label_0x9f0b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9f0d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9f15:
t_1067 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1067)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1067, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1067, 4bv32)), t_1067)), 2bv32)), (XOR_32((RSHIFT_32(t_1067, 4bv32)), t_1067)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1067, 4bv32)), t_1067)), 2bv32)), (XOR_32((RSHIFT_32(t_1067, 4bv32)), t_1067)))))[1:0]));
SF := t_1067[32:31];
ZF := bool2bv(0bv32 == t_1067);

label_0x9f19:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9f25;
}

label_0x9f1b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), 1bv32);

label_0x9f23:
goto label_0x9f2d;

label_0x9f25:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), 0bv32);

label_0x9f2d:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9f31:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_365;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9f35:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x9f38:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9f40:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0x9f46:
t_1073 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1073[32:31]) == (1bv32[32:31]))), (XOR_1((t_1073[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1073)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9f48:
mem := STORE_LE_32(mem, PLUS_64(RSP, 652bv64), RAX[32:0]);

label_0x9f4f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9f57:
t1_1077 := RAX;
t2_1078 := 1092bv64;
RAX := PLUS_64(RAX, t2_1078);
CF := bool2bv(LT_64(RAX, t1_1077));
OF := AND_1((bool2bv((t1_1077[64:63]) == (t2_1078[64:63]))), (XOR_1((t1_1077[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1077)), t2_1078)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9f5d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x9f62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x9f67:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_366;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9f6d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9f72:
t_1085 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_367;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)), 2bv64)), (XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)), 2bv64)), (XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)))))[1:0]));
SF := t_1085[64:63];
ZF := bool2bv(0bv64 == t_1085);

label_0x9f75:
if (bv2bool(ZF)) {
  goto label_0x9f78;
}

label_0x9f77:
assume false;

label_0x9f78:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x9f7d:
origDEST_1089 := RAX;
origCOUNT_1090 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), CF, LSHIFT_64(origDEST_1089, (MINUS_64(64bv64, origCOUNT_1090)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 1bv64)), origDEST_1089[64:63], unconstrained_368));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), AF, unconstrained_369);

label_0x9f81:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9f88:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9f8c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x9f91:
origDEST_1095 := RCX;
origCOUNT_1096 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), CF, LSHIFT_64(origDEST_1095, (MINUS_64(64bv64, origCOUNT_1096)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 1bv64)), origDEST_1095[64:63], unconstrained_370));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), AF, unconstrained_371);

label_0x9f95:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_372;
SF := unconstrained_373;
AF := unconstrained_374;
PF := unconstrained_375;

label_0x9f99:
if (bv2bool(CF)) {
  goto label_0x9f9c;
}

label_0x9f9b:
assume false;

label_0x9f9c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x9fa1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 652bv64)));

label_0x9fa8:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9faa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9fb2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x9fb8:
t_1101 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1101[32:31]) == (1bv32[32:31]))), (XOR_1((t_1101[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1101)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9fba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9fc2:
t_1105 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_1105)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1105, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1105, 4bv32)), t_1105)), 2bv32)), (XOR_32((RSHIFT_32(t_1105, 4bv32)), t_1105)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1105, 4bv32)), t_1105)), 2bv32)), (XOR_32((RSHIFT_32(t_1105, 4bv32)), t_1105)))))[1:0]));
SF := t_1105[32:31];
ZF := bool2bv(0bv32 == t_1105);

label_0x9fc8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x9fcf;
}

label_0x9fca:
goto label_0x8d00;

label_0x9fcf:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9fd3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9fdb:
t_1109 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_1109)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1109, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1109, 4bv32)), t_1109)), 2bv32)), (XOR_32((RSHIFT_32(t_1109, 4bv32)), t_1109)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1109, 4bv32)), t_1109)), 2bv32)), (XOR_32((RSHIFT_32(t_1109, 4bv32)), t_1109)))))[1:0]));
SF := t_1109[32:31];
ZF := bool2bv(0bv32 == t_1109);

label_0x9fde:
if (bv2bool(ZF)) {
  goto label_0xa058;
}

label_0x9fe0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0x9fe8:
t1_1113 := RAX;
t2_1114 := 64bv64;
RAX := PLUS_64(RAX, t2_1114);
CF := bool2bv(LT_64(RAX, t1_1113));
OF := AND_1((bool2bv((t1_1113[64:63]) == (t2_1114[64:63]))), (XOR_1((t1_1113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1113)), t2_1114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9fec:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x9ff4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x9ff8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 656bv64), RAX[32:0]);

label_0x9fff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa007:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_376;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa00d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa012:
t_1121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_377;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1121, 4bv64)), t_1121)), 2bv64)), (XOR_64((RSHIFT_64(t_1121, 4bv64)), t_1121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1121, 4bv64)), t_1121)), 2bv64)), (XOR_64((RSHIFT_64(t_1121, 4bv64)), t_1121)))))[1:0]));
SF := t_1121[64:63];
ZF := bool2bv(0bv64 == t_1121);

label_0xa015:
if (bv2bool(ZF)) {
  goto label_0xa018;
}

label_0xa017:
assume false;

label_0xa018:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa020:
origDEST_1125 := RAX;
origCOUNT_1126 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), CF, LSHIFT_64(origDEST_1125, (MINUS_64(64bv64, origCOUNT_1126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 1bv64)), origDEST_1125[64:63], unconstrained_378));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv64)), AF, unconstrained_379);

label_0xa024:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa02b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa02f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa037:
origDEST_1131 := RCX;
origCOUNT_1132 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), CF, LSHIFT_64(origDEST_1131, (MINUS_64(64bv64, origCOUNT_1132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 1bv64)), origDEST_1131[64:63], unconstrained_380));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1132 == 0bv64)), AF, unconstrained_381);

label_0xa03b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_382;
SF := unconstrained_383;
AF := unconstrained_384;
PF := unconstrained_385;

label_0xa03f:
if (bv2bool(CF)) {
  goto label_0xa042;
}

label_0xa041:
assume false;

label_0xa042:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa04a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 656bv64)));

label_0xa051:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa053:
goto label_0x8d00;

label_0xa058:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa060:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa063:
origDEST_1137 := RAX;
origCOUNT_1138 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), CF, RSHIFT_64(origDEST_1137, (MINUS_64(64bv64, origCOUNT_1138)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_386));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), AF, unconstrained_387);

label_0xa067:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa06f:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3152bv64));

label_0xa076:
t1_1143 := RCX;
t2_1144 := RAX;
RCX := PLUS_64(RCX, t2_1144);
CF := bool2bv(LT_64(RCX, t1_1143));
OF := AND_1((bool2bv((t1_1143[64:63]) == (t2_1144[64:63]))), (XOR_1((t1_1143[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1143)), t2_1144)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa079:
mem := STORE_LE_64(mem, PLUS_64(RSP, 800bv64), RCX);

label_0xa081:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa089:
t1_1149 := RAX;
t2_1150 := 60bv64;
RAX := PLUS_64(RAX, t2_1150);
CF := bool2bv(LT_64(RAX, t1_1149));
OF := AND_1((bool2bv((t1_1149[64:63]) == (t2_1150[64:63]))), (XOR_1((t1_1149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1149)), t2_1150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa08d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0xa095:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa09d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_388;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa0a3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa0a8:
t_1157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_389;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)), 2bv64)), (XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)), 2bv64)), (XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)))))[1:0]));
SF := t_1157[64:63];
ZF := bool2bv(0bv64 == t_1157);

label_0xa0ab:
if (bv2bool(ZF)) {
  goto label_0xa0ae;
}

label_0xa0ad:
assume false;

label_0xa0ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa0b6:
origDEST_1161 := RAX;
origCOUNT_1162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), CF, LSHIFT_64(origDEST_1161, (MINUS_64(64bv64, origCOUNT_1162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 1bv64)), origDEST_1161[64:63], unconstrained_390));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), AF, unconstrained_391);

label_0xa0ba:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa0c1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa0c5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa0cd:
origDEST_1167 := RCX;
origCOUNT_1168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), CF, LSHIFT_64(origDEST_1167, (MINUS_64(64bv64, origCOUNT_1168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 1bv64)), origDEST_1167[64:63], unconstrained_392));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), AF, unconstrained_393);

label_0xa0d1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_394;
SF := unconstrained_395;
AF := unconstrained_396;
PF := unconstrained_397;

label_0xa0d5:
if (bv2bool(CF)) {
  goto label_0xa0d8;
}

label_0xa0d7:
assume false;

label_0xa0d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa0e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 800bv64));

label_0xa0e8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xa0ea:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa0ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa0f4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa0f7:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_398;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa0fc:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xa0ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa107:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa10a:
origDEST_1175 := RAX[32:0];
origCOUNT_1176 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), CF, LSHIFT_32(origDEST_1175, (MINUS_32(32bv32, origCOUNT_1176)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 1bv32)), origDEST_1175[32:31], unconstrained_399));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv32)), AF, unconstrained_400);

label_0xa10d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 660bv64), RAX[32:0]);

label_0xa114:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa11c:
t1_1181 := RAX;
t2_1182 := 60bv64;
RAX := PLUS_64(RAX, t2_1182);
CF := bool2bv(LT_64(RAX, t1_1181));
OF := AND_1((bool2bv((t1_1181[64:63]) == (t2_1182[64:63]))), (XOR_1((t1_1181[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1181)), t2_1182)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa120:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0xa128:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xa130:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_401;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa136:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa13b:
t_1189 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_402;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1189, 4bv64)), t_1189)), 2bv64)), (XOR_64((RSHIFT_64(t_1189, 4bv64)), t_1189)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1189, 4bv64)), t_1189)), 2bv64)), (XOR_64((RSHIFT_64(t_1189, 4bv64)), t_1189)))))[1:0]));
SF := t_1189[64:63];
ZF := bool2bv(0bv64 == t_1189);

label_0xa13e:
if (bv2bool(ZF)) {
  goto label_0xa141;
}

label_0xa140:
assume false;

label_0xa141:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xa149:
origDEST_1193 := RAX;
origCOUNT_1194 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), CF, LSHIFT_64(origDEST_1193, (MINUS_64(64bv64, origCOUNT_1194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 1bv64)), origDEST_1193[64:63], unconstrained_403));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1194 == 0bv64)), AF, unconstrained_404);

label_0xa14d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa154:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa158:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xa160:
origDEST_1199 := RCX;
origCOUNT_1200 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), CF, LSHIFT_64(origDEST_1199, (MINUS_64(64bv64, origCOUNT_1200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 1bv64)), origDEST_1199[64:63], unconstrained_405));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1200 == 0bv64)), AF, unconstrained_406);

label_0xa164:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_407;
SF := unconstrained_408;
AF := unconstrained_409;
PF := unconstrained_410;

label_0xa168:
if (bv2bool(CF)) {
  goto label_0xa16b;
}

label_0xa16a:
assume false;

label_0xa16b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xa173:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 660bv64)));

label_0xa17a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa17c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa184:
t_1205 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1205)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1205, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1205, 4bv32)), t_1205)), 2bv32)), (XOR_32((RSHIFT_32(t_1205, 4bv32)), t_1205)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1205, 4bv32)), t_1205)), 2bv32)), (XOR_32((RSHIFT_32(t_1205, 4bv32)), t_1205)))))[1:0]));
SF := t_1205[32:31];
ZF := bool2bv(0bv32 == t_1205);

label_0xa188:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa30d;
}

label_0xa18e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa196:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xa19a:
origDEST_1209 := RAX;
origCOUNT_1210 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), CF, RSHIFT_64(origDEST_1209, (MINUS_64(64bv64, origCOUNT_1210)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_411));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1210 == 0bv64)), AF, unconstrained_412);

label_0xa19e:
RCX := PLUS_64((PLUS_64(0bv64, 41381bv64)), 0bv64)[64:0];

label_0xa1a5:
t1_1215 := RCX;
t2_1216 := RAX;
RCX := PLUS_64(RCX, t2_1216);
CF := bool2bv(LT_64(RCX, t1_1215));
OF := AND_1((bool2bv((t1_1215[64:63]) == (t2_1216[64:63]))), (XOR_1((t1_1215[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1215)), t2_1216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa1a8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 808bv64), RCX);

label_0xa1b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa1b8:
t1_1221 := RAX;
t2_1222 := 24bv64;
RAX := PLUS_64(RAX, t2_1222);
CF := bool2bv(LT_64(RAX, t1_1221));
OF := AND_1((bool2bv((t1_1221[64:63]) == (t2_1222[64:63]))), (XOR_1((t1_1221[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1221)), t2_1222)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa1bc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0xa1c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xa1cc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_413;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa1d2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa1d7:
t_1229 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_414;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1229, 4bv64)), t_1229)), 2bv64)), (XOR_64((RSHIFT_64(t_1229, 4bv64)), t_1229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1229, 4bv64)), t_1229)), 2bv64)), (XOR_64((RSHIFT_64(t_1229, 4bv64)), t_1229)))))[1:0]));
SF := t_1229[64:63];
ZF := bool2bv(0bv64 == t_1229);

label_0xa1da:
if (bv2bool(ZF)) {
  goto label_0xa1dd;
}

label_0xa1dc:
assume false;

label_0xa1dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xa1e5:
origDEST_1233 := RAX;
origCOUNT_1234 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), CF, LSHIFT_64(origDEST_1233, (MINUS_64(64bv64, origCOUNT_1234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 1bv64)), origDEST_1233[64:63], unconstrained_415));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1234 == 0bv64)), AF, unconstrained_416);

label_0xa1e9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa1f0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa1f4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xa1fc:
origDEST_1239 := RCX;
origCOUNT_1240 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), CF, LSHIFT_64(origDEST_1239, (MINUS_64(64bv64, origCOUNT_1240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 1bv64)), origDEST_1239[64:63], unconstrained_417));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1240 == 0bv64)), AF, unconstrained_418);

label_0xa200:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_419;
SF := unconstrained_420;
AF := unconstrained_421;
PF := unconstrained_422;

label_0xa204:
if (bv2bool(CF)) {
  goto label_0xa207;
}

label_0xa206:
assume false;

label_0xa207:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xa20f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 808bv64));

label_0xa217:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xa219:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa21b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa223:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xa226:
t_1245 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1245[32:31]) == (1bv32[32:31]))), (XOR_1((t_1245[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1245)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa228:
mem := STORE_LE_32(mem, PLUS_64(RSP, 664bv64), RAX[32:0]);

label_0xa22f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa237:
t1_1249 := RAX;
t2_1250 := 28bv64;
RAX := PLUS_64(RAX, t2_1250);
CF := bool2bv(LT_64(RAX, t1_1249));
OF := AND_1((bool2bv((t1_1249[64:63]) == (t2_1250[64:63]))), (XOR_1((t1_1249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1249)), t2_1250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa23b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0xa243:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xa24b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_423;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa251:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa256:
t_1257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_424;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1257, 4bv64)), t_1257)), 2bv64)), (XOR_64((RSHIFT_64(t_1257, 4bv64)), t_1257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1257, 4bv64)), t_1257)), 2bv64)), (XOR_64((RSHIFT_64(t_1257, 4bv64)), t_1257)))))[1:0]));
SF := t_1257[64:63];
ZF := bool2bv(0bv64 == t_1257);

label_0xa259:
if (bv2bool(ZF)) {
  goto label_0xa25c;
}

label_0xa25b:
assume false;

label_0xa25c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xa264:
origDEST_1261 := RAX;
origCOUNT_1262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), CF, LSHIFT_64(origDEST_1261, (MINUS_64(64bv64, origCOUNT_1262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 1bv64)), origDEST_1261[64:63], unconstrained_425));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1262 == 0bv64)), AF, unconstrained_426);

label_0xa268:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa26f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa273:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xa27b:
origDEST_1267 := RCX;
origCOUNT_1268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), CF, LSHIFT_64(origDEST_1267, (MINUS_64(64bv64, origCOUNT_1268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 1bv64)), origDEST_1267[64:63], unconstrained_427));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1268 == 0bv64)), AF, unconstrained_428);

label_0xa27f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_429;
SF := unconstrained_430;
AF := unconstrained_431;
PF := unconstrained_432;

label_0xa283:
if (bv2bool(CF)) {
  goto label_0xa286;
}

label_0xa285:
assume false;

label_0xa286:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xa28e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 664bv64)));

label_0xa295:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa297:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa29f:
t_1273 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_1273)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1273, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1273, 4bv32)), t_1273)), 2bv32)), (XOR_32((RSHIFT_32(t_1273, 4bv32)), t_1273)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1273, 4bv32)), t_1273)), 2bv32)), (XOR_32((RSHIFT_32(t_1273, 4bv32)), t_1273)))))[1:0]));
SF := t_1273[32:31];
ZF := bool2bv(0bv32 == t_1273);

label_0xa2a6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa30d;
}

label_0xa2a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa2b0:
t1_1277 := RAX;
t2_1278 := 28bv64;
RAX := PLUS_64(RAX, t2_1278);
CF := bool2bv(LT_64(RAX, t1_1277));
OF := AND_1((bool2bv((t1_1277[64:63]) == (t2_1278[64:63]))), (XOR_1((t1_1277[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1277)), t2_1278)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa2b4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0xa2bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xa2c4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_433;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa2ca:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa2cf:
t_1285 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_434;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1285, 4bv64)), t_1285)), 2bv64)), (XOR_64((RSHIFT_64(t_1285, 4bv64)), t_1285)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1285, 4bv64)), t_1285)), 2bv64)), (XOR_64((RSHIFT_64(t_1285, 4bv64)), t_1285)))))[1:0]));
SF := t_1285[64:63];
ZF := bool2bv(0bv64 == t_1285);

label_0xa2d2:
if (bv2bool(ZF)) {
  goto label_0xa2d5;
}

label_0xa2d4:
assume false;

label_0xa2d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xa2dd:
origDEST_1289 := RAX;
origCOUNT_1290 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), CF, LSHIFT_64(origDEST_1289, (MINUS_64(64bv64, origCOUNT_1290)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 1bv64)), origDEST_1289[64:63], unconstrained_435));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1290 == 0bv64)), AF, unconstrained_436);

label_0xa2e1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa2e8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa2ec:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xa2f4:
origDEST_1295 := RCX;
origCOUNT_1296 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), CF, LSHIFT_64(origDEST_1295, (MINUS_64(64bv64, origCOUNT_1296)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 1bv64)), origDEST_1295[64:63], unconstrained_437));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1296 == 0bv64)), AF, unconstrained_438);

label_0xa2f8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_439;
SF := unconstrained_440;
AF := unconstrained_441;
PF := unconstrained_442;

label_0xa2fc:
if (bv2bool(CF)) {
  goto label_0xa2ff;
}

label_0xa2fe:
assume false;

label_0xa2ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xa307:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xa30d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa315:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xa318:
t_1301 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1301, 1bv32)), (XOR_32(t_1301, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1301)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa31a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 668bv64), RAX[32:0]);

label_0xa321:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa329:
t1_1305 := RAX;
t2_1306 := 24bv64;
RAX := PLUS_64(RAX, t2_1306);
CF := bool2bv(LT_64(RAX, t1_1305));
OF := AND_1((bool2bv((t1_1305[64:63]) == (t2_1306[64:63]))), (XOR_1((t1_1305[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1305)), t2_1306)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa32d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0xa335:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xa33d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_443;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa343:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa348:
t_1313 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_444;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)), 2bv64)), (XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)), 2bv64)), (XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)))))[1:0]));
SF := t_1313[64:63];
ZF := bool2bv(0bv64 == t_1313);

label_0xa34b:
if (bv2bool(ZF)) {
  goto label_0xa34e;
}

label_0xa34d:
assume false;

label_0xa34e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xa356:
origDEST_1317 := RAX;
origCOUNT_1318 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), CF, LSHIFT_64(origDEST_1317, (MINUS_64(64bv64, origCOUNT_1318)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 1bv64)), origDEST_1317[64:63], unconstrained_445));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), AF, unconstrained_446);

label_0xa35a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa361:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa365:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xa36d:
origDEST_1323 := RCX;
origCOUNT_1324 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), CF, LSHIFT_64(origDEST_1323, (MINUS_64(64bv64, origCOUNT_1324)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 1bv64)), origDEST_1323[64:63], unconstrained_447));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), AF, unconstrained_448);

label_0xa371:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_449;
SF := unconstrained_450;
AF := unconstrained_451;
PF := unconstrained_452;

label_0xa375:
if (bv2bool(CF)) {
  goto label_0xa378;
}

label_0xa377:
assume false;

label_0xa378:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xa380:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 668bv64)));

label_0xa387:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa389:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa391:
t_1329 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1329)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1329, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1329, 4bv32)), t_1329)), 2bv32)), (XOR_32((RSHIFT_32(t_1329, 4bv32)), t_1329)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1329, 4bv32)), t_1329)), 2bv32)), (XOR_32((RSHIFT_32(t_1329, 4bv32)), t_1329)))))[1:0]));
SF := t_1329[32:31];
ZF := bool2bv(0bv32 == t_1329);

label_0xa395:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa3a1;
}

label_0xa397:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), 1bv32);

label_0xa39f:
goto label_0xa3a9;

label_0xa3a1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), 0bv32);

label_0xa3a9:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xa3ad:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 68bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_453;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa3b1:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xa3b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa3bc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xa3c2:
t_1335 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1335[32:31]) == (1bv32[32:31]))), (XOR_1((t_1335[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1335)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa3c4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 672bv64), RAX[32:0]);

label_0xa3cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa3d3:
t1_1339 := RAX;
t2_1340 := 1092bv64;
RAX := PLUS_64(RAX, t2_1340);
CF := bool2bv(LT_64(RAX, t1_1339));
OF := AND_1((bool2bv((t1_1339[64:63]) == (t2_1340[64:63]))), (XOR_1((t1_1339[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1339)), t2_1340)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa3d9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0xa3e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xa3e9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_454;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa3ef:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa3f4:
t_1347 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_455;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1347, 4bv64)), t_1347)), 2bv64)), (XOR_64((RSHIFT_64(t_1347, 4bv64)), t_1347)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1347, 4bv64)), t_1347)), 2bv64)), (XOR_64((RSHIFT_64(t_1347, 4bv64)), t_1347)))))[1:0]));
SF := t_1347[64:63];
ZF := bool2bv(0bv64 == t_1347);

label_0xa3f7:
if (bv2bool(ZF)) {
  goto label_0xa3fa;
}

label_0xa3f9:
assume false;

label_0xa3fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xa402:
origDEST_1351 := RAX;
origCOUNT_1352 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), CF, LSHIFT_64(origDEST_1351, (MINUS_64(64bv64, origCOUNT_1352)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 1bv64)), origDEST_1351[64:63], unconstrained_456));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1352 == 0bv64)), AF, unconstrained_457);

label_0xa406:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa40d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa411:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xa419:
origDEST_1357 := RCX;
origCOUNT_1358 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), CF, LSHIFT_64(origDEST_1357, (MINUS_64(64bv64, origCOUNT_1358)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 1bv64)), origDEST_1357[64:63], unconstrained_458));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1358 == 0bv64)), AF, unconstrained_459);

label_0xa41d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_460;
SF := unconstrained_461;
AF := unconstrained_462;
PF := unconstrained_463;

label_0xa421:
if (bv2bool(CF)) {
  goto label_0xa424;
}

label_0xa423:
assume false;

label_0xa424:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xa42c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 672bv64)));

label_0xa433:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa435:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xa439:
t1_1363 := RAX[32:0];
t2_1364 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_1364));
CF := bool2bv(LT_32((RAX[32:0]), t1_1363));
OF := AND_1((bool2bv((t1_1363[32:31]) == (t2_1364[32:31]))), (XOR_1((t1_1363[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_1363)), t2_1364)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa43c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 676bv64), RAX[32:0]);

label_0xa443:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa44b:
t1_1369 := RAX;
t2_1370 := 16bv64;
RAX := PLUS_64(RAX, t2_1370);
CF := bool2bv(LT_64(RAX, t1_1369));
OF := AND_1((bool2bv((t1_1369[64:63]) == (t2_1370[64:63]))), (XOR_1((t1_1369[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1369)), t2_1370)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa44f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0xa457:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xa45f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_464;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa465:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa46a:
t_1377 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_465;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1377, 4bv64)), t_1377)), 2bv64)), (XOR_64((RSHIFT_64(t_1377, 4bv64)), t_1377)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1377, 4bv64)), t_1377)), 2bv64)), (XOR_64((RSHIFT_64(t_1377, 4bv64)), t_1377)))))[1:0]));
SF := t_1377[64:63];
ZF := bool2bv(0bv64 == t_1377);

label_0xa46d:
if (bv2bool(ZF)) {
  goto label_0xa470;
}

label_0xa46f:
assume false;

label_0xa470:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xa478:
origDEST_1381 := RAX;
origCOUNT_1382 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), CF, LSHIFT_64(origDEST_1381, (MINUS_64(64bv64, origCOUNT_1382)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 1bv64)), origDEST_1381[64:63], unconstrained_466));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1382 == 0bv64)), AF, unconstrained_467);

label_0xa47c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa483:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa487:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xa48f:
origDEST_1387 := RCX;
origCOUNT_1388 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), CF, LSHIFT_64(origDEST_1387, (MINUS_64(64bv64, origCOUNT_1388)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 1bv64)), origDEST_1387[64:63], unconstrained_468));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1388 == 0bv64)), AF, unconstrained_469);

label_0xa493:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_470;
SF := unconstrained_471;
AF := unconstrained_472;
PF := unconstrained_473;

label_0xa497:
if (bv2bool(CF)) {
  goto label_0xa49a;
}

label_0xa499:
assume false;

label_0xa49a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xa4a2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 676bv64)));

label_0xa4a9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa4ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa4b3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa4b6:
origDEST_1393 := RAX;
origCOUNT_1394 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), CF, RSHIFT_64(origDEST_1393, (MINUS_64(64bv64, origCOUNT_1394)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_474));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1394 == 0bv64)), AF, unconstrained_475);

label_0xa4ba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa4c2:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3152bv64));

label_0xa4c9:
t1_1399 := RCX;
t2_1400 := RAX;
RCX := PLUS_64(RCX, t2_1400);
CF := bool2bv(LT_64(RCX, t1_1399));
OF := AND_1((bool2bv((t1_1399[64:63]) == (t2_1400[64:63]))), (XOR_1((t1_1399[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1399)), t2_1400)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa4cc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 816bv64), RCX);

label_0xa4d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa4dc:
t1_1405 := RAX;
t2_1406 := 60bv64;
RAX := PLUS_64(RAX, t2_1406);
CF := bool2bv(LT_64(RAX, t1_1405));
OF := AND_1((bool2bv((t1_1405[64:63]) == (t2_1406[64:63]))), (XOR_1((t1_1405[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1405)), t2_1406)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa4e0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0xa4e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa4f0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_476;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa4f6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa4fb:
t_1413 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_477;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1413, 4bv64)), t_1413)), 2bv64)), (XOR_64((RSHIFT_64(t_1413, 4bv64)), t_1413)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1413, 4bv64)), t_1413)), 2bv64)), (XOR_64((RSHIFT_64(t_1413, 4bv64)), t_1413)))))[1:0]));
SF := t_1413[64:63];
ZF := bool2bv(0bv64 == t_1413);

label_0xa4fe:
if (bv2bool(ZF)) {
  goto label_0xa501;
}

label_0xa500:
assume false;

label_0xa501:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa509:
origDEST_1417 := RAX;
origCOUNT_1418 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), CF, LSHIFT_64(origDEST_1417, (MINUS_64(64bv64, origCOUNT_1418)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 1bv64)), origDEST_1417[64:63], unconstrained_478));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1418 == 0bv64)), AF, unconstrained_479);

label_0xa50d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa514:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa518:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa520:
origDEST_1423 := RCX;
origCOUNT_1424 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), CF, LSHIFT_64(origDEST_1423, (MINUS_64(64bv64, origCOUNT_1424)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 1bv64)), origDEST_1423[64:63], unconstrained_480));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1424 == 0bv64)), AF, unconstrained_481);

label_0xa524:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_482;
SF := unconstrained_483;
AF := unconstrained_484;
PF := unconstrained_485;

label_0xa528:
if (bv2bool(CF)) {
  goto label_0xa52b;
}

label_0xa52a:
assume false;

label_0xa52b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa533:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 816bv64));

label_0xa53b:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xa53d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa53f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa547:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa54a:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_486;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa54f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa557:
t1_1431 := RCX;
t2_1432 := 64bv64;
RCX := PLUS_64(RCX, t2_1432);
CF := bool2bv(LT_64(RCX, t1_1431));
OF := AND_1((bool2bv((t1_1431[64:63]) == (t2_1432[64:63]))), (XOR_1((t1_1431[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1431)), t2_1432)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa55b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RCX);

label_0xa563:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xa566:
mem := STORE_LE_32(mem, PLUS_64(RSP, 680bv64), RAX[32:0]);

label_0xa56d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xa575:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_487;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa57b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa580:
t_1439 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_488;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1439, 4bv64)), t_1439)), 2bv64)), (XOR_64((RSHIFT_64(t_1439, 4bv64)), t_1439)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1439, 4bv64)), t_1439)), 2bv64)), (XOR_64((RSHIFT_64(t_1439, 4bv64)), t_1439)))))[1:0]));
SF := t_1439[64:63];
ZF := bool2bv(0bv64 == t_1439);

label_0xa583:
if (bv2bool(ZF)) {
  goto label_0xa586;
}

label_0xa585:
assume false;

label_0xa586:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xa58e:
origDEST_1443 := RAX;
origCOUNT_1444 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), CF, LSHIFT_64(origDEST_1443, (MINUS_64(64bv64, origCOUNT_1444)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 1bv64)), origDEST_1443[64:63], unconstrained_489));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1444 == 0bv64)), AF, unconstrained_490);

label_0xa592:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa599:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa59d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xa5a5:
origDEST_1449 := RCX;
origCOUNT_1450 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), CF, LSHIFT_64(origDEST_1449, (MINUS_64(64bv64, origCOUNT_1450)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 1bv64)), origDEST_1449[64:63], unconstrained_491));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), AF, unconstrained_492);

label_0xa5a9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_493;
SF := unconstrained_494;
AF := unconstrained_495;
PF := unconstrained_496;

label_0xa5ad:
if (bv2bool(CF)) {
  goto label_0xa5b0;
}

label_0xa5af:
assume false;

label_0xa5b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xa5b8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 680bv64)));

label_0xa5bf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa5c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa5c9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa5cc:
origDEST_1455 := RAX[32:0];
origCOUNT_1456 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), CF, LSHIFT_32(origDEST_1455, (MINUS_32(32bv32, origCOUNT_1456)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 1bv32)), origDEST_1455[32:31], unconstrained_497));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1456 == 0bv32)), AF, unconstrained_498);

label_0xa5cf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 684bv64), RAX[32:0]);

label_0xa5d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa5de:
t1_1461 := RAX;
t2_1462 := 60bv64;
RAX := PLUS_64(RAX, t2_1462);
CF := bool2bv(LT_64(RAX, t1_1461));
OF := AND_1((bool2bv((t1_1461[64:63]) == (t2_1462[64:63]))), (XOR_1((t1_1461[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1461)), t2_1462)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa5e2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0xa5ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xa5f2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_499;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa5f8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa5fd:
t_1469 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_500;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)), 2bv64)), (XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)), 2bv64)), (XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)))))[1:0]));
SF := t_1469[64:63];
ZF := bool2bv(0bv64 == t_1469);

label_0xa600:
if (bv2bool(ZF)) {
  goto label_0xa603;
}

label_0xa602:
assume false;

label_0xa603:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xa60b:
origDEST_1473 := RAX;
origCOUNT_1474 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), CF, LSHIFT_64(origDEST_1473, (MINUS_64(64bv64, origCOUNT_1474)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 1bv64)), origDEST_1473[64:63], unconstrained_501));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), AF, unconstrained_502);

label_0xa60f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa616:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa61a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xa622:
origDEST_1479 := RCX;
origCOUNT_1480 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), CF, LSHIFT_64(origDEST_1479, (MINUS_64(64bv64, origCOUNT_1480)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 1bv64)), origDEST_1479[64:63], unconstrained_503));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), AF, unconstrained_504);

label_0xa626:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_505;
SF := unconstrained_506;
AF := unconstrained_507;
PF := unconstrained_508;

label_0xa62a:
if (bv2bool(CF)) {
  goto label_0xa62d;
}

label_0xa62c:
assume false;

label_0xa62d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xa635:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 684bv64)));

label_0xa63c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa63e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa646:
t_1485 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1485)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1485, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1485, 4bv32)), t_1485)), 2bv32)), (XOR_32((RSHIFT_32(t_1485, 4bv32)), t_1485)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1485, 4bv32)), t_1485)), 2bv32)), (XOR_32((RSHIFT_32(t_1485, 4bv32)), t_1485)))))[1:0]));
SF := t_1485[32:31];
ZF := bool2bv(0bv32 == t_1485);

label_0xa64a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa7cf;
}

label_0xa650:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa658:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xa65c:
origDEST_1489 := RAX;
origCOUNT_1490 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), CF, RSHIFT_64(origDEST_1489, (MINUS_64(64bv64, origCOUNT_1490)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_509));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1490 == 0bv64)), AF, unconstrained_510);

label_0xa660:
RCX := PLUS_64((PLUS_64(0bv64, 42599bv64)), 0bv64)[64:0];

label_0xa667:
t1_1495 := RCX;
t2_1496 := RAX;
RCX := PLUS_64(RCX, t2_1496);
CF := bool2bv(LT_64(RCX, t1_1495));
OF := AND_1((bool2bv((t1_1495[64:63]) == (t2_1496[64:63]))), (XOR_1((t1_1495[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1495)), t2_1496)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa66a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 824bv64), RCX);

label_0xa672:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa67a:
t1_1501 := RAX;
t2_1502 := 24bv64;
RAX := PLUS_64(RAX, t2_1502);
CF := bool2bv(LT_64(RAX, t1_1501));
OF := AND_1((bool2bv((t1_1501[64:63]) == (t2_1502[64:63]))), (XOR_1((t1_1501[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1501)), t2_1502)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa67e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0xa686:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xa68e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_511;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa694:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa699:
t_1509 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_512;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1509, 4bv64)), t_1509)), 2bv64)), (XOR_64((RSHIFT_64(t_1509, 4bv64)), t_1509)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1509, 4bv64)), t_1509)), 2bv64)), (XOR_64((RSHIFT_64(t_1509, 4bv64)), t_1509)))))[1:0]));
SF := t_1509[64:63];
ZF := bool2bv(0bv64 == t_1509);

label_0xa69c:
if (bv2bool(ZF)) {
  goto label_0xa69f;
}

label_0xa69e:
assume false;

label_0xa69f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xa6a7:
origDEST_1513 := RAX;
origCOUNT_1514 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), CF, LSHIFT_64(origDEST_1513, (MINUS_64(64bv64, origCOUNT_1514)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 1bv64)), origDEST_1513[64:63], unconstrained_513));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1514 == 0bv64)), AF, unconstrained_514);

label_0xa6ab:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa6b2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa6b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xa6be:
origDEST_1519 := RCX;
origCOUNT_1520 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), CF, LSHIFT_64(origDEST_1519, (MINUS_64(64bv64, origCOUNT_1520)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 1bv64)), origDEST_1519[64:63], unconstrained_515));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1520 == 0bv64)), AF, unconstrained_516);

label_0xa6c2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_517;
SF := unconstrained_518;
AF := unconstrained_519;
PF := unconstrained_520;

label_0xa6c6:
if (bv2bool(CF)) {
  goto label_0xa6c9;
}

label_0xa6c8:
assume false;

label_0xa6c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xa6d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 824bv64));

label_0xa6d9:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xa6db:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa6dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa6e5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xa6e8:
t_1525 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1525[32:31]) == (1bv32[32:31]))), (XOR_1((t_1525[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1525)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa6ea:
mem := STORE_LE_32(mem, PLUS_64(RSP, 688bv64), RAX[32:0]);

label_0xa6f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa6f9:
t1_1529 := RAX;
t2_1530 := 28bv64;
RAX := PLUS_64(RAX, t2_1530);
CF := bool2bv(LT_64(RAX, t1_1529));
OF := AND_1((bool2bv((t1_1529[64:63]) == (t2_1530[64:63]))), (XOR_1((t1_1529[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1529)), t2_1530)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa6fd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0xa705:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xa70d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_521;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa713:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa718:
t_1537 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_522;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1537, 4bv64)), t_1537)), 2bv64)), (XOR_64((RSHIFT_64(t_1537, 4bv64)), t_1537)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1537, 4bv64)), t_1537)), 2bv64)), (XOR_64((RSHIFT_64(t_1537, 4bv64)), t_1537)))))[1:0]));
SF := t_1537[64:63];
ZF := bool2bv(0bv64 == t_1537);

label_0xa71b:
if (bv2bool(ZF)) {
  goto label_0xa71e;
}

label_0xa71d:
assume false;

label_0xa71e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xa726:
origDEST_1541 := RAX;
origCOUNT_1542 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), CF, LSHIFT_64(origDEST_1541, (MINUS_64(64bv64, origCOUNT_1542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 1bv64)), origDEST_1541[64:63], unconstrained_523));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1542 == 0bv64)), AF, unconstrained_524);

label_0xa72a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa731:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa735:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xa73d:
origDEST_1547 := RCX;
origCOUNT_1548 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), CF, LSHIFT_64(origDEST_1547, (MINUS_64(64bv64, origCOUNT_1548)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 1bv64)), origDEST_1547[64:63], unconstrained_525));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1548 == 0bv64)), AF, unconstrained_526);

label_0xa741:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_527;
SF := unconstrained_528;
AF := unconstrained_529;
PF := unconstrained_530;

label_0xa745:
if (bv2bool(CF)) {
  goto label_0xa748;
}

label_0xa747:
assume false;

label_0xa748:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xa750:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 688bv64)));

label_0xa757:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa759:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa761:
t_1553 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_1553)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1553, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1553, 4bv32)), t_1553)), 2bv32)), (XOR_32((RSHIFT_32(t_1553, 4bv32)), t_1553)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1553, 4bv32)), t_1553)), 2bv32)), (XOR_32((RSHIFT_32(t_1553, 4bv32)), t_1553)))))[1:0]));
SF := t_1553[32:31];
ZF := bool2bv(0bv32 == t_1553);

label_0xa768:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa7cf;
}

label_0xa76a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa772:
t1_1557 := RAX;
t2_1558 := 28bv64;
RAX := PLUS_64(RAX, t2_1558);
CF := bool2bv(LT_64(RAX, t1_1557));
OF := AND_1((bool2bv((t1_1557[64:63]) == (t2_1558[64:63]))), (XOR_1((t1_1557[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1557)), t2_1558)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa776:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0xa77e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xa786:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_531;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa78c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa791:
t_1565 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_532;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1565, 4bv64)), t_1565)), 2bv64)), (XOR_64((RSHIFT_64(t_1565, 4bv64)), t_1565)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1565, 4bv64)), t_1565)), 2bv64)), (XOR_64((RSHIFT_64(t_1565, 4bv64)), t_1565)))))[1:0]));
SF := t_1565[64:63];
ZF := bool2bv(0bv64 == t_1565);

label_0xa794:
if (bv2bool(ZF)) {
  goto label_0xa797;
}

label_0xa796:
assume false;

label_0xa797:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xa79f:
origDEST_1569 := RAX;
origCOUNT_1570 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), CF, LSHIFT_64(origDEST_1569, (MINUS_64(64bv64, origCOUNT_1570)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 1bv64)), origDEST_1569[64:63], unconstrained_533));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1570 == 0bv64)), AF, unconstrained_534);

label_0xa7a3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa7aa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa7ae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xa7b6:
origDEST_1575 := RCX;
origCOUNT_1576 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), CF, LSHIFT_64(origDEST_1575, (MINUS_64(64bv64, origCOUNT_1576)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 1bv64)), origDEST_1575[64:63], unconstrained_535));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1576 == 0bv64)), AF, unconstrained_536);

label_0xa7ba:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_537;
SF := unconstrained_538;
AF := unconstrained_539;
PF := unconstrained_540;

label_0xa7be:
if (bv2bool(CF)) {
  goto label_0xa7c1;
}

label_0xa7c0:
assume false;

label_0xa7c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xa7c9:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xa7cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa7d7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xa7da:
t_1581 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1581, 1bv32)), (XOR_32(t_1581, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1581)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa7dc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 692bv64), RAX[32:0]);

label_0xa7e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa7eb:
t1_1585 := RAX;
t2_1586 := 24bv64;
RAX := PLUS_64(RAX, t2_1586);
CF := bool2bv(LT_64(RAX, t1_1585));
OF := AND_1((bool2bv((t1_1585[64:63]) == (t2_1586[64:63]))), (XOR_1((t1_1585[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1585)), t2_1586)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa7ef:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0xa7f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xa7ff:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_541;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa805:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa80a:
t_1593 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_542;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1593, 4bv64)), t_1593)), 2bv64)), (XOR_64((RSHIFT_64(t_1593, 4bv64)), t_1593)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1593, 4bv64)), t_1593)), 2bv64)), (XOR_64((RSHIFT_64(t_1593, 4bv64)), t_1593)))))[1:0]));
SF := t_1593[64:63];
ZF := bool2bv(0bv64 == t_1593);

label_0xa80d:
if (bv2bool(ZF)) {
  goto label_0xa810;
}

label_0xa80f:
assume false;

label_0xa810:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xa818:
origDEST_1597 := RAX;
origCOUNT_1598 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), CF, LSHIFT_64(origDEST_1597, (MINUS_64(64bv64, origCOUNT_1598)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 1bv64)), origDEST_1597[64:63], unconstrained_543));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1598 == 0bv64)), AF, unconstrained_544);

label_0xa81c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa823:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa827:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xa82f:
origDEST_1603 := RCX;
origCOUNT_1604 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), CF, LSHIFT_64(origDEST_1603, (MINUS_64(64bv64, origCOUNT_1604)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 1bv64)), origDEST_1603[64:63], unconstrained_545));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1604 == 0bv64)), AF, unconstrained_546);

label_0xa833:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_547;
SF := unconstrained_548;
AF := unconstrained_549;
PF := unconstrained_550;

label_0xa837:
if (bv2bool(CF)) {
  goto label_0xa83a;
}

label_0xa839:
assume false;

label_0xa83a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xa842:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 692bv64)));

label_0xa849:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa84b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa853:
t_1609 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1609)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1609, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1609, 4bv32)), t_1609)), 2bv32)), (XOR_32((RSHIFT_32(t_1609, 4bv32)), t_1609)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1609, 4bv32)), t_1609)), 2bv32)), (XOR_32((RSHIFT_32(t_1609, 4bv32)), t_1609)))))[1:0]));
SF := t_1609[32:31];
ZF := bool2bv(0bv32 == t_1609);

label_0xa857:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa863;
}

label_0xa859:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 1bv32);

label_0xa861:
goto label_0xa86b;

label_0xa863:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 0bv32);

label_0xa86b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa873:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 72bv64)));

label_0xa877:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64bv64)));

label_0xa87a:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_551;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa87c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 696bv64), RAX[32:0]);

label_0xa883:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa88b:
t1_1615 := RAX;
t2_1616 := 64bv64;
RAX := PLUS_64(RAX, t2_1616);
CF := bool2bv(LT_64(RAX, t1_1615));
OF := AND_1((bool2bv((t1_1615[64:63]) == (t2_1616[64:63]))), (XOR_1((t1_1615[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1615)), t2_1616)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa88f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RAX);

label_0xa897:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xa89f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_552;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa8a5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa8aa:
t_1623 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_553;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1623, 4bv64)), t_1623)), 2bv64)), (XOR_64((RSHIFT_64(t_1623, 4bv64)), t_1623)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1623, 4bv64)), t_1623)), 2bv64)), (XOR_64((RSHIFT_64(t_1623, 4bv64)), t_1623)))))[1:0]));
SF := t_1623[64:63];
ZF := bool2bv(0bv64 == t_1623);

label_0xa8ad:
if (bv2bool(ZF)) {
  goto label_0xa8b0;
}

label_0xa8af:
assume false;

label_0xa8b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xa8b8:
origDEST_1627 := RAX;
origCOUNT_1628 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), CF, LSHIFT_64(origDEST_1627, (MINUS_64(64bv64, origCOUNT_1628)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 1bv64)), origDEST_1627[64:63], unconstrained_554));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1628 == 0bv64)), AF, unconstrained_555);

label_0xa8bc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa8c3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa8c7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xa8cf:
origDEST_1633 := RCX;
origCOUNT_1634 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), CF, LSHIFT_64(origDEST_1633, (MINUS_64(64bv64, origCOUNT_1634)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 1bv64)), origDEST_1633[64:63], unconstrained_556));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), AF, unconstrained_557);

label_0xa8d3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_558;
SF := unconstrained_559;
AF := unconstrained_560;
PF := unconstrained_561;

label_0xa8d7:
if (bv2bool(CF)) {
  goto label_0xa8da;
}

label_0xa8d9:
assume false;

label_0xa8da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xa8e2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 696bv64)));

label_0xa8e9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa8eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa8f3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xa8f9:
t_1639 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1639[32:31]) == (1bv32[32:31]))), (XOR_1((t_1639[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1639)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa8fb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 700bv64), RAX[32:0]);

label_0xa902:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa90a:
t1_1643 := RAX;
t2_1644 := 1092bv64;
RAX := PLUS_64(RAX, t2_1644);
CF := bool2bv(LT_64(RAX, t1_1643));
OF := AND_1((bool2bv((t1_1643[64:63]) == (t2_1644[64:63]))), (XOR_1((t1_1643[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1643)), t2_1644)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa910:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0xa918:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xa920:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_562;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa926:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa92b:
t_1651 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_563;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)), 2bv64)), (XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)), 2bv64)), (XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)))))[1:0]));
SF := t_1651[64:63];
ZF := bool2bv(0bv64 == t_1651);

label_0xa92e:
if (bv2bool(ZF)) {
  goto label_0xa931;
}

label_0xa930:
assume false;

label_0xa931:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xa939:
origDEST_1655 := RAX;
origCOUNT_1656 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), CF, LSHIFT_64(origDEST_1655, (MINUS_64(64bv64, origCOUNT_1656)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 1bv64)), origDEST_1655[64:63], unconstrained_564));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), AF, unconstrained_565);

label_0xa93d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa944:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa948:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xa950:
origDEST_1661 := RCX;
origCOUNT_1662 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), CF, LSHIFT_64(origDEST_1661, (MINUS_64(64bv64, origCOUNT_1662)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 1bv64)), origDEST_1661[64:63], unconstrained_566));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), AF, unconstrained_567);

label_0xa954:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_568;
SF := unconstrained_569;
AF := unconstrained_570;
PF := unconstrained_571;

label_0xa958:
if (bv2bool(CF)) {
  goto label_0xa95b;
}

label_0xa95a:
assume false;

label_0xa95b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xa963:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 700bv64)));

label_0xa96a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa96c:
goto label_0x8d00;

label_0xa971:
goto label_0xb22d;

label_0xa976:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa97e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64)));

label_0xa984:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), RAX[32:0]);

label_0xa988:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa990:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 12bv64))));

label_0xa994:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0xa998:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9a0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0xa9a3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0xa9a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9af:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xa9b5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xa9b9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9c1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64bv64)));

label_0xa9c4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xa9c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9d0:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 3152bv64));

label_0xa9d7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0xa9dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9e4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xa9e7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xa9eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xa9f3:
RAX := LOAD_LE_64(mem, RAX);

label_0xa9f6:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0xa9fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0xa9ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xaa07:
RAX := LOAD_LE_64(mem, RAX);

label_0xaa0a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0xaa0d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0xaa11:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xaa15:
mem := STORE_LE_32(mem, PLUS_64(RSP, 704bv64), RAX[32:0]);

label_0xaa1c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xaa24:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xaa2a:
t_1667 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1667[32:31]) == (1bv32[32:31]))), (XOR_1((t_1667[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1667)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xaa2c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0xaa30:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_572;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xaa32:
t_1671 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_1671)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1671, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1671, 4bv32)), t_1671)), 2bv32)), (XOR_32((RSHIFT_32(t_1671, 4bv32)), t_1671)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1671, 4bv32)), t_1671)), 2bv32)), (XOR_32((RSHIFT_32(t_1671, 4bv32)), t_1671)))))[1:0]));
SF := t_1671[32:31];
ZF := bool2bv(0bv32 == t_1671);

label_0xaa35:
if (bv2bool(ZF)) {
  goto label_0xad4c;
}

label_0xaa3b:
t_1675 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), t_1675)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1675, (LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1675, 4bv32)), t_1675)), 2bv32)), (XOR_32((RSHIFT_32(t_1675, 4bv32)), t_1675)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1675, 4bv32)), t_1675)), 2bv32)), (XOR_32((RSHIFT_32(t_1675, 4bv32)), t_1675)))))[1:0]));
SF := t_1675[32:31];
ZF := bool2bv(0bv32 == t_1675);

label_0xaa40:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xab90;
}

label_0xaa46:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_573;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xaa48:
t_1679 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_1679)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1679, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1679, 4bv32)), t_1679)), 2bv32)), (XOR_32((RSHIFT_32(t_1679, 4bv32)), t_1679)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1679, 4bv32)), t_1679)), 2bv32)), (XOR_32((RSHIFT_32(t_1679, 4bv32)), t_1679)))))[1:0]));
SF := t_1679[32:31];
ZF := bool2bv(0bv32 == t_1679);

label_0xaa4b:
if (bv2bool(ZF)) {
  goto label_0xaafa;
}

label_0xaa51:
t_1683 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), t_1683)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1683, (LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1683, 4bv32)), t_1683)), 2bv32)), (XOR_32((RSHIFT_32(t_1683, 4bv32)), t_1683)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1683, 4bv32)), t_1683)), 2bv32)), (XOR_32((RSHIFT_32(t_1683, 4bv32)), t_1683)))))[1:0]));
SF := t_1683[32:31];
ZF := bool2bv(0bv32 == t_1683);

label_0xaa56:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xaa5d;
}

label_0xaa58:
goto label_0xad4c;

label_0xaa5d:
t_1687 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), t_1687)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1687, (LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1687, 4bv32)), t_1687)), 2bv32)), (XOR_32((RSHIFT_32(t_1687, 4bv32)), t_1687)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1687, 4bv32)), t_1687)), 2bv32)), (XOR_32((RSHIFT_32(t_1687, 4bv32)), t_1687)))))[1:0]));
SF := t_1687[32:31];
ZF := bool2bv(0bv32 == t_1687);

label_0xaa62:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xaa69;
}

label_0xaa64:
goto label_0xaafa;

label_0xaa69:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaa6e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_574;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaa74:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xaa79:
t_1693 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_575;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1693, 4bv64)), t_1693)), 2bv64)), (XOR_64((RSHIFT_64(t_1693, 4bv64)), t_1693)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1693, 4bv64)), t_1693)), 2bv64)), (XOR_64((RSHIFT_64(t_1693, 4bv64)), t_1693)))))[1:0]));
SF := t_1693[64:63];
ZF := bool2bv(0bv64 == t_1693);

label_0xaa7c:
if (bv2bool(ZF)) {
  goto label_0xaa7f;
}

label_0xaa7e:
assume false;

label_0xaa7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaa84:
origDEST_1697 := RAX;
origCOUNT_1698 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), CF, LSHIFT_64(origDEST_1697, (MINUS_64(64bv64, origCOUNT_1698)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 1bv64)), origDEST_1697[64:63], unconstrained_576));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1698 == 0bv64)), AF, unconstrained_577);

label_0xaa88:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xaa8f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xaa93:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaa98:
origDEST_1703 := RCX;
origCOUNT_1704 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), CF, LSHIFT_64(origDEST_1703, (MINUS_64(64bv64, origCOUNT_1704)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 1bv64)), origDEST_1703[64:63], unconstrained_578));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1704 == 0bv64)), AF, unconstrained_579);

label_0xaa9c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_580;
SF := unconstrained_581;
AF := unconstrained_582;
PF := unconstrained_583;

label_0xaaa0:
if (bv2bool(CF)) {
  goto label_0xaaa3;
}

label_0xaaa2:
assume false;

label_0xaaa3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaaa8:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0xaaad:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xaaaf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0xaab3:
origDEST_1709 := RAX[32:0];
origCOUNT_1710 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), CF, RSHIFT_32(origDEST_1709, (MINUS_32(32bv32, origCOUNT_1710)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_584));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1710 == 0bv32)), AF, unconstrained_585);

label_0xaab6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0xaaba:
origDEST_1715 := RCX[32:0];
origCOUNT_1716 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), CF, LSHIFT_32(origDEST_1715, (MINUS_32(32bv32, origCOUNT_1716)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 1bv32)), origDEST_1715[32:31], unconstrained_586));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1716 == 0bv32)), AF, unconstrained_587);

label_0xaabd:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0xaac2:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_588;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xaac4:
RCX := (0bv32 ++ RCX[32:0]);

label_0xaac6:
RDX := PLUS_64((PLUS_64(0bv64, 43725bv64)), 0bv64)[64:0];

label_0xaacd:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_589;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xaad0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), RAX[32:0]);

label_0xaad4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64)));

label_0xaad8:
t_1725 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1725, 1bv32)), (XOR_32(t_1725, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1725)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xaada:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0xaade:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaae3:
t_1729 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_1729[64:63]) == (1bv64[64:63]))), (XOR_1((t_1729[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_1729)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaae6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0xaaeb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xaaef:
t_1733 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1733, 1bv32)), (XOR_32(t_1733, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1733)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xaaf1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0xaaf5:
goto label_0xaa46;

label_0xaafa:
t_1737 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), t_1737)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1737, (LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1737, 4bv32)), t_1737)), 2bv32)), (XOR_32((RSHIFT_32(t_1737, 4bv32)), t_1737)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1737, 4bv32)), t_1737)), 2bv32)), (XOR_32((RSHIFT_32(t_1737, 4bv32)), t_1737)))))[1:0]));
SF := t_1737[32:31];
ZF := bool2bv(0bv32 == t_1737);

label_0xaaff:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xab0e;
}

label_0xab01:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), 1bv32);

label_0xab09:
goto label_0xad4c;

label_0xab0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xab13:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_590;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xab19:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xab1e:
t_1743 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_591;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1743, 4bv64)), t_1743)), 2bv64)), (XOR_64((RSHIFT_64(t_1743, 4bv64)), t_1743)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1743, 4bv64)), t_1743)), 2bv64)), (XOR_64((RSHIFT_64(t_1743, 4bv64)), t_1743)))))[1:0]));
SF := t_1743[64:63];
ZF := bool2bv(0bv64 == t_1743);

label_0xab21:
if (bv2bool(ZF)) {
  goto label_0xab24;
}

label_0xab23:
assume false;

label_0xab24:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xab29:
origDEST_1747 := RAX;
origCOUNT_1748 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), CF, LSHIFT_64(origDEST_1747, (MINUS_64(64bv64, origCOUNT_1748)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 1bv64)), origDEST_1747[64:63], unconstrained_592));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1748 == 0bv64)), AF, unconstrained_593);

label_0xab2d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xab34:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xab38:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xab3d:
origDEST_1753 := RCX;
origCOUNT_1754 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), CF, LSHIFT_64(origDEST_1753, (MINUS_64(64bv64, origCOUNT_1754)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 1bv64)), origDEST_1753[64:63], unconstrained_594));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1754 == 0bv64)), AF, unconstrained_595);

label_0xab41:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_596;
SF := unconstrained_597;
AF := unconstrained_598;
PF := unconstrained_599;

label_0xab45:
if (bv2bool(CF)) {
  goto label_0xab48;
}

label_0xab47:
assume false;

label_0xab48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xab4d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0xab52:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xab54:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0xab58:
origDEST_1759 := RAX[32:0];
origCOUNT_1760 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), CF, RSHIFT_32(origDEST_1759, (MINUS_32(32bv32, origCOUNT_1760)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_600));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1760 == 0bv32)), AF, unconstrained_601);

label_0xab5b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0xab5f:
origDEST_1765 := RCX[32:0];
origCOUNT_1766 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), CF, LSHIFT_32(origDEST_1765, (MINUS_32(32bv32, origCOUNT_1766)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 1bv32)), origDEST_1765[32:31], unconstrained_602));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1766 == 0bv32)), AF, unconstrained_603);

label_0xab62:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0xab67:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_604;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xab69:
RCX := (0bv32 ++ RCX[32:0]);

label_0xab6b:
RDX := PLUS_64((PLUS_64(0bv64, 43890bv64)), 0bv64)[64:0];

label_0xab72:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_605;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xab75:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), RAX[32:0]);

label_0xab79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xab7e:
t_1775 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_1775[64:63]) == (1bv64[64:63]))), (XOR_1((t_1775[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_1775)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xab81:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0xab86:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xab8a:
t_1779 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1779, 1bv32)), (XOR_32(t_1779, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1779)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xab8c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0xab90:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0xab94:
t_1783 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_1783)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1783, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1783, 4bv32)), t_1783)), 2bv32)), (XOR_32((RSHIFT_32(t_1783, 4bv32)), t_1783)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1783, 4bv32)), t_1783)), 2bv32)), (XOR_32((RSHIFT_32(t_1783, 4bv32)), t_1783)))))[1:0]));
SF := t_1783[32:31];
ZF := bool2bv(0bv32 == t_1783);

label_0xab98:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xaba1;
}

label_0xab9a:
RAX := (RAX[64:8]) ++ 1bv8;

label_0xab9c:
goto label_0xb22f;

label_0xaba1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0xaba5:
t_1787 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_1787)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1787, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1787, 4bv32)), t_1787)), 2bv32)), (XOR_32((RSHIFT_32(t_1787, 4bv32)), t_1787)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1787, 4bv32)), t_1787)), 2bv32)), (XOR_32((RSHIFT_32(t_1787, 4bv32)), t_1787)))))[1:0]));
SF := t_1787[32:31];
ZF := bool2bv(0bv32 == t_1787);

label_0xaba9:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xabb8;
}

label_0xabab:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), 0bv32);

label_0xabb3:
goto label_0xad4c;

label_0xabb8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 16bv64))));

label_0xabbd:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0xabc1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xabc5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xabca:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0xabcd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xabd1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xabd5:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_606;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xabda:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xabdd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xabe1:
origDEST_1793 := RAX[32:0];
origCOUNT_1794 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), CF, LSHIFT_32(origDEST_1793, (MINUS_32(32bv32, origCOUNT_1794)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 1bv32)), origDEST_1793[32:31], unconstrained_607));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv32)), AF, unconstrained_608);

label_0xabe4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xabe8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xabec:
t_1799 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1799[32:31]) == (1bv32[32:31]))), (XOR_1((t_1799[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1799)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xabee:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xabf2:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xabf6:
t_1803 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))), (XOR_32((RAX[32:0]), t_1803)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1803, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1803, 4bv32)), t_1803)), 2bv32)), (XOR_32((RSHIFT_32(t_1803, 4bv32)), t_1803)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1803, 4bv32)), t_1803)), 2bv32)), (XOR_32((RSHIFT_32(t_1803, 4bv32)), t_1803)))))[1:0]));
SF := t_1803[32:31];
ZF := bool2bv(0bv32 == t_1803);

label_0xabfa:
if (bv2bool(ZF)) {
  goto label_0xac09;
}

label_0xabfc:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xac00:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xac04:
goto label_0xaafa;

label_0xac09:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0xac0d:
t_1807 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_1807)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1807, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1807, 4bv32)), t_1807)), 2bv32)), (XOR_32((RSHIFT_32(t_1807, 4bv32)), t_1807)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1807, 4bv32)), t_1807)), 2bv32)), (XOR_32((RSHIFT_32(t_1807, 4bv32)), t_1807)))))[1:0]));
SF := t_1807[32:31];
ZF := bool2bv(0bv32 == t_1807);

label_0xac11:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xac18;
}

label_0xac13:
goto label_0xaafa;

label_0xac18:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), 2bv32);

label_0xac20:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac24:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xac29:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0xac2c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xac30:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac34:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_609;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xac39:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xac3c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac40:
origDEST_1813 := RAX[32:0];
origCOUNT_1814 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), CF, LSHIFT_32(origDEST_1813, (MINUS_32(32bv32, origCOUNT_1814)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 1bv32)), origDEST_1813[32:31], unconstrained_610));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv32)), AF, unconstrained_611);

label_0xac43:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xac47:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xac4b:
t_1819 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1819[32:31]) == (1bv32[32:31]))), (XOR_1((t_1819[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1819)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xac4d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xac51:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0xac55:
t_1823 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_1823)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1823, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1823, 4bv32)), t_1823)), 2bv32)), (XOR_32((RSHIFT_32(t_1823, 4bv32)), t_1823)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1823, 4bv32)), t_1823)), 2bv32)), (XOR_32((RSHIFT_32(t_1823, 4bv32)), t_1823)))))[1:0]));
SF := t_1823[32:31];
ZF := bool2bv(0bv32 == t_1823);

label_0xac59:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xac60;
}

label_0xac5b:
goto label_0xaa30;

label_0xac60:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xac64:
t_1827 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))), (XOR_32((RAX[32:0]), t_1827)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1827, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1827, 4bv32)), t_1827)), 2bv32)), (XOR_32((RSHIFT_32(t_1827, 4bv32)), t_1827)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1827, 4bv32)), t_1827)), 2bv32)), (XOR_32((RSHIFT_32(t_1827, 4bv32)), t_1827)))))[1:0]));
SF := t_1827[32:31];
ZF := bool2bv(0bv32 == t_1827);

label_0xac68:
if (bv2bool(ZF)) {
  goto label_0xac77;
}

label_0xac6a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xac6e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xac72:
goto label_0xaa30;

label_0xac77:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), 3bv32);

label_0xac7f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac83:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xac88:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0xac8b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xac8f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac93:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_612;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xac98:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xac9b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xac9f:
origDEST_1833 := RAX[32:0];
origCOUNT_1834 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), CF, LSHIFT_32(origDEST_1833, (MINUS_32(32bv32, origCOUNT_1834)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 1bv32)), origDEST_1833[32:31], unconstrained_613));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1834 == 0bv32)), AF, unconstrained_614);

label_0xaca2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xaca6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xacaa:
t_1839 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1839[32:31]) == (1bv32[32:31]))), (XOR_1((t_1839[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1839)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xacac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xacb0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0xacb4:
t_1843 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_1843)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1843, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1843, 4bv32)), t_1843)), 2bv32)), (XOR_32((RSHIFT_32(t_1843, 4bv32)), t_1843)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1843, 4bv32)), t_1843)), 2bv32)), (XOR_32((RSHIFT_32(t_1843, 4bv32)), t_1843)))))[1:0]));
SF := t_1843[32:31];
ZF := bool2bv(0bv32 == t_1843);

label_0xacb8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xacbf;
}

label_0xacba:
goto label_0xaa30;

label_0xacbf:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xacc3:
t_1847 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))), (XOR_32((RAX[32:0]), t_1847)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1847, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 16bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1847, 4bv32)), t_1847)), 2bv32)), (XOR_32((RSHIFT_32(t_1847, 4bv32)), t_1847)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1847, 4bv32)), t_1847)), 2bv32)), (XOR_32((RSHIFT_32(t_1847, 4bv32)), t_1847)))))[1:0]));
SF := t_1847[32:31];
ZF := bool2bv(0bv32 == t_1847);

label_0xacc7:
if (bv2bool(ZF)) {
  goto label_0xacd6;
}

label_0xacc9:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xaccd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xacd1:
goto label_0xaa30;

label_0xacd6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xacda:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xacdf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0xace2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xace6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xacea:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_615;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xacef:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0xacf2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xacf6:
origDEST_1853 := RAX[32:0];
origCOUNT_1854 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), CF, LSHIFT_32(origDEST_1853, (MINUS_32(32bv32, origCOUNT_1854)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 1bv32)), origDEST_1853[32:31], unconstrained_616));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1854 == 0bv32)), AF, unconstrained_617);

label_0xacf9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xacfd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xad01:
t_1859 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1859[32:31]) == (1bv32[32:31]))), (XOR_1((t_1859[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1859)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xad03:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xad07:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0xad0b:
t1_1863 := RAX[32:0];
t2_1864 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_1864));
CF := bool2bv(LT_32((RAX[32:0]), t1_1863));
OF := AND_1((bool2bv((t1_1863[32:31]) == (t2_1864[32:31]))), (XOR_1((t1_1863[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_1863)), t2_1864)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xad0e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0xad12:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xad16:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xad1b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0xad1e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xad22:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xad26:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_618;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xad2b:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xad2e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xad32:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xad36:
origDEST_1871 := RAX[32:0];
origCOUNT_1872 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), CF, LSHIFT_32(origDEST_1871, (MINUS_32(32bv32, origCOUNT_1872)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 1bv32)), origDEST_1871[32:31], unconstrained_619));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1872 == 0bv32)), AF, unconstrained_620);

label_0xad39:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xad3d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xad41:
t_1877 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1877[32:31]) == (1bv32[32:31]))), (XOR_1((t_1877[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1877)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xad43:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xad47:
goto label_0xaa30;

label_0xad4c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xad54:
RAX := LOAD_LE_64(mem, RAX);

label_0xad57:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 36bv64)));

label_0xad5a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 712bv64), RAX[32:0]);

label_0xad61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xad69:
RAX := LOAD_LE_64(mem, RAX);

label_0xad6c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xad70:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 704bv64)));

label_0xad77:
t_1881 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_1881, (RCX[32:0])));
OF := AND_32((XOR_32(t_1881, (RCX[32:0]))), (XOR_32(t_1881, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_1881)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xad79:
RCX := (0bv32 ++ RDX[32:0]);

label_0xad7b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 36bv64)));

label_0xad7e:
t1_1885 := RAX[32:0];
t2_1886 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_1886));
CF := bool2bv(LT_32((RAX[32:0]), t1_1885));
OF := AND_1((bool2bv((t1_1885[32:31]) == (t2_1886[32:31]))), (XOR_1((t1_1885[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_1885)), t2_1886)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xad80:
mem := STORE_LE_32(mem, PLUS_64(RSP, 708bv64), RAX[32:0]);

label_0xad87:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xad8f:
RAX := LOAD_LE_64(mem, RAX);

label_0xad92:
t1_1891 := RAX;
t2_1892 := 36bv64;
RAX := PLUS_64(RAX, t2_1892);
CF := bool2bv(LT_64(RAX, t1_1891));
OF := AND_1((bool2bv((t1_1891[64:63]) == (t2_1892[64:63]))), (XOR_1((t1_1891[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1891)), t2_1892)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xad96:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0xad9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xada6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_621;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xadac:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xadb1:
t_1899 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_622;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1899, 4bv64)), t_1899)), 2bv64)), (XOR_64((RSHIFT_64(t_1899, 4bv64)), t_1899)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1899, 4bv64)), t_1899)), 2bv64)), (XOR_64((RSHIFT_64(t_1899, 4bv64)), t_1899)))))[1:0]));
SF := t_1899[64:63];
ZF := bool2bv(0bv64 == t_1899);

label_0xadb4:
if (bv2bool(ZF)) {
  goto label_0xadb7;
}

label_0xadb6:
assume false;

label_0xadb7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xadbf:
origDEST_1903 := RAX;
origCOUNT_1904 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), CF, LSHIFT_64(origDEST_1903, (MINUS_64(64bv64, origCOUNT_1904)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 1bv64)), origDEST_1903[64:63], unconstrained_623));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1904 == 0bv64)), AF, unconstrained_624);

label_0xadc3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xadca:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xadce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xadd6:
origDEST_1909 := RCX;
origCOUNT_1910 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), CF, LSHIFT_64(origDEST_1909, (MINUS_64(64bv64, origCOUNT_1910)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 1bv64)), origDEST_1909[64:63], unconstrained_625));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), AF, unconstrained_626);

label_0xadda:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_627;
SF := unconstrained_628;
AF := unconstrained_629;
PF := unconstrained_630;

label_0xadde:
if (bv2bool(CF)) {
  goto label_0xade1;
}

label_0xade0:
assume false;

label_0xade1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xade9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 708bv64)));

label_0xadf0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xadf2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xadfa:
RAX := LOAD_LE_64(mem, RAX);

label_0xadfd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 712bv64)));

label_0xae04:
t_1915 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), t_1915)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1915, (LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1915, 4bv32)), t_1915)), 2bv32)), (XOR_32((RSHIFT_32(t_1915, 4bv32)), t_1915)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1915, 4bv32)), t_1915)), 2bv32)), (XOR_32((RSHIFT_32(t_1915, 4bv32)), t_1915)))))[1:0]));
SF := t_1915[32:31];
ZF := bool2bv(0bv32 == t_1915);

label_0xae07:
if (bv2bool(NOT_1(CF))) {
  goto label_0xae8f;
}

label_0xae0d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xae15:
RAX := LOAD_LE_64(mem, RAX);

label_0xae18:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 40bv64)));

label_0xae1b:
t_1919 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1919[32:31]) == (1bv32[32:31]))), (XOR_1((t_1919[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1919)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xae1d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 716bv64), RAX[32:0]);

label_0xae24:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xae2c:
RAX := LOAD_LE_64(mem, RAX);

label_0xae2f:
t1_1923 := RAX;
t2_1924 := 40bv64;
RAX := PLUS_64(RAX, t2_1924);
CF := bool2bv(LT_64(RAX, t1_1923));
OF := AND_1((bool2bv((t1_1923[64:63]) == (t2_1924[64:63]))), (XOR_1((t1_1923[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1923)), t2_1924)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xae33:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RAX);

label_0xae3b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xae43:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_631;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xae49:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xae4e:
t_1931 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_632;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1931, 4bv64)), t_1931)), 2bv64)), (XOR_64((RSHIFT_64(t_1931, 4bv64)), t_1931)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1931, 4bv64)), t_1931)), 2bv64)), (XOR_64((RSHIFT_64(t_1931, 4bv64)), t_1931)))))[1:0]));
SF := t_1931[64:63];
ZF := bool2bv(0bv64 == t_1931);

label_0xae51:
if (bv2bool(ZF)) {
  goto label_0xae54;
}

label_0xae53:
assume false;

label_0xae54:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xae5c:
origDEST_1935 := RAX;
origCOUNT_1936 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), CF, LSHIFT_64(origDEST_1935, (MINUS_64(64bv64, origCOUNT_1936)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 1bv64)), origDEST_1935[64:63], unconstrained_633));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1936 == 0bv64)), AF, unconstrained_634);

label_0xae60:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xae67:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xae6b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xae73:
origDEST_1941 := RCX;
origCOUNT_1942 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), CF, LSHIFT_64(origDEST_1941, (MINUS_64(64bv64, origCOUNT_1942)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 1bv64)), origDEST_1941[64:63], unconstrained_635));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv64)), AF, unconstrained_636);

label_0xae77:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_637;
SF := unconstrained_638;
AF := unconstrained_639;
PF := unconstrained_640;

label_0xae7b:
if (bv2bool(CF)) {
  goto label_0xae7e;
}

label_0xae7d:
assume false;

label_0xae7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xae86:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 716bv64)));

label_0xae8d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xae8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xae97:
t1_1947 := RAX;
t2_1948 := 3184bv64;
RAX := PLUS_64(RAX, t2_1948);
CF := bool2bv(LT_64(RAX, t1_1947));
OF := AND_1((bool2bv((t1_1947[64:63]) == (t2_1948[64:63]))), (XOR_1((t1_1947[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1947)), t2_1948)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xae9d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0xaea5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xaead:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_641;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaeb3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xaeb8:
t_1955 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_642;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1955, 4bv64)), t_1955)), 2bv64)), (XOR_64((RSHIFT_64(t_1955, 4bv64)), t_1955)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1955, 4bv64)), t_1955)), 2bv64)), (XOR_64((RSHIFT_64(t_1955, 4bv64)), t_1955)))))[1:0]));
SF := t_1955[64:63];
ZF := bool2bv(0bv64 == t_1955);

label_0xaebb:
if (bv2bool(ZF)) {
  goto label_0xaebe;
}

label_0xaebd:
assume false;

label_0xaebe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xaec6:
origDEST_1959 := RAX;
origCOUNT_1960 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), CF, LSHIFT_64(origDEST_1959, (MINUS_64(64bv64, origCOUNT_1960)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 1bv64)), origDEST_1959[64:63], unconstrained_643));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1960 == 0bv64)), AF, unconstrained_644);

label_0xaeca:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xaed1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xaed5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xaedd:
origDEST_1965 := RCX;
origCOUNT_1966 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), CF, LSHIFT_64(origDEST_1965, (MINUS_64(64bv64, origCOUNT_1966)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 1bv64)), origDEST_1965[64:63], unconstrained_645));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1966 == 0bv64)), AF, unconstrained_646);

label_0xaee1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_647;
SF := unconstrained_648;
AF := unconstrained_649;
PF := unconstrained_650;

label_0xaee5:
if (bv2bool(CF)) {
  goto label_0xaee8;
}

label_0xaee7:
assume false;

label_0xaee8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xaef0:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0xaef4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xaef6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xaefe:
t1_1971 := RAX;
t2_1972 := 12bv64;
RAX := PLUS_64(RAX, t2_1972);
CF := bool2bv(LT_64(RAX, t1_1971));
OF := AND_1((bool2bv((t1_1971[64:63]) == (t2_1972[64:63]))), (XOR_1((t1_1971[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1971)), t2_1972)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaf02:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0xaf0a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xaf12:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_651;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaf18:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xaf1d:
t_1979 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_652;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)), 2bv64)), (XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)), 2bv64)), (XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)))))[1:0]));
SF := t_1979[64:63];
ZF := bool2bv(0bv64 == t_1979);

label_0xaf20:
if (bv2bool(ZF)) {
  goto label_0xaf23;
}

label_0xaf22:
assume false;

label_0xaf23:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xaf2b:
origDEST_1983 := RAX;
origCOUNT_1984 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), CF, LSHIFT_64(origDEST_1983, (MINUS_64(64bv64, origCOUNT_1984)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 1bv64)), origDEST_1983[64:63], unconstrained_653));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), AF, unconstrained_654);

label_0xaf2f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xaf36:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xaf3a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xaf42:
origDEST_1989 := RCX;
origCOUNT_1990 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), CF, LSHIFT_64(origDEST_1989, (MINUS_64(64bv64, origCOUNT_1990)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 1bv64)), origDEST_1989[64:63], unconstrained_655));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), AF, unconstrained_656);

label_0xaf46:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_657;
SF := unconstrained_658;
AF := unconstrained_659;
PF := unconstrained_660;

label_0xaf4a:
if (bv2bool(CF)) {
  goto label_0xaf4d;
}

label_0xaf4c:
assume false;

label_0xaf4d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xaf55:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0xaf5a:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xaf5c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xaf64:
t1_1995 := RAX;
t2_1996 := 16bv64;
RAX := PLUS_64(RAX, t2_1996);
CF := bool2bv(LT_64(RAX, t1_1995));
OF := AND_1((bool2bv((t1_1995[64:63]) == (t2_1996[64:63]))), (XOR_1((t1_1995[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1995)), t2_1996)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaf68:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0xaf70:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xaf78:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_661;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaf7e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xaf83:
t_2003 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_662;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2003, 4bv64)), t_2003)), 2bv64)), (XOR_64((RSHIFT_64(t_2003, 4bv64)), t_2003)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2003, 4bv64)), t_2003)), 2bv64)), (XOR_64((RSHIFT_64(t_2003, 4bv64)), t_2003)))))[1:0]));
SF := t_2003[64:63];
ZF := bool2bv(0bv64 == t_2003);

label_0xaf86:
if (bv2bool(ZF)) {
  goto label_0xaf89;
}

label_0xaf88:
assume false;

label_0xaf89:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xaf91:
origDEST_2007 := RAX;
origCOUNT_2008 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), CF, LSHIFT_64(origDEST_2007, (MINUS_64(64bv64, origCOUNT_2008)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 1bv64)), origDEST_2007[64:63], unconstrained_663));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2008 == 0bv64)), AF, unconstrained_664);

label_0xaf95:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xaf9c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xafa0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xafa8:
origDEST_2013 := RCX;
origCOUNT_2014 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), CF, LSHIFT_64(origDEST_2013, (MINUS_64(64bv64, origCOUNT_2014)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 1bv64)), origDEST_2013[64:63], unconstrained_665));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2014 == 0bv64)), AF, unconstrained_666);

label_0xafac:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_667;
SF := unconstrained_668;
AF := unconstrained_669;
PF := unconstrained_670;

label_0xafb0:
if (bv2bool(CF)) {
  goto label_0xafb3;
}

label_0xafb2:
assume false;

label_0xafb3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xafbb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64)));

label_0xafbf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xafc1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xafc9:
t1_2019 := RAX;
t2_2020 := 1092bv64;
RAX := PLUS_64(RAX, t2_2020);
CF := bool2bv(LT_64(RAX, t1_2019));
OF := AND_1((bool2bv((t1_2019[64:63]) == (t2_2020[64:63]))), (XOR_1((t1_2019[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2019)), t2_2020)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xafcf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RAX);

label_0xafd7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xafdf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_671;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xafe5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xafea:
t_2027 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_672;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2027, 4bv64)), t_2027)), 2bv64)), (XOR_64((RSHIFT_64(t_2027, 4bv64)), t_2027)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2027, 4bv64)), t_2027)), 2bv64)), (XOR_64((RSHIFT_64(t_2027, 4bv64)), t_2027)))))[1:0]));
SF := t_2027[64:63];
ZF := bool2bv(0bv64 == t_2027);

label_0xafed:
if (bv2bool(ZF)) {
  goto label_0xaff0;
}

label_0xafef:
assume false;

label_0xaff0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xaff8:
origDEST_2031 := RAX;
origCOUNT_2032 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), CF, LSHIFT_64(origDEST_2031, (MINUS_64(64bv64, origCOUNT_2032)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 1bv64)), origDEST_2031[64:63], unconstrained_673));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2032 == 0bv64)), AF, unconstrained_674);

label_0xaffc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb003:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb007:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xb00f:
origDEST_2037 := RCX;
origCOUNT_2038 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), CF, LSHIFT_64(origDEST_2037, (MINUS_64(64bv64, origCOUNT_2038)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 1bv64)), origDEST_2037[64:63], unconstrained_675));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2038 == 0bv64)), AF, unconstrained_676);

label_0xb013:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_677;
SF := unconstrained_678;
AF := unconstrained_679;
PF := unconstrained_680;

label_0xb017:
if (bv2bool(CF)) {
  goto label_0xb01a;
}

label_0xb019:
assume false;

label_0xb01a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xb022:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xb026:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb028:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xb030:
t1_2043 := RAX;
t2_2044 := 64bv64;
RAX := PLUS_64(RAX, t2_2044);
CF := bool2bv(LT_64(RAX, t1_2043));
OF := AND_1((bool2bv((t1_2043[64:63]) == (t2_2044[64:63]))), (XOR_1((t1_2043[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2043)), t2_2044)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb034:
mem := STORE_LE_64(mem, PLUS_64(RSP, 320bv64), RAX);

label_0xb03c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xb044:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_681;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb04a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb04f:
t_2051 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_682;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2051, 4bv64)), t_2051)), 2bv64)), (XOR_64((RSHIFT_64(t_2051, 4bv64)), t_2051)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2051, 4bv64)), t_2051)), 2bv64)), (XOR_64((RSHIFT_64(t_2051, 4bv64)), t_2051)))))[1:0]));
SF := t_2051[64:63];
ZF := bool2bv(0bv64 == t_2051);

label_0xb052:
if (bv2bool(ZF)) {
  goto label_0xb055;
}

label_0xb054:
assume false;

label_0xb055:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xb05d:
origDEST_2055 := RAX;
origCOUNT_2056 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), CF, LSHIFT_64(origDEST_2055, (MINUS_64(64bv64, origCOUNT_2056)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 1bv64)), origDEST_2055[64:63], unconstrained_683));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2056 == 0bv64)), AF, unconstrained_684);

label_0xb061:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb068:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb06c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xb074:
origDEST_2061 := RCX;
origCOUNT_2062 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), CF, LSHIFT_64(origDEST_2061, (MINUS_64(64bv64, origCOUNT_2062)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 1bv64)), origDEST_2061[64:63], unconstrained_685));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2062 == 0bv64)), AF, unconstrained_686);

label_0xb078:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_687;
SF := unconstrained_688;
AF := unconstrained_689;
PF := unconstrained_690;

label_0xb07c:
if (bv2bool(CF)) {
  goto label_0xb07f;
}

label_0xb07e:
assume false;

label_0xb07f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xb087:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0xb08b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb08d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xb095:
t1_2067 := RAX;
t2_2068 := 3152bv64;
RAX := PLUS_64(RAX, t2_2068);
CF := bool2bv(LT_64(RAX, t1_2067));
OF := AND_1((bool2bv((t1_2067[64:63]) == (t2_2068[64:63]))), (XOR_1((t1_2067[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2067)), t2_2068)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb09b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 328bv64), RAX);

label_0xb0a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xb0ab:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_691;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb0b1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb0b6:
t_2075 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_692;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2075, 4bv64)), t_2075)), 2bv64)), (XOR_64((RSHIFT_64(t_2075, 4bv64)), t_2075)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2075, 4bv64)), t_2075)), 2bv64)), (XOR_64((RSHIFT_64(t_2075, 4bv64)), t_2075)))))[1:0]));
SF := t_2075[64:63];
ZF := bool2bv(0bv64 == t_2075);

label_0xb0b9:
if (bv2bool(ZF)) {
  goto label_0xb0bc;
}

label_0xb0bb:
assume false;

label_0xb0bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xb0c4:
origDEST_2079 := RAX;
origCOUNT_2080 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), CF, LSHIFT_64(origDEST_2079, (MINUS_64(64bv64, origCOUNT_2080)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 1bv64)), origDEST_2079[64:63], unconstrained_693));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2080 == 0bv64)), AF, unconstrained_694);

label_0xb0c8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb0cf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb0d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xb0db:
origDEST_2085 := RCX;
origCOUNT_2086 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), CF, LSHIFT_64(origDEST_2085, (MINUS_64(64bv64, origCOUNT_2086)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 1bv64)), origDEST_2085[64:63], unconstrained_695));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2086 == 0bv64)), AF, unconstrained_696);

label_0xb0df:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_697;
SF := unconstrained_698;
AF := unconstrained_699;
PF := unconstrained_700;

label_0xb0e3:
if (bv2bool(CF)) {
  goto label_0xb0e6;
}

label_0xb0e5:
assume false;

label_0xb0e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xb0ee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xb0f3:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xb0f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xb0fe:
t1_2091 := RAX;
t2_2092 := 60bv64;
RAX := PLUS_64(RAX, t2_2092);
CF := bool2bv(LT_64(RAX, t1_2091));
OF := AND_1((bool2bv((t1_2091[64:63]) == (t2_2092[64:63]))), (XOR_1((t1_2091[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2091)), t2_2092)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb102:
mem := STORE_LE_64(mem, PLUS_64(RSP, 456bv64), RAX);

label_0xb10a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xb112:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_701;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb118:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb11d:
t_2099 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_702;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2099, 4bv64)), t_2099)), 2bv64)), (XOR_64((RSHIFT_64(t_2099, 4bv64)), t_2099)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2099, 4bv64)), t_2099)), 2bv64)), (XOR_64((RSHIFT_64(t_2099, 4bv64)), t_2099)))))[1:0]));
SF := t_2099[64:63];
ZF := bool2bv(0bv64 == t_2099);

label_0xb120:
if (bv2bool(ZF)) {
  goto label_0xb123;
}

label_0xb122:
assume false;

label_0xb123:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xb12b:
origDEST_2103 := RAX;
origCOUNT_2104 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), CF, LSHIFT_64(origDEST_2103, (MINUS_64(64bv64, origCOUNT_2104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 1bv64)), origDEST_2103[64:63], unconstrained_703));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2104 == 0bv64)), AF, unconstrained_704);

label_0xb12f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb136:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb13a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xb142:
origDEST_2109 := RCX;
origCOUNT_2110 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), CF, LSHIFT_64(origDEST_2109, (MINUS_64(64bv64, origCOUNT_2110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 1bv64)), origDEST_2109[64:63], unconstrained_705));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2110 == 0bv64)), AF, unconstrained_706);

label_0xb146:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_707;
SF := unconstrained_708;
AF := unconstrained_709;
PF := unconstrained_710;

label_0xb14a:
if (bv2bool(CF)) {
  goto label_0xb14d;
}

label_0xb14c:
assume false;

label_0xb14d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xb155:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xb159:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb15b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xb163:
RAX := LOAD_LE_64(mem, RAX);

label_0xb166:
t1_2115 := RAX;
t2_2116 := 24bv64;
RAX := PLUS_64(RAX, t2_2116);
CF := bool2bv(LT_64(RAX, t1_2115));
OF := AND_1((bool2bv((t1_2115[64:63]) == (t2_2116[64:63]))), (XOR_1((t1_2115[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2115)), t2_2116)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb16a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RAX);

label_0xb172:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xb17a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_711;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb180:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb185:
t_2123 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_712;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2123, 4bv64)), t_2123)), 2bv64)), (XOR_64((RSHIFT_64(t_2123, 4bv64)), t_2123)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2123, 4bv64)), t_2123)), 2bv64)), (XOR_64((RSHIFT_64(t_2123, 4bv64)), t_2123)))))[1:0]));
SF := t_2123[64:63];
ZF := bool2bv(0bv64 == t_2123);

label_0xb188:
if (bv2bool(ZF)) {
  goto label_0xb18b;
}

label_0xb18a:
assume false;

label_0xb18b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xb193:
origDEST_2127 := RAX;
origCOUNT_2128 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), CF, LSHIFT_64(origDEST_2127, (MINUS_64(64bv64, origCOUNT_2128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 1bv64)), origDEST_2127[64:63], unconstrained_713));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2128 == 0bv64)), AF, unconstrained_714);

label_0xb197:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb19e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb1a2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xb1aa:
origDEST_2133 := RCX;
origCOUNT_2134 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), CF, LSHIFT_64(origDEST_2133, (MINUS_64(64bv64, origCOUNT_2134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 1bv64)), origDEST_2133[64:63], unconstrained_715));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2134 == 0bv64)), AF, unconstrained_716);

label_0xb1ae:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_717;
SF := unconstrained_718;
AF := unconstrained_719;
PF := unconstrained_720;

label_0xb1b2:
if (bv2bool(CF)) {
  goto label_0xb1b5;
}

label_0xb1b4:
assume false;

label_0xb1b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xb1bd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xb1c2:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xb1c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 848bv64));

label_0xb1cd:
RAX := LOAD_LE_64(mem, RAX);

label_0xb1d0:
t1_2139 := RAX;
t2_2140 := 32bv64;
RAX := PLUS_64(RAX, t2_2140);
CF := bool2bv(LT_64(RAX, t1_2139));
OF := AND_1((bool2bv((t1_2139[64:63]) == (t2_2140[64:63]))), (XOR_1((t1_2139[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2139)), t2_2140)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb1d4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 344bv64), RAX);

label_0xb1dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xb1e4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_721;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb1ea:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb1ef:
t_2147 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_722;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2147, 4bv64)), t_2147)), 2bv64)), (XOR_64((RSHIFT_64(t_2147, 4bv64)), t_2147)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2147, 4bv64)), t_2147)), 2bv64)), (XOR_64((RSHIFT_64(t_2147, 4bv64)), t_2147)))))[1:0]));
SF := t_2147[64:63];
ZF := bool2bv(0bv64 == t_2147);

label_0xb1f2:
if (bv2bool(ZF)) {
  goto label_0xb1f5;
}

label_0xb1f4:
assume false;

label_0xb1f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xb1fd:
origDEST_2151 := RAX;
origCOUNT_2152 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), CF, LSHIFT_64(origDEST_2151, (MINUS_64(64bv64, origCOUNT_2152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 1bv64)), origDEST_2151[64:63], unconstrained_723));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), AF, unconstrained_724);

label_0xb201:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb208:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb20c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xb214:
origDEST_2157 := RCX;
origCOUNT_2158 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), CF, LSHIFT_64(origDEST_2157, (MINUS_64(64bv64, origCOUNT_2158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 1bv64)), origDEST_2157[64:63], unconstrained_725));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), AF, unconstrained_726);

label_0xb218:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_727;
SF := unconstrained_728;
AF := unconstrained_729;
PF := unconstrained_730;

label_0xb21c:
if (bv2bool(CF)) {
  goto label_0xb21f;
}

label_0xb21e:
assume false;

label_0xb21f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xb227:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xb22b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb22d:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_731;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb22f:
t1_2163 := RSP;
t2_2164 := 840bv64;
RSP := PLUS_64(RSP, t2_2164);
CF := bool2bv(LT_64(RSP, t1_2163));
OF := AND_1((bool2bv((t1_2163[64:63]) == (t2_2164[64:63]))), (XOR_1((t1_2163[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_2163)), t2_2164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xb236:

ra_2169 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_1000,origCOUNT_1006,origCOUNT_1028,origCOUNT_1034,origCOUNT_1056,origCOUNT_106,origCOUNT_1062,origCOUNT_1090,origCOUNT_1096,origCOUNT_112,origCOUNT_1126,origCOUNT_1132,origCOUNT_1138,origCOUNT_1162,origCOUNT_1168,origCOUNT_1176,origCOUNT_1194,origCOUNT_1200,origCOUNT_1210,origCOUNT_1234,origCOUNT_1240,origCOUNT_1262,origCOUNT_1268,origCOUNT_1290,origCOUNT_1296,origCOUNT_1318,origCOUNT_1324,origCOUNT_134,origCOUNT_1352,origCOUNT_1358,origCOUNT_1382,origCOUNT_1388,origCOUNT_1394,origCOUNT_140,origCOUNT_1418,origCOUNT_1424,origCOUNT_1444,origCOUNT_1450,origCOUNT_1456,origCOUNT_1474,origCOUNT_1480,origCOUNT_1490,origCOUNT_1514,origCOUNT_1520,origCOUNT_1542,origCOUNT_1548,origCOUNT_1570,origCOUNT_1576,origCOUNT_1598,origCOUNT_1604,origCOUNT_162,origCOUNT_1628,origCOUNT_1634,origCOUNT_1656,origCOUNT_1662,origCOUNT_168,origCOUNT_1698,origCOUNT_1704,origCOUNT_1710,origCOUNT_1716,origCOUNT_1748,origCOUNT_1754,origCOUNT_1760,origCOUNT_1766,origCOUNT_1794,origCOUNT_1814,origCOUNT_1834,origCOUNT_1854,origCOUNT_1872,origCOUNT_190,origCOUNT_1904,origCOUNT_1910,origCOUNT_1936,origCOUNT_1942,origCOUNT_196,origCOUNT_1960,origCOUNT_1966,origCOUNT_1984,origCOUNT_1990,origCOUNT_2008,origCOUNT_2014,origCOUNT_2032,origCOUNT_2038,origCOUNT_2056,origCOUNT_2062,origCOUNT_2080,origCOUNT_2086,origCOUNT_2104,origCOUNT_2110,origCOUNT_2128,origCOUNT_2134,origCOUNT_2152,origCOUNT_2158,origCOUNT_222,origCOUNT_228,origCOUNT_262,origCOUNT_268,origCOUNT_292,origCOUNT_298,origCOUNT_304,origCOUNT_328,origCOUNT_334,origCOUNT_342,origCOUNT_360,origCOUNT_366,origCOUNT_376,origCOUNT_38,origCOUNT_400,origCOUNT_406,origCOUNT_428,origCOUNT_434,origCOUNT_44,origCOUNT_456,origCOUNT_462,origCOUNT_484,origCOUNT_490,origCOUNT_50,origCOUNT_518,origCOUNT_524,origCOUNT_554,origCOUNT_56,origCOUNT_560,origCOUNT_578,origCOUNT_584,origCOUNT_590,origCOUNT_614,origCOUNT_620,origCOUNT_628,origCOUNT_646,origCOUNT_652,origCOUNT_662,origCOUNT_686,origCOUNT_692,origCOUNT_714,origCOUNT_720,origCOUNT_742,origCOUNT_748,origCOUNT_770,origCOUNT_776,origCOUNT_78,origCOUNT_804,origCOUNT_810,origCOUNT_84,origCOUNT_840,origCOUNT_846,origCOUNT_864,origCOUNT_870,origCOUNT_876,origCOUNT_900,origCOUNT_906,origCOUNT_914,origCOUNT_932,origCOUNT_938,origCOUNT_948,origCOUNT_972,origCOUNT_978,origDEST_1005,origDEST_1027,origDEST_1033,origDEST_105,origDEST_1055,origDEST_1061,origDEST_1089,origDEST_1095,origDEST_111,origDEST_1125,origDEST_1131,origDEST_1137,origDEST_1161,origDEST_1167,origDEST_1175,origDEST_1193,origDEST_1199,origDEST_1209,origDEST_1233,origDEST_1239,origDEST_1261,origDEST_1267,origDEST_1289,origDEST_1295,origDEST_1317,origDEST_1323,origDEST_133,origDEST_1351,origDEST_1357,origDEST_1381,origDEST_1387,origDEST_139,origDEST_1393,origDEST_1417,origDEST_1423,origDEST_1443,origDEST_1449,origDEST_1455,origDEST_1473,origDEST_1479,origDEST_1489,origDEST_1513,origDEST_1519,origDEST_1541,origDEST_1547,origDEST_1569,origDEST_1575,origDEST_1597,origDEST_1603,origDEST_161,origDEST_1627,origDEST_1633,origDEST_1655,origDEST_1661,origDEST_167,origDEST_1697,origDEST_1703,origDEST_1709,origDEST_1715,origDEST_1747,origDEST_1753,origDEST_1759,origDEST_1765,origDEST_1793,origDEST_1813,origDEST_1833,origDEST_1853,origDEST_1871,origDEST_189,origDEST_1903,origDEST_1909,origDEST_1935,origDEST_1941,origDEST_195,origDEST_1959,origDEST_1965,origDEST_1983,origDEST_1989,origDEST_2007,origDEST_2013,origDEST_2031,origDEST_2037,origDEST_2055,origDEST_2061,origDEST_2079,origDEST_2085,origDEST_2103,origDEST_2109,origDEST_2127,origDEST_2133,origDEST_2151,origDEST_2157,origDEST_221,origDEST_227,origDEST_261,origDEST_267,origDEST_291,origDEST_297,origDEST_303,origDEST_327,origDEST_333,origDEST_341,origDEST_359,origDEST_365,origDEST_37,origDEST_375,origDEST_399,origDEST_405,origDEST_427,origDEST_43,origDEST_433,origDEST_455,origDEST_461,origDEST_483,origDEST_489,origDEST_49,origDEST_517,origDEST_523,origDEST_55,origDEST_553,origDEST_559,origDEST_577,origDEST_583,origDEST_589,origDEST_613,origDEST_619,origDEST_627,origDEST_645,origDEST_651,origDEST_661,origDEST_685,origDEST_691,origDEST_713,origDEST_719,origDEST_741,origDEST_747,origDEST_769,origDEST_77,origDEST_775,origDEST_803,origDEST_809,origDEST_83,origDEST_839,origDEST_845,origDEST_863,origDEST_869,origDEST_875,origDEST_899,origDEST_905,origDEST_913,origDEST_931,origDEST_937,origDEST_947,origDEST_971,origDEST_977,origDEST_999,ra_2169,t1_1015,t1_1043,t1_1077,t1_1113,t1_1143,t1_1149,t1_1181,t1_121,t1_1215,t1_1221,t1_1249,t1_1277,t1_1305,t1_1339,t1_1363,t1_1369,t1_1399,t1_1405,t1_1431,t1_1461,t1_149,t1_1495,t1_1501,t1_1529,t1_1557,t1_1585,t1_1615,t1_1643,t1_177,t1_1863,t1_1885,t1_1891,t1_1923,t1_1947,t1_1971,t1_1995,t1_2019,t1_2043,t1_2067,t1_209,t1_2091,t1_2115,t1_2139,t1_2163,t1_249,t1_25,t1_273,t1_279,t1_309,t1_315,t1_347,t1_381,t1_387,t1_415,t1_443,t1_471,t1_505,t1_541,t1_565,t1_595,t1_601,t1_633,t1_65,t1_667,t1_673,t1_701,t1_729,t1_757,t1_791,t1_827,t1_851,t1_881,t1_887,t1_919,t1_93,t1_953,t1_959,t1_987,t2_1016,t2_1044,t2_1078,t2_1114,t2_1144,t2_1150,t2_1182,t2_1216,t2_122,t2_1222,t2_1250,t2_1278,t2_1306,t2_1340,t2_1364,t2_1370,t2_1400,t2_1406,t2_1432,t2_1462,t2_1496,t2_150,t2_1502,t2_1530,t2_1558,t2_1586,t2_1616,t2_1644,t2_178,t2_1864,t2_1886,t2_1892,t2_1924,t2_1948,t2_1972,t2_1996,t2_2020,t2_2044,t2_2068,t2_2092,t2_210,t2_2116,t2_2140,t2_2164,t2_250,t2_26,t2_274,t2_280,t2_310,t2_316,t2_348,t2_382,t2_388,t2_416,t2_444,t2_472,t2_506,t2_542,t2_566,t2_596,t2_602,t2_634,t2_66,t2_668,t2_674,t2_702,t2_730,t2_758,t2_792,t2_828,t2_852,t2_882,t2_888,t2_920,t2_94,t2_954,t2_960,t2_988,t_1,t_101,t_1011,t_1023,t_1039,t_1051,t_1067,t_1073,t_1085,t_1101,t_1105,t_1109,t_1121,t_1157,t_117,t_1189,t_1205,t_1229,t_1245,t_1257,t_1273,t_1285,t_129,t_13,t_1301,t_1313,t_1329,t_1335,t_1347,t_1377,t_1413,t_1439,t_145,t_1469,t_1485,t_1509,t_1525,t_1537,t_1553,t_1565,t_157,t_1581,t_1593,t_1609,t_1623,t_1639,t_1651,t_1667,t_1671,t_1675,t_1679,t_1683,t_1687,t_1693,t_17,t_1725,t_1729,t_173,t_1733,t_1737,t_1743,t_1775,t_1779,t_1783,t_1787,t_1799,t_1803,t_1807,t_1819,t_1823,t_1827,t_1839,t_1843,t_1847,t_185,t_1859,t_1877,t_1881,t_1899,t_1915,t_1919,t_1931,t_1955,t_1979,t_2003,t_201,t_2027,t_205,t_2051,t_2075,t_2099,t_21,t_2123,t_2147,t_217,t_233,t_237,t_241,t_245,t_257,t_287,t_323,t_33,t_355,t_371,t_395,t_411,t_423,t_439,t_451,t_467,t_479,t_495,t_5,t_501,t_513,t_529,t_533,t_537,t_549,t_573,t_609,t_641,t_657,t_681,t_697,t_709,t_725,t_73,t_737,t_753,t_765,t_781,t_787,t_799,t_815,t_819,t_823,t_835,t_859,t_89,t_895,t_9,t_927,t_943,t_967,t_983,t_995;

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
const unconstrained_265: bv1;
const unconstrained_266: bv1;
const unconstrained_267: bv1;
const unconstrained_268: bv1;
const unconstrained_269: bv1;
const unconstrained_27: bv1;
const unconstrained_270: bv1;
const unconstrained_271: bv1;
const unconstrained_272: bv1;
const unconstrained_273: bv1;
const unconstrained_274: bv1;
const unconstrained_275: bv1;
const unconstrained_276: bv1;
const unconstrained_277: bv1;
const unconstrained_278: bv1;
const unconstrained_279: bv1;
const unconstrained_28: bv1;
const unconstrained_280: bv1;
const unconstrained_281: bv1;
const unconstrained_282: bv1;
const unconstrained_283: bv1;
const unconstrained_284: bv1;
const unconstrained_285: bv1;
const unconstrained_286: bv1;
const unconstrained_287: bv1;
const unconstrained_288: bv1;
const unconstrained_289: bv1;
const unconstrained_29: bv1;
const unconstrained_290: bv1;
const unconstrained_291: bv1;
const unconstrained_292: bv1;
const unconstrained_293: bv1;
const unconstrained_294: bv1;
const unconstrained_295: bv1;
const unconstrained_296: bv1;
const unconstrained_297: bv1;
const unconstrained_298: bv1;
const unconstrained_299: bv1;
const unconstrained_3: bv1;
const unconstrained_30: bv1;
const unconstrained_300: bv1;
const unconstrained_301: bv1;
const unconstrained_302: bv1;
const unconstrained_303: bv1;
const unconstrained_304: bv1;
const unconstrained_305: bv1;
const unconstrained_306: bv1;
const unconstrained_307: bv1;
const unconstrained_308: bv1;
const unconstrained_309: bv1;
const unconstrained_31: bv1;
const unconstrained_310: bv1;
const unconstrained_311: bv1;
const unconstrained_312: bv1;
const unconstrained_313: bv1;
const unconstrained_314: bv1;
const unconstrained_315: bv1;
const unconstrained_316: bv1;
const unconstrained_317: bv1;
const unconstrained_318: bv1;
const unconstrained_319: bv1;
const unconstrained_32: bv1;
const unconstrained_320: bv1;
const unconstrained_321: bv1;
const unconstrained_322: bv1;
const unconstrained_323: bv1;
const unconstrained_324: bv1;
const unconstrained_325: bv1;
const unconstrained_326: bv1;
const unconstrained_327: bv1;
const unconstrained_328: bv1;
const unconstrained_329: bv1;
const unconstrained_33: bv1;
const unconstrained_330: bv1;
const unconstrained_331: bv1;
const unconstrained_332: bv1;
const unconstrained_333: bv1;
const unconstrained_334: bv1;
const unconstrained_335: bv1;
const unconstrained_336: bv1;
const unconstrained_337: bv1;
const unconstrained_338: bv1;
const unconstrained_339: bv1;
const unconstrained_34: bv1;
const unconstrained_340: bv1;
const unconstrained_341: bv1;
const unconstrained_342: bv1;
const unconstrained_343: bv1;
const unconstrained_344: bv1;
const unconstrained_345: bv1;
const unconstrained_346: bv1;
const unconstrained_347: bv1;
const unconstrained_348: bv1;
const unconstrained_349: bv1;
const unconstrained_35: bv1;
const unconstrained_350: bv1;
const unconstrained_351: bv1;
const unconstrained_352: bv1;
const unconstrained_353: bv1;
const unconstrained_354: bv1;
const unconstrained_355: bv1;
const unconstrained_356: bv1;
const unconstrained_357: bv1;
const unconstrained_358: bv1;
const unconstrained_359: bv1;
const unconstrained_36: bv1;
const unconstrained_360: bv1;
const unconstrained_361: bv1;
const unconstrained_362: bv1;
const unconstrained_363: bv1;
const unconstrained_364: bv1;
const unconstrained_365: bv1;
const unconstrained_366: bv1;
const unconstrained_367: bv1;
const unconstrained_368: bv1;
const unconstrained_369: bv1;
const unconstrained_37: bv1;
const unconstrained_370: bv1;
const unconstrained_371: bv1;
const unconstrained_372: bv1;
const unconstrained_373: bv1;
const unconstrained_374: bv1;
const unconstrained_375: bv1;
const unconstrained_376: bv1;
const unconstrained_377: bv1;
const unconstrained_378: bv1;
const unconstrained_379: bv1;
const unconstrained_38: bv1;
const unconstrained_380: bv1;
const unconstrained_381: bv1;
const unconstrained_382: bv1;
const unconstrained_383: bv1;
const unconstrained_384: bv1;
const unconstrained_385: bv1;
const unconstrained_386: bv1;
const unconstrained_387: bv1;
const unconstrained_388: bv1;
const unconstrained_389: bv1;
const unconstrained_39: bv1;
const unconstrained_390: bv1;
const unconstrained_391: bv1;
const unconstrained_392: bv1;
const unconstrained_393: bv1;
const unconstrained_394: bv1;
const unconstrained_395: bv1;
const unconstrained_396: bv1;
const unconstrained_397: bv1;
const unconstrained_398: bv1;
const unconstrained_399: bv1;
const unconstrained_4: bv1;
const unconstrained_40: bv1;
const unconstrained_400: bv1;
const unconstrained_401: bv1;
const unconstrained_402: bv1;
const unconstrained_403: bv1;
const unconstrained_404: bv1;
const unconstrained_405: bv1;
const unconstrained_406: bv1;
const unconstrained_407: bv1;
const unconstrained_408: bv1;
const unconstrained_409: bv1;
const unconstrained_41: bv1;
const unconstrained_410: bv1;
const unconstrained_411: bv1;
const unconstrained_412: bv1;
const unconstrained_413: bv1;
const unconstrained_414: bv1;
const unconstrained_415: bv1;
const unconstrained_416: bv1;
const unconstrained_417: bv1;
const unconstrained_418: bv1;
const unconstrained_419: bv1;
const unconstrained_42: bv1;
const unconstrained_420: bv1;
const unconstrained_421: bv1;
const unconstrained_422: bv1;
const unconstrained_423: bv1;
const unconstrained_424: bv1;
const unconstrained_425: bv1;
const unconstrained_426: bv1;
const unconstrained_427: bv1;
const unconstrained_428: bv1;
const unconstrained_429: bv1;
const unconstrained_43: bv1;
const unconstrained_430: bv1;
const unconstrained_431: bv1;
const unconstrained_432: bv1;
const unconstrained_433: bv1;
const unconstrained_434: bv1;
const unconstrained_435: bv1;
const unconstrained_436: bv1;
const unconstrained_437: bv1;
const unconstrained_438: bv1;
const unconstrained_439: bv1;
const unconstrained_44: bv1;
const unconstrained_440: bv1;
const unconstrained_441: bv1;
const unconstrained_442: bv1;
const unconstrained_443: bv1;
const unconstrained_444: bv1;
const unconstrained_445: bv1;
const unconstrained_446: bv1;
const unconstrained_447: bv1;
const unconstrained_448: bv1;
const unconstrained_449: bv1;
const unconstrained_45: bv1;
const unconstrained_450: bv1;
const unconstrained_451: bv1;
const unconstrained_452: bv1;
const unconstrained_453: bv1;
const unconstrained_454: bv1;
const unconstrained_455: bv1;
const unconstrained_456: bv1;
const unconstrained_457: bv1;
const unconstrained_458: bv1;
const unconstrained_459: bv1;
const unconstrained_46: bv1;
const unconstrained_460: bv1;
const unconstrained_461: bv1;
const unconstrained_462: bv1;
const unconstrained_463: bv1;
const unconstrained_464: bv1;
const unconstrained_465: bv1;
const unconstrained_466: bv1;
const unconstrained_467: bv1;
const unconstrained_468: bv1;
const unconstrained_469: bv1;
const unconstrained_47: bv1;
const unconstrained_470: bv1;
const unconstrained_471: bv1;
const unconstrained_472: bv1;
const unconstrained_473: bv1;
const unconstrained_474: bv1;
const unconstrained_475: bv1;
const unconstrained_476: bv1;
const unconstrained_477: bv1;
const unconstrained_478: bv1;
const unconstrained_479: bv1;
const unconstrained_48: bv1;
const unconstrained_480: bv1;
const unconstrained_481: bv1;
const unconstrained_482: bv1;
const unconstrained_483: bv1;
const unconstrained_484: bv1;
const unconstrained_485: bv1;
const unconstrained_486: bv1;
const unconstrained_487: bv1;
const unconstrained_488: bv1;
const unconstrained_489: bv1;
const unconstrained_49: bv1;
const unconstrained_490: bv1;
const unconstrained_491: bv1;
const unconstrained_492: bv1;
const unconstrained_493: bv1;
const unconstrained_494: bv1;
const unconstrained_495: bv1;
const unconstrained_496: bv1;
const unconstrained_497: bv1;
const unconstrained_498: bv1;
const unconstrained_499: bv1;
const unconstrained_5: bv1;
const unconstrained_50: bv1;
const unconstrained_500: bv1;
const unconstrained_501: bv1;
const unconstrained_502: bv1;
const unconstrained_503: bv1;
const unconstrained_504: bv1;
const unconstrained_505: bv1;
const unconstrained_506: bv1;
const unconstrained_507: bv1;
const unconstrained_508: bv1;
const unconstrained_509: bv1;
const unconstrained_51: bv1;
const unconstrained_510: bv1;
const unconstrained_511: bv1;
const unconstrained_512: bv1;
const unconstrained_513: bv1;
const unconstrained_514: bv1;
const unconstrained_515: bv1;
const unconstrained_516: bv1;
const unconstrained_517: bv1;
const unconstrained_518: bv1;
const unconstrained_519: bv1;
const unconstrained_52: bv1;
const unconstrained_520: bv1;
const unconstrained_521: bv1;
const unconstrained_522: bv1;
const unconstrained_523: bv1;
const unconstrained_524: bv1;
const unconstrained_525: bv1;
const unconstrained_526: bv1;
const unconstrained_527: bv1;
const unconstrained_528: bv1;
const unconstrained_529: bv1;
const unconstrained_53: bv1;
const unconstrained_530: bv1;
const unconstrained_531: bv1;
const unconstrained_532: bv1;
const unconstrained_533: bv1;
const unconstrained_534: bv1;
const unconstrained_535: bv1;
const unconstrained_536: bv1;
const unconstrained_537: bv1;
const unconstrained_538: bv1;
const unconstrained_539: bv1;
const unconstrained_54: bv1;
const unconstrained_540: bv1;
const unconstrained_541: bv1;
const unconstrained_542: bv1;
const unconstrained_543: bv1;
const unconstrained_544: bv1;
const unconstrained_545: bv1;
const unconstrained_546: bv1;
const unconstrained_547: bv1;
const unconstrained_548: bv1;
const unconstrained_549: bv1;
const unconstrained_55: bv1;
const unconstrained_550: bv1;
const unconstrained_551: bv1;
const unconstrained_552: bv1;
const unconstrained_553: bv1;
const unconstrained_554: bv1;
const unconstrained_555: bv1;
const unconstrained_556: bv1;
const unconstrained_557: bv1;
const unconstrained_558: bv1;
const unconstrained_559: bv1;
const unconstrained_56: bv1;
const unconstrained_560: bv1;
const unconstrained_561: bv1;
const unconstrained_562: bv1;
const unconstrained_563: bv1;
const unconstrained_564: bv1;
const unconstrained_565: bv1;
const unconstrained_566: bv1;
const unconstrained_567: bv1;
const unconstrained_568: bv1;
const unconstrained_569: bv1;
const unconstrained_57: bv1;
const unconstrained_570: bv1;
const unconstrained_571: bv1;
const unconstrained_572: bv1;
const unconstrained_573: bv1;
const unconstrained_574: bv1;
const unconstrained_575: bv1;
const unconstrained_576: bv1;
const unconstrained_577: bv1;
const unconstrained_578: bv1;
const unconstrained_579: bv1;
const unconstrained_58: bv1;
const unconstrained_580: bv1;
const unconstrained_581: bv1;
const unconstrained_582: bv1;
const unconstrained_583: bv1;
const unconstrained_584: bv1;
const unconstrained_585: bv1;
const unconstrained_586: bv1;
const unconstrained_587: bv1;
const unconstrained_588: bv1;
const unconstrained_589: bv1;
const unconstrained_59: bv1;
const unconstrained_590: bv1;
const unconstrained_591: bv1;
const unconstrained_592: bv1;
const unconstrained_593: bv1;
const unconstrained_594: bv1;
const unconstrained_595: bv1;
const unconstrained_596: bv1;
const unconstrained_597: bv1;
const unconstrained_598: bv1;
const unconstrained_599: bv1;
const unconstrained_6: bv1;
const unconstrained_60: bv1;
const unconstrained_600: bv1;
const unconstrained_601: bv1;
const unconstrained_602: bv1;
const unconstrained_603: bv1;
const unconstrained_604: bv1;
const unconstrained_605: bv1;
const unconstrained_606: bv1;
const unconstrained_607: bv1;
const unconstrained_608: bv1;
const unconstrained_609: bv1;
const unconstrained_61: bv1;
const unconstrained_610: bv1;
const unconstrained_611: bv1;
const unconstrained_612: bv1;
const unconstrained_613: bv1;
const unconstrained_614: bv1;
const unconstrained_615: bv1;
const unconstrained_616: bv1;
const unconstrained_617: bv1;
const unconstrained_618: bv1;
const unconstrained_619: bv1;
const unconstrained_62: bv1;
const unconstrained_620: bv1;
const unconstrained_621: bv1;
const unconstrained_622: bv1;
const unconstrained_623: bv1;
const unconstrained_624: bv1;
const unconstrained_625: bv1;
const unconstrained_626: bv1;
const unconstrained_627: bv1;
const unconstrained_628: bv1;
const unconstrained_629: bv1;
const unconstrained_63: bv1;
const unconstrained_630: bv1;
const unconstrained_631: bv1;
const unconstrained_632: bv1;
const unconstrained_633: bv1;
const unconstrained_634: bv1;
const unconstrained_635: bv1;
const unconstrained_636: bv1;
const unconstrained_637: bv1;
const unconstrained_638: bv1;
const unconstrained_639: bv1;
const unconstrained_64: bv1;
const unconstrained_640: bv1;
const unconstrained_641: bv1;
const unconstrained_642: bv1;
const unconstrained_643: bv1;
const unconstrained_644: bv1;
const unconstrained_645: bv1;
const unconstrained_646: bv1;
const unconstrained_647: bv1;
const unconstrained_648: bv1;
const unconstrained_649: bv1;
const unconstrained_65: bv1;
const unconstrained_650: bv1;
const unconstrained_651: bv1;
const unconstrained_652: bv1;
const unconstrained_653: bv1;
const unconstrained_654: bv1;
const unconstrained_655: bv1;
const unconstrained_656: bv1;
const unconstrained_657: bv1;
const unconstrained_658: bv1;
const unconstrained_659: bv1;
const unconstrained_66: bv1;
const unconstrained_660: bv1;
const unconstrained_661: bv1;
const unconstrained_662: bv1;
const unconstrained_663: bv1;
const unconstrained_664: bv1;
const unconstrained_665: bv1;
const unconstrained_666: bv1;
const unconstrained_667: bv1;
const unconstrained_668: bv1;
const unconstrained_669: bv1;
const unconstrained_67: bv1;
const unconstrained_670: bv1;
const unconstrained_671: bv1;
const unconstrained_672: bv1;
const unconstrained_673: bv1;
const unconstrained_674: bv1;
const unconstrained_675: bv1;
const unconstrained_676: bv1;
const unconstrained_677: bv1;
const unconstrained_678: bv1;
const unconstrained_679: bv1;
const unconstrained_68: bv1;
const unconstrained_680: bv1;
const unconstrained_681: bv1;
const unconstrained_682: bv1;
const unconstrained_683: bv1;
const unconstrained_684: bv1;
const unconstrained_685: bv1;
const unconstrained_686: bv1;
const unconstrained_687: bv1;
const unconstrained_688: bv1;
const unconstrained_689: bv1;
const unconstrained_69: bv1;
const unconstrained_690: bv1;
const unconstrained_691: bv1;
const unconstrained_692: bv1;
const unconstrained_693: bv1;
const unconstrained_694: bv1;
const unconstrained_695: bv1;
const unconstrained_696: bv1;
const unconstrained_697: bv1;
const unconstrained_698: bv1;
const unconstrained_699: bv1;
const unconstrained_7: bv1;
const unconstrained_70: bv1;
const unconstrained_700: bv1;
const unconstrained_701: bv1;
const unconstrained_702: bv1;
const unconstrained_703: bv1;
const unconstrained_704: bv1;
const unconstrained_705: bv1;
const unconstrained_706: bv1;
const unconstrained_707: bv1;
const unconstrained_708: bv1;
const unconstrained_709: bv1;
const unconstrained_71: bv1;
const unconstrained_710: bv1;
const unconstrained_711: bv1;
const unconstrained_712: bv1;
const unconstrained_713: bv1;
const unconstrained_714: bv1;
const unconstrained_715: bv1;
const unconstrained_716: bv1;
const unconstrained_717: bv1;
const unconstrained_718: bv1;
const unconstrained_719: bv1;
const unconstrained_72: bv1;
const unconstrained_720: bv1;
const unconstrained_721: bv1;
const unconstrained_722: bv1;
const unconstrained_723: bv1;
const unconstrained_724: bv1;
const unconstrained_725: bv1;
const unconstrained_726: bv1;
const unconstrained_727: bv1;
const unconstrained_728: bv1;
const unconstrained_729: bv1;
const unconstrained_73: bv1;
const unconstrained_730: bv1;
const unconstrained_731: bv1;
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
var origCOUNT_1000: bv64;
var origCOUNT_1006: bv64;
var origCOUNT_1028: bv64;
var origCOUNT_1034: bv64;
var origCOUNT_1056: bv64;
var origCOUNT_106: bv64;
var origCOUNT_1062: bv64;
var origCOUNT_1090: bv64;
var origCOUNT_1096: bv64;
var origCOUNT_112: bv64;
var origCOUNT_1126: bv64;
var origCOUNT_1132: bv64;
var origCOUNT_1138: bv64;
var origCOUNT_1162: bv64;
var origCOUNT_1168: bv64;
var origCOUNT_1176: bv32;
var origCOUNT_1194: bv64;
var origCOUNT_1200: bv64;
var origCOUNT_1210: bv64;
var origCOUNT_1234: bv64;
var origCOUNT_1240: bv64;
var origCOUNT_1262: bv64;
var origCOUNT_1268: bv64;
var origCOUNT_1290: bv64;
var origCOUNT_1296: bv64;
var origCOUNT_1318: bv64;
var origCOUNT_1324: bv64;
var origCOUNT_134: bv64;
var origCOUNT_1352: bv64;
var origCOUNT_1358: bv64;
var origCOUNT_1382: bv64;
var origCOUNT_1388: bv64;
var origCOUNT_1394: bv64;
var origCOUNT_140: bv64;
var origCOUNT_1418: bv64;
var origCOUNT_1424: bv64;
var origCOUNT_1444: bv64;
var origCOUNT_1450: bv64;
var origCOUNT_1456: bv32;
var origCOUNT_1474: bv64;
var origCOUNT_1480: bv64;
var origCOUNT_1490: bv64;
var origCOUNT_1514: bv64;
var origCOUNT_1520: bv64;
var origCOUNT_1542: bv64;
var origCOUNT_1548: bv64;
var origCOUNT_1570: bv64;
var origCOUNT_1576: bv64;
var origCOUNT_1598: bv64;
var origCOUNT_1604: bv64;
var origCOUNT_162: bv64;
var origCOUNT_1628: bv64;
var origCOUNT_1634: bv64;
var origCOUNT_1656: bv64;
var origCOUNT_1662: bv64;
var origCOUNT_168: bv64;
var origCOUNT_1698: bv64;
var origCOUNT_1704: bv64;
var origCOUNT_1710: bv32;
var origCOUNT_1716: bv32;
var origCOUNT_1748: bv64;
var origCOUNT_1754: bv64;
var origCOUNT_1760: bv32;
var origCOUNT_1766: bv32;
var origCOUNT_1794: bv32;
var origCOUNT_1814: bv32;
var origCOUNT_1834: bv32;
var origCOUNT_1854: bv32;
var origCOUNT_1872: bv32;
var origCOUNT_190: bv64;
var origCOUNT_1904: bv64;
var origCOUNT_1910: bv64;
var origCOUNT_1936: bv64;
var origCOUNT_1942: bv64;
var origCOUNT_196: bv64;
var origCOUNT_1960: bv64;
var origCOUNT_1966: bv64;
var origCOUNT_1984: bv64;
var origCOUNT_1990: bv64;
var origCOUNT_2008: bv64;
var origCOUNT_2014: bv64;
var origCOUNT_2032: bv64;
var origCOUNT_2038: bv64;
var origCOUNT_2056: bv64;
var origCOUNT_2062: bv64;
var origCOUNT_2080: bv64;
var origCOUNT_2086: bv64;
var origCOUNT_2104: bv64;
var origCOUNT_2110: bv64;
var origCOUNT_2128: bv64;
var origCOUNT_2134: bv64;
var origCOUNT_2152: bv64;
var origCOUNT_2158: bv64;
var origCOUNT_222: bv64;
var origCOUNT_228: bv64;
var origCOUNT_262: bv64;
var origCOUNT_268: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_304: bv64;
var origCOUNT_328: bv64;
var origCOUNT_334: bv64;
var origCOUNT_342: bv32;
var origCOUNT_360: bv64;
var origCOUNT_366: bv64;
var origCOUNT_376: bv64;
var origCOUNT_38: bv64;
var origCOUNT_400: bv64;
var origCOUNT_406: bv64;
var origCOUNT_428: bv64;
var origCOUNT_434: bv64;
var origCOUNT_44: bv64;
var origCOUNT_456: bv64;
var origCOUNT_462: bv64;
var origCOUNT_484: bv64;
var origCOUNT_490: bv64;
var origCOUNT_50: bv32;
var origCOUNT_518: bv64;
var origCOUNT_524: bv64;
var origCOUNT_554: bv64;
var origCOUNT_56: bv32;
var origCOUNT_560: bv64;
var origCOUNT_578: bv64;
var origCOUNT_584: bv64;
var origCOUNT_590: bv64;
var origCOUNT_614: bv64;
var origCOUNT_620: bv64;
var origCOUNT_628: bv32;
var origCOUNT_646: bv64;
var origCOUNT_652: bv64;
var origCOUNT_662: bv64;
var origCOUNT_686: bv64;
var origCOUNT_692: bv64;
var origCOUNT_714: bv64;
var origCOUNT_720: bv64;
var origCOUNT_742: bv64;
var origCOUNT_748: bv64;
var origCOUNT_770: bv64;
var origCOUNT_776: bv64;
var origCOUNT_78: bv64;
var origCOUNT_804: bv64;
var origCOUNT_810: bv64;
var origCOUNT_84: bv64;
var origCOUNT_840: bv64;
var origCOUNT_846: bv64;
var origCOUNT_864: bv64;
var origCOUNT_870: bv64;
var origCOUNT_876: bv64;
var origCOUNT_900: bv64;
var origCOUNT_906: bv64;
var origCOUNT_914: bv32;
var origCOUNT_932: bv64;
var origCOUNT_938: bv64;
var origCOUNT_948: bv64;
var origCOUNT_972: bv64;
var origCOUNT_978: bv64;
var origDEST_1005: bv64;
var origDEST_1027: bv64;
var origDEST_1033: bv64;
var origDEST_105: bv64;
var origDEST_1055: bv64;
var origDEST_1061: bv64;
var origDEST_1089: bv64;
var origDEST_1095: bv64;
var origDEST_111: bv64;
var origDEST_1125: bv64;
var origDEST_1131: bv64;
var origDEST_1137: bv64;
var origDEST_1161: bv64;
var origDEST_1167: bv64;
var origDEST_1175: bv32;
var origDEST_1193: bv64;
var origDEST_1199: bv64;
var origDEST_1209: bv64;
var origDEST_1233: bv64;
var origDEST_1239: bv64;
var origDEST_1261: bv64;
var origDEST_1267: bv64;
var origDEST_1289: bv64;
var origDEST_1295: bv64;
var origDEST_1317: bv64;
var origDEST_1323: bv64;
var origDEST_133: bv64;
var origDEST_1351: bv64;
var origDEST_1357: bv64;
var origDEST_1381: bv64;
var origDEST_1387: bv64;
var origDEST_139: bv64;
var origDEST_1393: bv64;
var origDEST_1417: bv64;
var origDEST_1423: bv64;
var origDEST_1443: bv64;
var origDEST_1449: bv64;
var origDEST_1455: bv32;
var origDEST_1473: bv64;
var origDEST_1479: bv64;
var origDEST_1489: bv64;
var origDEST_1513: bv64;
var origDEST_1519: bv64;
var origDEST_1541: bv64;
var origDEST_1547: bv64;
var origDEST_1569: bv64;
var origDEST_1575: bv64;
var origDEST_1597: bv64;
var origDEST_1603: bv64;
var origDEST_161: bv64;
var origDEST_1627: bv64;
var origDEST_1633: bv64;
var origDEST_1655: bv64;
var origDEST_1661: bv64;
var origDEST_167: bv64;
var origDEST_1697: bv64;
var origDEST_1703: bv64;
var origDEST_1709: bv32;
var origDEST_1715: bv32;
var origDEST_1747: bv64;
var origDEST_1753: bv64;
var origDEST_1759: bv32;
var origDEST_1765: bv32;
var origDEST_1793: bv32;
var origDEST_1813: bv32;
var origDEST_1833: bv32;
var origDEST_1853: bv32;
var origDEST_1871: bv32;
var origDEST_189: bv64;
var origDEST_1903: bv64;
var origDEST_1909: bv64;
var origDEST_1935: bv64;
var origDEST_1941: bv64;
var origDEST_195: bv64;
var origDEST_1959: bv64;
var origDEST_1965: bv64;
var origDEST_1983: bv64;
var origDEST_1989: bv64;
var origDEST_2007: bv64;
var origDEST_2013: bv64;
var origDEST_2031: bv64;
var origDEST_2037: bv64;
var origDEST_2055: bv64;
var origDEST_2061: bv64;
var origDEST_2079: bv64;
var origDEST_2085: bv64;
var origDEST_2103: bv64;
var origDEST_2109: bv64;
var origDEST_2127: bv64;
var origDEST_2133: bv64;
var origDEST_2151: bv64;
var origDEST_2157: bv64;
var origDEST_221: bv64;
var origDEST_227: bv64;
var origDEST_261: bv64;
var origDEST_267: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_303: bv64;
var origDEST_327: bv64;
var origDEST_333: bv64;
var origDEST_341: bv32;
var origDEST_359: bv64;
var origDEST_365: bv64;
var origDEST_37: bv64;
var origDEST_375: bv64;
var origDEST_399: bv64;
var origDEST_405: bv64;
var origDEST_427: bv64;
var origDEST_43: bv64;
var origDEST_433: bv64;
var origDEST_455: bv64;
var origDEST_461: bv64;
var origDEST_483: bv64;
var origDEST_489: bv64;
var origDEST_49: bv32;
var origDEST_517: bv64;
var origDEST_523: bv64;
var origDEST_55: bv32;
var origDEST_553: bv64;
var origDEST_559: bv64;
var origDEST_577: bv64;
var origDEST_583: bv64;
var origDEST_589: bv64;
var origDEST_613: bv64;
var origDEST_619: bv64;
var origDEST_627: bv32;
var origDEST_645: bv64;
var origDEST_651: bv64;
var origDEST_661: bv64;
var origDEST_685: bv64;
var origDEST_691: bv64;
var origDEST_713: bv64;
var origDEST_719: bv64;
var origDEST_741: bv64;
var origDEST_747: bv64;
var origDEST_769: bv64;
var origDEST_77: bv64;
var origDEST_775: bv64;
var origDEST_803: bv64;
var origDEST_809: bv64;
var origDEST_83: bv64;
var origDEST_839: bv64;
var origDEST_845: bv64;
var origDEST_863: bv64;
var origDEST_869: bv64;
var origDEST_875: bv64;
var origDEST_899: bv64;
var origDEST_905: bv64;
var origDEST_913: bv32;
var origDEST_931: bv64;
var origDEST_937: bv64;
var origDEST_947: bv64;
var origDEST_971: bv64;
var origDEST_977: bv64;
var origDEST_999: bv64;
var ra_2169: bv64;
var t1_1015: bv64;
var t1_1043: bv64;
var t1_1077: bv64;
var t1_1113: bv64;
var t1_1143: bv64;
var t1_1149: bv64;
var t1_1181: bv64;
var t1_121: bv64;
var t1_1215: bv64;
var t1_1221: bv64;
var t1_1249: bv64;
var t1_1277: bv64;
var t1_1305: bv64;
var t1_1339: bv64;
var t1_1363: bv32;
var t1_1369: bv64;
var t1_1399: bv64;
var t1_1405: bv64;
var t1_1431: bv64;
var t1_1461: bv64;
var t1_149: bv64;
var t1_1495: bv64;
var t1_1501: bv64;
var t1_1529: bv64;
var t1_1557: bv64;
var t1_1585: bv64;
var t1_1615: bv64;
var t1_1643: bv64;
var t1_177: bv64;
var t1_1863: bv32;
var t1_1885: bv32;
var t1_1891: bv64;
var t1_1923: bv64;
var t1_1947: bv64;
var t1_1971: bv64;
var t1_1995: bv64;
var t1_2019: bv64;
var t1_2043: bv64;
var t1_2067: bv64;
var t1_209: bv64;
var t1_2091: bv64;
var t1_2115: bv64;
var t1_2139: bv64;
var t1_2163: bv64;
var t1_249: bv64;
var t1_25: bv64;
var t1_273: bv64;
var t1_279: bv64;
var t1_309: bv64;
var t1_315: bv64;
var t1_347: bv64;
var t1_381: bv64;
var t1_387: bv64;
var t1_415: bv64;
var t1_443: bv64;
var t1_471: bv64;
var t1_505: bv64;
var t1_541: bv64;
var t1_565: bv64;
var t1_595: bv64;
var t1_601: bv64;
var t1_633: bv64;
var t1_65: bv64;
var t1_667: bv64;
var t1_673: bv64;
var t1_701: bv64;
var t1_729: bv64;
var t1_757: bv64;
var t1_791: bv64;
var t1_827: bv64;
var t1_851: bv64;
var t1_881: bv64;
var t1_887: bv64;
var t1_919: bv64;
var t1_93: bv64;
var t1_953: bv64;
var t1_959: bv64;
var t1_987: bv64;
var t2_1016: bv64;
var t2_1044: bv64;
var t2_1078: bv64;
var t2_1114: bv64;
var t2_1144: bv64;
var t2_1150: bv64;
var t2_1182: bv64;
var t2_1216: bv64;
var t2_122: bv64;
var t2_1222: bv64;
var t2_1250: bv64;
var t2_1278: bv64;
var t2_1306: bv64;
var t2_1340: bv64;
var t2_1364: bv32;
var t2_1370: bv64;
var t2_1400: bv64;
var t2_1406: bv64;
var t2_1432: bv64;
var t2_1462: bv64;
var t2_1496: bv64;
var t2_150: bv64;
var t2_1502: bv64;
var t2_1530: bv64;
var t2_1558: bv64;
var t2_1586: bv64;
var t2_1616: bv64;
var t2_1644: bv64;
var t2_178: bv64;
var t2_1864: bv32;
var t2_1886: bv32;
var t2_1892: bv64;
var t2_1924: bv64;
var t2_1948: bv64;
var t2_1972: bv64;
var t2_1996: bv64;
var t2_2020: bv64;
var t2_2044: bv64;
var t2_2068: bv64;
var t2_2092: bv64;
var t2_210: bv64;
var t2_2116: bv64;
var t2_2140: bv64;
var t2_2164: bv64;
var t2_250: bv64;
var t2_26: bv64;
var t2_274: bv64;
var t2_280: bv64;
var t2_310: bv64;
var t2_316: bv64;
var t2_348: bv64;
var t2_382: bv64;
var t2_388: bv64;
var t2_416: bv64;
var t2_444: bv64;
var t2_472: bv64;
var t2_506: bv64;
var t2_542: bv64;
var t2_566: bv64;
var t2_596: bv64;
var t2_602: bv64;
var t2_634: bv64;
var t2_66: bv64;
var t2_668: bv64;
var t2_674: bv64;
var t2_702: bv64;
var t2_730: bv64;
var t2_758: bv64;
var t2_792: bv64;
var t2_828: bv64;
var t2_852: bv64;
var t2_882: bv64;
var t2_888: bv64;
var t2_920: bv64;
var t2_94: bv64;
var t2_954: bv64;
var t2_960: bv64;
var t2_988: bv64;
var t_1: bv64;
var t_101: bv64;
var t_1011: bv32;
var t_1023: bv64;
var t_1039: bv32;
var t_1051: bv64;
var t_1067: bv32;
var t_1073: bv32;
var t_1085: bv64;
var t_1101: bv32;
var t_1105: bv32;
var t_1109: bv32;
var t_1121: bv64;
var t_1157: bv64;
var t_117: bv64;
var t_1189: bv64;
var t_1205: bv32;
var t_1229: bv64;
var t_1245: bv32;
var t_1257: bv64;
var t_1273: bv32;
var t_1285: bv64;
var t_129: bv64;
var t_13: bv32;
var t_1301: bv32;
var t_1313: bv64;
var t_1329: bv32;
var t_1335: bv32;
var t_1347: bv64;
var t_1377: bv64;
var t_1413: bv64;
var t_1439: bv64;
var t_145: bv32;
var t_1469: bv64;
var t_1485: bv32;
var t_1509: bv64;
var t_1525: bv32;
var t_1537: bv64;
var t_1553: bv32;
var t_1565: bv64;
var t_157: bv64;
var t_1581: bv32;
var t_1593: bv64;
var t_1609: bv32;
var t_1623: bv64;
var t_1639: bv32;
var t_1651: bv64;
var t_1667: bv32;
var t_1671: bv32;
var t_1675: bv32;
var t_1679: bv32;
var t_1683: bv32;
var t_1687: bv32;
var t_1693: bv64;
var t_17: bv32;
var t_1725: bv32;
var t_1729: bv64;
var t_173: bv32;
var t_1733: bv32;
var t_1737: bv32;
var t_1743: bv64;
var t_1775: bv64;
var t_1779: bv32;
var t_1783: bv32;
var t_1787: bv32;
var t_1799: bv32;
var t_1803: bv32;
var t_1807: bv32;
var t_1819: bv32;
var t_1823: bv32;
var t_1827: bv32;
var t_1839: bv32;
var t_1843: bv32;
var t_1847: bv32;
var t_185: bv64;
var t_1859: bv32;
var t_1877: bv32;
var t_1881: bv32;
var t_1899: bv64;
var t_1915: bv32;
var t_1919: bv32;
var t_1931: bv64;
var t_1955: bv64;
var t_1979: bv64;
var t_2003: bv64;
var t_201: bv32;
var t_2027: bv64;
var t_205: bv32;
var t_2051: bv64;
var t_2075: bv64;
var t_2099: bv64;
var t_21: bv32;
var t_2123: bv64;
var t_2147: bv64;
var t_217: bv64;
var t_233: bv32;
var t_237: bv32;
var t_241: bv32;
var t_245: bv32;
var t_257: bv64;
var t_287: bv64;
var t_323: bv64;
var t_33: bv64;
var t_355: bv64;
var t_371: bv32;
var t_395: bv64;
var t_411: bv32;
var t_423: bv64;
var t_439: bv32;
var t_451: bv64;
var t_467: bv32;
var t_479: bv64;
var t_495: bv32;
var t_5: bv32;
var t_501: bv32;
var t_513: bv64;
var t_529: bv32;
var t_533: bv32;
var t_537: bv32;
var t_549: bv64;
var t_573: bv64;
var t_609: bv64;
var t_641: bv64;
var t_657: bv32;
var t_681: bv64;
var t_697: bv32;
var t_709: bv64;
var t_725: bv32;
var t_73: bv64;
var t_737: bv64;
var t_753: bv32;
var t_765: bv64;
var t_781: bv32;
var t_787: bv32;
var t_799: bv64;
var t_815: bv32;
var t_819: bv32;
var t_823: bv32;
var t_835: bv64;
var t_859: bv64;
var t_89: bv32;
var t_895: bv64;
var t_9: bv32;
var t_927: bv64;
var t_943: bv32;
var t_967: bv64;
var t_983: bv32;
var t_995: bv64;


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
