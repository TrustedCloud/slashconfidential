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
axiom _function_addr_low == 5008bv64;
axiom _function_addr_high == 6912bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1390:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x1395:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x1399:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x139e:
t_1 := RSP;
RSP := MINUS_64(RSP, 200bv64);
CF := bool2bv(LT_64(t_1, 200bv64));
OF := AND_64((XOR_64(t_1, 200bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 200bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x13a5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5034bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x13aa"} true;
call arbitrary_func();

label_0x13aa:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x13ac:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13b8;
}

label_0x13ae:
RAX := (0bv32 ++ 4294967287bv32);

label_0x13b3:
goto label_0x1af0;

label_0x13b8:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x13c1:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13cd;
}

label_0x13c3:
RAX := (0bv32 ++ 4294967294bv32);

label_0x13c8:
goto label_0x1af0;

label_0x13cd:
t_13 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x13d5:
if (bv2bool(ZF)) {
  goto label_0x13eb;
}

label_0x13d7:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x13df:
if (bv2bool(ZF)) {
  goto label_0x13eb;
}

label_0x13e1:
RAX := (0bv32 ++ 4294967294bv32);

label_0x13e6:
goto label_0x1af0;

label_0x13eb:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x13f3:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x13ff;
}

label_0x13f5:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x13fd:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1409;
}

label_0x13ff:
RAX := (0bv32 ++ 4294967294bv32);

label_0x1404:
goto label_0x1af0;

label_0x1409:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1411:
t_29 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), t_29)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_29, (LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0x1416:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1472;
}

label_0x1418:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1420:
t1_33 := RAX;
t2_34 := 56bv64;
RAX := PLUS_64(RAX, t2_34);
CF := bool2bv(LT_64(RAX, t1_33));
OF := AND_1((bool2bv((t1_33[64:63]) == (t2_34[64:63]))), (XOR_1((t1_33[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_33)), t2_34)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1424:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1429:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x142e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1434:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1439:
t_41 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x143c:
if (bv2bool(ZF)) {
  goto label_0x143f;
}

label_0x143e:
assume false;

label_0x143f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1444:
origDEST_45 := RAX;
origCOUNT_46 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), CF, LSHIFT_64(origDEST_45, (MINUS_64(64bv64, origCOUNT_46)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_46 == 1bv64)), origDEST_45[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), AF, unconstrained_5);

label_0x1448:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x144f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1453:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1458:
origDEST_51 := RCX;
origCOUNT_52 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), CF, LSHIFT_64(origDEST_51, (MINUS_64(64bv64, origCOUNT_52)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_52 == 1bv64)), origDEST_51[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), AF, unconstrained_7);

label_0x145c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x1460:
if (bv2bool(CF)) {
  goto label_0x1463;
}

label_0x1462:
assume false;

label_0x1463:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1468:
RCX := PLUS_64((PLUS_64(0bv64, 5231bv64)), 0bv64)[64:0];

label_0x146f:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1472:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x147a:
t_57 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), t_57)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_57, (LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0x147f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14db;
}

label_0x1481:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1489:
t1_61 := RAX;
t2_62 := 64bv64;
RAX := PLUS_64(RAX, t2_62);
CF := bool2bv(LT_64(RAX, t1_61));
OF := AND_1((bool2bv((t1_61[64:63]) == (t2_62[64:63]))), (XOR_1((t1_61[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_61)), t2_62)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x148d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1492:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1497:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x149d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x14a2:
t_69 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))))[1:0]));
SF := t_69[64:63];
ZF := bool2bv(0bv64 == t_69);

label_0x14a5:
if (bv2bool(ZF)) {
  goto label_0x14a8;
}

label_0x14a7:
assume false;

label_0x14a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x14ad:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_15);

label_0x14b1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x14b8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x14bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x14c1:
origDEST_79 := RCX;
origCOUNT_80 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_17);

label_0x14c5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x14c9:
if (bv2bool(CF)) {
  goto label_0x14cc;
}

label_0x14cb:
assume false;

label_0x14cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x14d1:
RCX := PLUS_64((PLUS_64(0bv64, 5336bv64)), 0bv64)[64:0];

label_0x14d8:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x14db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x14e3:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 56bv64));

label_0x14e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x14ef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x14f7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5372bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14fc"} true;
call arbitrary_func();

label_0x14fc:
R8 := (0bv32 ++ 1bv32);

label_0x1502:
RDX := (0bv32 ++ 64144bv32);

label_0x1507:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x150f:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x1513:

target_85 := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5402bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_85"} true;
call arbitrary_func();

label_0x151a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x151f:
t_87 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_87)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_87, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))))[1:0]));
SF := t_87[64:63];
ZF := bool2bv(0bv64 == t_87);

label_0x1525:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1531;
}

label_0x1527:
RAX := (0bv32 ++ 4294967293bv32);

label_0x152c:
goto label_0x1af0;

label_0x1531:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1536:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x153b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1540:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1546:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x154b:
t_93 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x154e:
if (bv2bool(ZF)) {
  goto label_0x1551;
}

label_0x1550:
assume false;

label_0x1551:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1556:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_25);

label_0x155a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1561:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1565:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x156a:
origDEST_103 := RCX;
origCOUNT_104 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_27);

label_0x156e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0x1572:
if (bv2bool(CF)) {
  goto label_0x1575;
}

label_0x1574:
assume false;

label_0x1575:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x157a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1582:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1585:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x158d:
t1_109 := RAX;
t2_110 := 48bv64;
RAX := PLUS_64(RAX, t2_110);
CF := bool2bv(LT_64(RAX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1591:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1596:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x159b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15a1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15a6:
t_117 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x15a9:
if (bv2bool(ZF)) {
  goto label_0x15ac;
}

label_0x15ab:
assume false;

label_0x15ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15b1:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_35);

label_0x15b5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x15bc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x15c0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15c5:
origDEST_127 := RCX;
origCOUNT_128 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_37);

label_0x15c9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0x15cd:
if (bv2bool(CF)) {
  goto label_0x15d0;
}

label_0x15cf:
assume false;

label_0x15d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15d5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x15da:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x15dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x15e2:
t1_133 := RAX;
t2_134 := 8bv64;
RAX := PLUS_64(RAX, t2_134);
CF := bool2bv(LT_64(RAX, t1_133));
OF := AND_1((bool2bv((t1_133[64:63]) == (t2_134[64:63]))), (XOR_1((t1_133[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_133)), t2_134)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15e6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x15eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x15f0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15f6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15fb:
t_141 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)), 2bv64)), (XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)), 2bv64)), (XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)))))[1:0]));
SF := t_141[64:63];
ZF := bool2bv(0bv64 == t_141);

label_0x15fe:
if (bv2bool(ZF)) {
  goto label_0x1601;
}

label_0x1600:
assume false;

label_0x1601:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1606:
origDEST_145 := RAX;
origCOUNT_146 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), CF, LSHIFT_64(origDEST_145, (MINUS_64(64bv64, origCOUNT_146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_146 == 1bv64)), origDEST_145[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), AF, unconstrained_45);

label_0x160a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1611:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1615:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x161a:
origDEST_151 := RCX;
origCOUNT_152 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), CF, LSHIFT_64(origDEST_151, (MINUS_64(64bv64, origCOUNT_152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_152 == 1bv64)), origDEST_151[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), AF, unconstrained_47);

label_0x161e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0x1622:
if (bv2bool(CF)) {
  goto label_0x1625;
}

label_0x1624:
assume false;

label_0x1625:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x162a:
mem := STORE_LE_32(mem, RAX, 10bv32);

label_0x1630:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1635:
t1_157 := RAX;
t2_158 := 36bv64;
RAX := PLUS_64(RAX, t2_158);
CF := bool2bv(LT_64(RAX, t1_157));
OF := AND_1((bool2bv((t1_157[64:63]) == (t2_158[64:63]))), (XOR_1((t1_157[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_157)), t2_158)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1639:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x163e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1643:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1649:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x164e:
t_165 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)), 2bv64)), (XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)), 2bv64)), (XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)))))[1:0]));
SF := t_165[64:63];
ZF := bool2bv(0bv64 == t_165);

label_0x1651:
if (bv2bool(ZF)) {
  goto label_0x1654;
}

label_0x1653:
assume false;

label_0x1654:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1659:
origDEST_169 := RAX;
origCOUNT_170 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), CF, LSHIFT_64(origDEST_169, (MINUS_64(64bv64, origCOUNT_170)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv64)), origDEST_169[64:63], unconstrained_54));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), AF, unconstrained_55);

label_0x165d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1664:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1668:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x166d:
origDEST_175 := RCX;
origCOUNT_176 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_57);

label_0x1671:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_58;
SF := unconstrained_59;
AF := unconstrained_60;
PF := unconstrained_61;

label_0x1675:
if (bv2bool(CF)) {
  goto label_0x1678;
}

label_0x1677:
assume false;

label_0x1678:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x167d:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1683:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1688:
t1_181 := RAX;
t2_182 := 32bv64;
RAX := PLUS_64(RAX, t2_182);
CF := bool2bv(LT_64(RAX, t1_181));
OF := AND_1((bool2bv((t1_181[64:63]) == (t2_182[64:63]))), (XOR_1((t1_181[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_181)), t2_182)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x168c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x1691:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1696:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x169c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x16a1:
t_189 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))))[1:0]));
SF := t_189[64:63];
ZF := bool2bv(0bv64 == t_189);

label_0x16a4:
if (bv2bool(ZF)) {
  goto label_0x16a7;
}

label_0x16a6:
assume false;

label_0x16a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x16ac:
origDEST_193 := RAX;
origCOUNT_194 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), CF, LSHIFT_64(origDEST_193, (MINUS_64(64bv64, origCOUNT_194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_194 == 1bv64)), origDEST_193[64:63], unconstrained_64));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), AF, unconstrained_65);

label_0x16b0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x16b7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x16bb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x16c0:
origDEST_199 := RCX;
origCOUNT_200 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_67);

label_0x16c4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_68;
SF := unconstrained_69;
AF := unconstrained_70;
PF := unconstrained_71;

label_0x16c8:
if (bv2bool(CF)) {
  goto label_0x16cb;
}

label_0x16ca:
assume false;

label_0x16cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x16d0:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x16d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x16db:
t1_205 := RAX;
t2_206 := 3188bv64;
RAX := PLUS_64(RAX, t2_206);
CF := bool2bv(LT_64(RAX, t1_205));
OF := AND_1((bool2bv((t1_205[64:63]) == (t2_206[64:63]))), (XOR_1((t1_205[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_205)), t2_206)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16e1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x16e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x16eb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16f1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x16f6:
t_213 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_73;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))))[1:0]));
SF := t_213[64:63];
ZF := bool2bv(0bv64 == t_213);

label_0x16f9:
if (bv2bool(ZF)) {
  goto label_0x16fc;
}

label_0x16fb:
assume false;

label_0x16fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1701:
origDEST_217 := RAX;
origCOUNT_218 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), CF, LSHIFT_64(origDEST_217, (MINUS_64(64bv64, origCOUNT_218)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv64)), origDEST_217[64:63], unconstrained_74));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), AF, unconstrained_75);

label_0x1705:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x170c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1710:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1715:
origDEST_223 := RCX;
origCOUNT_224 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), CF, LSHIFT_64(origDEST_223, (MINUS_64(64bv64, origCOUNT_224)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_224 == 1bv64)), origDEST_223[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), AF, unconstrained_77);

label_0x1719:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_78;
SF := unconstrained_79;
AF := unconstrained_80;
PF := unconstrained_81;

label_0x171d:
if (bv2bool(CF)) {
  goto label_0x1720;
}

label_0x171f:
assume false;

label_0x1720:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1725:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x172b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1733:
t1_229 := RAX;
t2_230 := 12bv64;
RAX := PLUS_64(RAX, t2_230);
CF := bool2bv(LT_64(RAX, t1_229));
OF := AND_1((bool2bv((t1_229[64:63]) == (t2_230[64:63]))), (XOR_1((t1_229[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_229)), t2_230)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1737:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x173c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1741:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1747:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x174c:
t_237 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_83;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))))[1:0]));
SF := t_237[64:63];
ZF := bool2bv(0bv64 == t_237);

label_0x174f:
if (bv2bool(ZF)) {
  goto label_0x1752;
}

label_0x1751:
assume false;

label_0x1752:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1757:
origDEST_241 := RAX;
origCOUNT_242 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), CF, LSHIFT_64(origDEST_241, (MINUS_64(64bv64, origCOUNT_242)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_242 == 1bv64)), origDEST_241[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), AF, unconstrained_85);

label_0x175b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1762:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1766:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x176b:
origDEST_247 := RCX;
origCOUNT_248 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), CF, LSHIFT_64(origDEST_247, (MINUS_64(64bv64, origCOUNT_248)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_248 == 1bv64)), origDEST_247[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), AF, unconstrained_87);

label_0x176f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_88;
SF := unconstrained_89;
AF := unconstrained_90;
PF := unconstrained_91;

label_0x1773:
if (bv2bool(CF)) {
  goto label_0x1776;
}

label_0x1775:
assume false;

label_0x1776:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x177b:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1781:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1789:
t1_253 := RAX;
t2_254 := 16bv64;
RAX := PLUS_64(RAX, t2_254);
CF := bool2bv(LT_64(RAX, t1_253));
OF := AND_1((bool2bv((t1_253[64:63]) == (t2_254[64:63]))), (XOR_1((t1_253[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_253)), t2_254)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x178d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x1792:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1797:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x179d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17a2:
t_261 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_93;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_261, 4bv64)), t_261)), 2bv64)), (XOR_64((RSHIFT_64(t_261, 4bv64)), t_261)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_261, 4bv64)), t_261)), 2bv64)), (XOR_64((RSHIFT_64(t_261, 4bv64)), t_261)))))[1:0]));
SF := t_261[64:63];
ZF := bool2bv(0bv64 == t_261);

label_0x17a5:
if (bv2bool(ZF)) {
  goto label_0x17a8;
}

label_0x17a7:
assume false;

label_0x17a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x17ad:
origDEST_265 := RAX;
origCOUNT_266 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), CF, LSHIFT_64(origDEST_265, (MINUS_64(64bv64, origCOUNT_266)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_266 == 1bv64)), origDEST_265[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), AF, unconstrained_95);

label_0x17b1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x17b8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x17c1:
origDEST_271 := RCX;
origCOUNT_272 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), CF, LSHIFT_64(origDEST_271, (MINUS_64(64bv64, origCOUNT_272)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_272 == 1bv64)), origDEST_271[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), AF, unconstrained_97);

label_0x17c5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_98;
SF := unconstrained_99;
AF := unconstrained_100;
PF := unconstrained_101;

label_0x17c9:
if (bv2bool(CF)) {
  goto label_0x17cc;
}

label_0x17cb:
assume false;

label_0x17cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x17d1:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x17d7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x17df:
t1_277 := RAX;
t2_278 := 36bv64;
RAX := PLUS_64(RAX, t2_278);
CF := bool2bv(LT_64(RAX, t1_277));
OF := AND_1((bool2bv((t1_277[64:63]) == (t2_278[64:63]))), (XOR_1((t1_277[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_277)), t2_278)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17e3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x17e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x17ed:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17f3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17f8:
t_285 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_103;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_285, 4bv64)), t_285)), 2bv64)), (XOR_64((RSHIFT_64(t_285, 4bv64)), t_285)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_285, 4bv64)), t_285)), 2bv64)), (XOR_64((RSHIFT_64(t_285, 4bv64)), t_285)))))[1:0]));
SF := t_285[64:63];
ZF := bool2bv(0bv64 == t_285);

label_0x17fb:
if (bv2bool(ZF)) {
  goto label_0x17fe;
}

label_0x17fd:
assume false;

label_0x17fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1803:
origDEST_289 := RAX;
origCOUNT_290 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), CF, LSHIFT_64(origDEST_289, (MINUS_64(64bv64, origCOUNT_290)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_290 == 1bv64)), origDEST_289[64:63], unconstrained_104));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), AF, unconstrained_105);

label_0x1807:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x180e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1812:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1817:
origDEST_295 := RCX;
origCOUNT_296 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), CF, LSHIFT_64(origDEST_295, (MINUS_64(64bv64, origCOUNT_296)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_296 == 1bv64)), origDEST_295[64:63], unconstrained_106));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_296 == 0bv64)), AF, unconstrained_107);

label_0x181b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_108;
SF := unconstrained_109;
AF := unconstrained_110;
PF := unconstrained_111;

label_0x181f:
if (bv2bool(CF)) {
  goto label_0x1822;
}

label_0x1821:
assume false;

label_0x1822:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1827:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x182d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x1835:
t1_301 := RAX;
t2_302 := 40bv64;
RAX := PLUS_64(RAX, t2_302);
CF := bool2bv(LT_64(RAX, t1_301));
OF := AND_1((bool2bv((t1_301[64:63]) == (t2_302[64:63]))), (XOR_1((t1_301[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_301)), t2_302)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1839:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x1841:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1849:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_112;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x184f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1854:
t_309 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_113;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_309, 4bv64)), t_309)), 2bv64)), (XOR_64((RSHIFT_64(t_309, 4bv64)), t_309)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_309, 4bv64)), t_309)), 2bv64)), (XOR_64((RSHIFT_64(t_309, 4bv64)), t_309)))))[1:0]));
SF := t_309[64:63];
ZF := bool2bv(0bv64 == t_309);

label_0x1857:
if (bv2bool(ZF)) {
  goto label_0x185a;
}

label_0x1859:
assume false;

label_0x185a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1862:
origDEST_313 := RAX;
origCOUNT_314 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), CF, LSHIFT_64(origDEST_313, (MINUS_64(64bv64, origCOUNT_314)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_314 == 1bv64)), origDEST_313[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), AF, unconstrained_115);

label_0x1866:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x186d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1871:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1879:
origDEST_319 := RCX;
origCOUNT_320 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), CF, LSHIFT_64(origDEST_319, (MINUS_64(64bv64, origCOUNT_320)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_320 == 1bv64)), origDEST_319[64:63], unconstrained_116));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), AF, unconstrained_117);

label_0x187d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_118;
SF := unconstrained_119;
AF := unconstrained_120;
PF := unconstrained_121;

label_0x1881:
if (bv2bool(CF)) {
  goto label_0x1884;
}

label_0x1883:
assume false;

label_0x1884:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x188c:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1892:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1897:
t1_325 := RAX;
t2_326 := 44bv64;
RAX := PLUS_64(RAX, t2_326);
CF := bool2bv(LT_64(RAX, t1_325));
OF := AND_1((bool2bv((t1_325[64:63]) == (t2_326[64:63]))), (XOR_1((t1_325[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_325)), t2_326)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x189b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x18a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18ab:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_122;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18b1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x18b6:
t_333 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_123;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_333, 4bv64)), t_333)), 2bv64)), (XOR_64((RSHIFT_64(t_333, 4bv64)), t_333)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_333, 4bv64)), t_333)), 2bv64)), (XOR_64((RSHIFT_64(t_333, 4bv64)), t_333)))))[1:0]));
SF := t_333[64:63];
ZF := bool2bv(0bv64 == t_333);

label_0x18b9:
if (bv2bool(ZF)) {
  goto label_0x18bc;
}

label_0x18bb:
assume false;

label_0x18bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18c4:
origDEST_337 := RAX;
origCOUNT_338 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), CF, LSHIFT_64(origDEST_337, (MINUS_64(64bv64, origCOUNT_338)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_338 == 1bv64)), origDEST_337[64:63], unconstrained_124));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), AF, unconstrained_125);

label_0x18c8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x18cf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x18d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18db:
origDEST_343 := RCX;
origCOUNT_344 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), CF, LSHIFT_64(origDEST_343, (MINUS_64(64bv64, origCOUNT_344)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_344 == 1bv64)), origDEST_343[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), AF, unconstrained_127);

label_0x18df:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_128;
SF := unconstrained_129;
AF := unconstrained_130;
PF := unconstrained_131;

label_0x18e3:
if (bv2bool(CF)) {
  goto label_0x18e6;
}

label_0x18e5:
assume false;

label_0x18e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18ee:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 224bv64))));

label_0x18f6:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x18f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x18fd:
t1_349 := RAX;
t2_350 := 3168bv64;
RAX := PLUS_64(RAX, t2_350);
CF := bool2bv(LT_64(RAX, t1_349));
OF := AND_1((bool2bv((t1_349[64:63]) == (t2_350[64:63]))), (XOR_1((t1_349[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_349)), t2_350)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1903:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x190b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1913:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1919:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x191e:
t_357 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))))[1:0]));
SF := t_357[64:63];
ZF := bool2bv(0bv64 == t_357);

label_0x1921:
if (bv2bool(ZF)) {
  goto label_0x1924;
}

label_0x1923:
assume false;

label_0x1924:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x192c:
origDEST_361 := RAX;
origCOUNT_362 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), CF, LSHIFT_64(origDEST_361, (MINUS_64(64bv64, origCOUNT_362)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_362 == 1bv64)), origDEST_361[64:63], unconstrained_134));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), AF, unconstrained_135);

label_0x1930:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1937:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x193b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1943:
origDEST_367 := RCX;
origCOUNT_368 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, LSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), origDEST_367[64:63], unconstrained_136));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_137);

label_0x1947:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_138;
SF := unconstrained_139;
AF := unconstrained_140;
PF := unconstrained_141;

label_0x194b:
if (bv2bool(CF)) {
  goto label_0x194e;
}

label_0x194d:
assume false;

label_0x194e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1956:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x195d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1962:
t1_373 := RAX;
t2_374 := 3160bv64;
RAX := PLUS_64(RAX, t2_374);
CF := bool2bv(LT_64(RAX, t1_373));
OF := AND_1((bool2bv((t1_373[64:63]) == (t2_374[64:63]))), (XOR_1((t1_373[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_373)), t2_374)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1968:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x1970:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x1978:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_142;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x197e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1983:
t_381 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_143;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_381, 4bv64)), t_381)), 2bv64)), (XOR_64((RSHIFT_64(t_381, 4bv64)), t_381)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_381, 4bv64)), t_381)), 2bv64)), (XOR_64((RSHIFT_64(t_381, 4bv64)), t_381)))))[1:0]));
SF := t_381[64:63];
ZF := bool2bv(0bv64 == t_381);

label_0x1986:
if (bv2bool(ZF)) {
  goto label_0x1989;
}

label_0x1988:
assume false;

label_0x1989:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x1991:
origDEST_385 := RAX;
origCOUNT_386 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), CF, LSHIFT_64(origDEST_385, (MINUS_64(64bv64, origCOUNT_386)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_386 == 1bv64)), origDEST_385[64:63], unconstrained_144));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), AF, unconstrained_145);

label_0x1995:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x199c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x19a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19a8:
origDEST_391 := RCX;
origCOUNT_392 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), CF, LSHIFT_64(origDEST_391, (MINUS_64(64bv64, origCOUNT_392)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_392 == 1bv64)), origDEST_391[64:63], unconstrained_146));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), AF, unconstrained_147);

label_0x19ac:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_148;
SF := unconstrained_149;
AF := unconstrained_150;
PF := unconstrained_151;

label_0x19b0:
if (bv2bool(CF)) {
  goto label_0x19b3;
}

label_0x19b2:
assume false;

label_0x19b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19bb:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x19c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x19c7:
t1_397 := RAX;
t2_398 := 3152bv64;
RAX := PLUS_64(RAX, t2_398);
CF := bool2bv(LT_64(RAX, t1_397));
OF := AND_1((bool2bv((t1_397[64:63]) == (t2_398[64:63]))), (XOR_1((t1_397[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_397)), t2_398)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x19cd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x19d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19dd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_152;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x19e3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x19e8:
t_405 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_153;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_405, 4bv64)), t_405)), 2bv64)), (XOR_64((RSHIFT_64(t_405, 4bv64)), t_405)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_405, 4bv64)), t_405)), 2bv64)), (XOR_64((RSHIFT_64(t_405, 4bv64)), t_405)))))[1:0]));
SF := t_405[64:63];
ZF := bool2bv(0bv64 == t_405);

label_0x19eb:
if (bv2bool(ZF)) {
  goto label_0x19ee;
}

label_0x19ed:
assume false;

label_0x19ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19f6:
origDEST_409 := RAX;
origCOUNT_410 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), CF, LSHIFT_64(origDEST_409, (MINUS_64(64bv64, origCOUNT_410)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_410 == 1bv64)), origDEST_409[64:63], unconstrained_154));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), AF, unconstrained_155);

label_0x19fa:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a01:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a05:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a0d:
origDEST_415 := RCX;
origCOUNT_416 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), CF, LSHIFT_64(origDEST_415, (MINUS_64(64bv64, origCOUNT_416)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_416 == 1bv64)), origDEST_415[64:63], unconstrained_156));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), AF, unconstrained_157);

label_0x1a11:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_158;
SF := unconstrained_159;
AF := unconstrained_160;
PF := unconstrained_161;

label_0x1a15:
if (bv2bool(CF)) {
  goto label_0x1a18;
}

label_0x1a17:
assume false;

label_0x1a18:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a20:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x1a27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1a2c:
t1_421 := RAX;
t2_422 := 48bv64;
RAX := PLUS_64(RAX, t2_422);
CF := bool2bv(LT_64(RAX, t1_421));
OF := AND_1((bool2bv((t1_421[64:63]) == (t2_422[64:63]))), (XOR_1((t1_421[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_421)), t2_422)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a30:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x1a38:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a40:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_162;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a46:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a4b:
t_429 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_163;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))))[1:0]));
SF := t_429[64:63];
ZF := bool2bv(0bv64 == t_429);

label_0x1a4e:
if (bv2bool(ZF)) {
  goto label_0x1a51;
}

label_0x1a50:
assume false;

label_0x1a51:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a59:
origDEST_433 := RAX;
origCOUNT_434 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), CF, LSHIFT_64(origDEST_433, (MINUS_64(64bv64, origCOUNT_434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_434 == 1bv64)), origDEST_433[64:63], unconstrained_164));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), AF, unconstrained_165);

label_0x1a5d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a64:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a68:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a70:
origDEST_439 := RCX;
origCOUNT_440 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), CF, LSHIFT_64(origDEST_439, (MINUS_64(64bv64, origCOUNT_440)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_440 == 1bv64)), origDEST_439[64:63], unconstrained_166));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), AF, unconstrained_167);

label_0x1a74:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_168;
SF := unconstrained_169;
AF := unconstrained_170;
PF := unconstrained_171;

label_0x1a78:
if (bv2bool(CF)) {
  goto label_0x1a7b;
}

label_0x1a7a:
assume false;

label_0x1a7b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a83:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1a89:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1a8e:
t1_445 := RAX;
t2_446 := 52bv64;
RAX := PLUS_64(RAX, t2_446);
CF := bool2bv(LT_64(RAX, t1_445));
OF := AND_1((bool2bv((t1_445[64:63]) == (t2_446[64:63]))), (XOR_1((t1_445[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_445)), t2_446)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a92:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x1a9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1aa2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_172;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1aa8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1aad:
t_453 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_173;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)), 2bv64)), (XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)), 2bv64)), (XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)))))[1:0]));
SF := t_453[64:63];
ZF := bool2bv(0bv64 == t_453);

label_0x1ab0:
if (bv2bool(ZF)) {
  goto label_0x1ab3;
}

label_0x1ab2:
assume false;

label_0x1ab3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1abb:
origDEST_457 := RAX;
origCOUNT_458 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), CF, LSHIFT_64(origDEST_457, (MINUS_64(64bv64, origCOUNT_458)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_458 == 1bv64)), origDEST_457[64:63], unconstrained_174));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), AF, unconstrained_175);

label_0x1abf:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1ac6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1aca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1ad2:
origDEST_463 := RCX;
origCOUNT_464 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), CF, LSHIFT_64(origDEST_463, (MINUS_64(64bv64, origCOUNT_464)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_464 == 1bv64)), origDEST_463[64:63], unconstrained_176));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), AF, unconstrained_177);

label_0x1ad6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_178;
SF := unconstrained_179;
AF := unconstrained_180;
PF := unconstrained_181;

label_0x1ada:
if (bv2bool(CF)) {
  goto label_0x1add;
}

label_0x1adc:
assume false;

label_0x1add:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1ae5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)));

label_0x1aec:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1aee:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_182;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1af0:
t1_469 := RSP;
t2_470 := 200bv64;
RSP := PLUS_64(RSP, t2_470);
CF := bool2bv(LT_64(RSP, t1_469));
OF := AND_1((bool2bv((t1_469[64:63]) == (t2_470[64:63]))), (XOR_1((t1_469[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_469)), t2_470)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1af7:

ra_475 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_122,origCOUNT_128,origCOUNT_146,origCOUNT_152,origCOUNT_170,origCOUNT_176,origCOUNT_194,origCOUNT_200,origCOUNT_218,origCOUNT_224,origCOUNT_242,origCOUNT_248,origCOUNT_266,origCOUNT_272,origCOUNT_290,origCOUNT_296,origCOUNT_314,origCOUNT_320,origCOUNT_338,origCOUNT_344,origCOUNT_362,origCOUNT_368,origCOUNT_386,origCOUNT_392,origCOUNT_410,origCOUNT_416,origCOUNT_434,origCOUNT_440,origCOUNT_458,origCOUNT_46,origCOUNT_464,origCOUNT_52,origCOUNT_74,origCOUNT_80,origCOUNT_98,origDEST_103,origDEST_121,origDEST_127,origDEST_145,origDEST_151,origDEST_169,origDEST_175,origDEST_193,origDEST_199,origDEST_217,origDEST_223,origDEST_241,origDEST_247,origDEST_265,origDEST_271,origDEST_289,origDEST_295,origDEST_313,origDEST_319,origDEST_337,origDEST_343,origDEST_361,origDEST_367,origDEST_385,origDEST_391,origDEST_409,origDEST_415,origDEST_433,origDEST_439,origDEST_45,origDEST_457,origDEST_463,origDEST_51,origDEST_73,origDEST_79,origDEST_97,ra_475,t1_109,t1_133,t1_157,t1_181,t1_205,t1_229,t1_253,t1_277,t1_301,t1_325,t1_33,t1_349,t1_373,t1_397,t1_421,t1_445,t1_469,t1_61,t2_110,t2_134,t2_158,t2_182,t2_206,t2_230,t2_254,t2_278,t2_302,t2_326,t2_34,t2_350,t2_374,t2_398,t2_422,t2_446,t2_470,t2_62,t_1,t_117,t_13,t_141,t_165,t_17,t_189,t_21,t_213,t_237,t_25,t_261,t_285,t_29,t_309,t_333,t_357,t_381,t_405,t_41,t_429,t_453,t_5,t_57,t_69,t_87,t_9,t_93,target_85;

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
const unconstrained_98: bv1;
const unconstrained_99: bv1;
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
var origCOUNT_104: bv64;
var origCOUNT_122: bv64;
var origCOUNT_128: bv64;
var origCOUNT_146: bv64;
var origCOUNT_152: bv64;
var origCOUNT_170: bv64;
var origCOUNT_176: bv64;
var origCOUNT_194: bv64;
var origCOUNT_200: bv64;
var origCOUNT_218: bv64;
var origCOUNT_224: bv64;
var origCOUNT_242: bv64;
var origCOUNT_248: bv64;
var origCOUNT_266: bv64;
var origCOUNT_272: bv64;
var origCOUNT_290: bv64;
var origCOUNT_296: bv64;
var origCOUNT_314: bv64;
var origCOUNT_320: bv64;
var origCOUNT_338: bv64;
var origCOUNT_344: bv64;
var origCOUNT_362: bv64;
var origCOUNT_368: bv64;
var origCOUNT_386: bv64;
var origCOUNT_392: bv64;
var origCOUNT_410: bv64;
var origCOUNT_416: bv64;
var origCOUNT_434: bv64;
var origCOUNT_440: bv64;
var origCOUNT_458: bv64;
var origCOUNT_46: bv64;
var origCOUNT_464: bv64;
var origCOUNT_52: bv64;
var origCOUNT_74: bv64;
var origCOUNT_80: bv64;
var origCOUNT_98: bv64;
var origDEST_103: bv64;
var origDEST_121: bv64;
var origDEST_127: bv64;
var origDEST_145: bv64;
var origDEST_151: bv64;
var origDEST_169: bv64;
var origDEST_175: bv64;
var origDEST_193: bv64;
var origDEST_199: bv64;
var origDEST_217: bv64;
var origDEST_223: bv64;
var origDEST_241: bv64;
var origDEST_247: bv64;
var origDEST_265: bv64;
var origDEST_271: bv64;
var origDEST_289: bv64;
var origDEST_295: bv64;
var origDEST_313: bv64;
var origDEST_319: bv64;
var origDEST_337: bv64;
var origDEST_343: bv64;
var origDEST_361: bv64;
var origDEST_367: bv64;
var origDEST_385: bv64;
var origDEST_391: bv64;
var origDEST_409: bv64;
var origDEST_415: bv64;
var origDEST_433: bv64;
var origDEST_439: bv64;
var origDEST_45: bv64;
var origDEST_457: bv64;
var origDEST_463: bv64;
var origDEST_51: bv64;
var origDEST_73: bv64;
var origDEST_79: bv64;
var origDEST_97: bv64;
var ra_475: bv64;
var t1_109: bv64;
var t1_133: bv64;
var t1_157: bv64;
var t1_181: bv64;
var t1_205: bv64;
var t1_229: bv64;
var t1_253: bv64;
var t1_277: bv64;
var t1_301: bv64;
var t1_325: bv64;
var t1_33: bv64;
var t1_349: bv64;
var t1_373: bv64;
var t1_397: bv64;
var t1_421: bv64;
var t1_445: bv64;
var t1_469: bv64;
var t1_61: bv64;
var t2_110: bv64;
var t2_134: bv64;
var t2_158: bv64;
var t2_182: bv64;
var t2_206: bv64;
var t2_230: bv64;
var t2_254: bv64;
var t2_278: bv64;
var t2_302: bv64;
var t2_326: bv64;
var t2_34: bv64;
var t2_350: bv64;
var t2_374: bv64;
var t2_398: bv64;
var t2_422: bv64;
var t2_446: bv64;
var t2_470: bv64;
var t2_62: bv64;
var t_1: bv64;
var t_117: bv64;
var t_13: bv32;
var t_141: bv64;
var t_165: bv64;
var t_17: bv32;
var t_189: bv64;
var t_21: bv32;
var t_213: bv64;
var t_237: bv64;
var t_25: bv32;
var t_261: bv64;
var t_285: bv64;
var t_29: bv64;
var t_309: bv64;
var t_333: bv64;
var t_357: bv64;
var t_381: bv64;
var t_405: bv64;
var t_41: bv64;
var t_429: bv64;
var t_453: bv64;
var t_5: bv32;
var t_57: bv64;
var t_69: bv64;
var t_87: bv64;
var t_9: bv64;
var t_93: bv64;
var target_85: bv64;


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
