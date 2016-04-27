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
axiom _function_addr_low == 0bv64;
axiom _function_addr_high == 3456bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0xa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0xe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x13:
t_1 := RSP;
RSP := MINUS_64(RSP, 408bv64);
CF := bool2bv(LT_64(t_1, 408bv64));
OF := AND_64((XOR_64(t_1, 408bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 408bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 440bv64)));

label_0x21:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x25:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 42bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a"} true;
call arbitrary_func();

label_0x2a:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x2c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x38;
}

label_0x2e:
RAX := (0bv32 ++ 4294967287bv32);

label_0x33:
goto label_0xd6f;

label_0x38:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 416bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 416bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 416bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 416bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 416bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x41:
if (bv2bool(ZF)) {
  goto label_0x68;
}

label_0x43:
t_13 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x4b:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x68;
}

label_0x4d:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 9bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 9bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), 9bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))))), 9bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x55:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x68;
}

label_0x57:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x5c:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x68;
}

label_0x5e:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 250bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x66:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x72;
}

label_0x68:
RAX := (0bv32 ++ 4294967294bv32);

label_0x6d:
goto label_0xd6f;

label_0x72:
t_29 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_29)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_29, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))))[1:0]));
SF := t_29[32:31];
ZF := bool2bv(0bv32 == t_29);

label_0x77:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x81;
}

label_0x79:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 30bv32);

label_0x81:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x89:
t_33 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))), t_33)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_33, (LOAD_LE_64(mem, PLUS_64(RAX, 56bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x8e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xea;
}

label_0x90:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x98:
t1_37 := RAX;
t2_38 := 56bv64;
RAX := PLUS_64(RAX, t2_38);
CF := bool2bv(LT_64(RAX, t1_37));
OF := AND_1((bool2bv((t1_37[64:63]) == (t2_38[64:63]))), (XOR_1((t1_37[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_37)), t2_38)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0xa1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xa6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xac:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb1:
t_45 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)), 2bv64)), (XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)), 2bv64)), (XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)))))[1:0]));
SF := t_45[64:63];
ZF := bool2bv(0bv64 == t_45);

label_0xb4:
if (bv2bool(ZF)) {
  goto label_0xb7;
}

label_0xb6:
assume false;

label_0xb7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xbc:
origDEST_49 := RAX;
origCOUNT_50 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_5);

label_0xc0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xd0:
origDEST_55 := RCX;
origCOUNT_56 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_7);

label_0xd4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0xd8:
if (bv2bool(CF)) {
  goto label_0xdb;
}

label_0xda:
assume false;

label_0xdb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xe0:
RCX := PLUS_64((PLUS_64(0bv64, 231bv64)), 0bv64)[64:0];

label_0xe7:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xf2:
t_61 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))), t_61)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_61, (LOAD_LE_64(mem, PLUS_64(RAX, 64bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))))[1:0]));
SF := t_61[64:63];
ZF := bool2bv(0bv64 == t_61);

label_0xf7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x153;
}

label_0xf9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x101:
t1_65 := RAX;
t2_66 := 64bv64;
RAX := PLUS_64(RAX, t2_66);
CF := bool2bv(LT_64(RAX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x105:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x10a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x10f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x115:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11a:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0x11d:
if (bv2bool(ZF)) {
  goto label_0x120;
}

label_0x11f:
assume false;

label_0x120:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x125:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_15);

label_0x129:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x130:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x134:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x139:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_17);

label_0x13d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x141:
if (bv2bool(CF)) {
  goto label_0x144;
}

label_0x143:
assume false;

label_0x144:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x149:
RCX := PLUS_64((PLUS_64(0bv64, 336bv64)), 0bv64)[64:0];

label_0x150:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x153:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x15b:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 56bv64));

label_0x15f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0x167:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x16f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 372bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x174"} true;
call arbitrary_func();

label_0x174:
R8 := (0bv32 ++ 1bv32);

label_0x17a:
RDX := (0bv32 ++ 55768bv32);

label_0x17f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x187:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x18b:

target_89 := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 402bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_89"} true;
call arbitrary_func();

label_0x192:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x197:
t_91 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_91)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_91, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))))[1:0]));
SF := t_91[64:63];
ZF := bool2bv(0bv64 == t_91);

label_0x19d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1a9;
}

label_0x19f:
RAX := (0bv32 ++ 4294967293bv32);

label_0x1a4:
goto label_0xd6f;

label_0x1a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1ae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1b8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1be:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1c3:
t_97 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))))[1:0]));
SF := t_97[64:63];
ZF := bool2bv(0bv64 == t_97);

label_0x1c6:
if (bv2bool(ZF)) {
  goto label_0x1c9;
}

label_0x1c8:
assume false;

label_0x1c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1ce:
origDEST_101 := RAX;
origCOUNT_102 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), CF, LSHIFT_64(origDEST_101, (MINUS_64(64bv64, origCOUNT_102)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_102 == 1bv64)), origDEST_101[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), AF, unconstrained_25);

label_0x1d2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1d9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1dd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1e2:
origDEST_107 := RCX;
origCOUNT_108 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_27);

label_0x1e6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0x1ea:
if (bv2bool(CF)) {
  goto label_0x1ed;
}

label_0x1ec:
assume false;

label_0x1ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1f2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x1fa:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x202:
t1_113 := RAX;
t2_114 := 24bv64;
RAX := PLUS_64(RAX, t2_114);
CF := bool2bv(LT_64(RAX, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x206:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x20b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x210:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x216:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x21b:
t_121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x21e:
if (bv2bool(ZF)) {
  goto label_0x221;
}

label_0x220:
assume false;

label_0x221:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x226:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_35);

label_0x22a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x231:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x235:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x23a:
origDEST_131 := RCX;
origCOUNT_132 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_37);

label_0x23e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0x242:
if (bv2bool(CF)) {
  goto label_0x245;
}

label_0x244:
assume false;

label_0x245:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x24a:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x251:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x256:
t1_137 := RAX;
t2_138 := 32bv64;
RAX := PLUS_64(RAX, t2_138);
CF := bool2bv(LT_64(RAX, t1_137));
OF := AND_1((bool2bv((t1_137[64:63]) == (t2_138[64:63]))), (XOR_1((t1_137[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_137)), t2_138)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x25f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x264:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x26f:
t_145 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)), 2bv64)), (XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)), 2bv64)), (XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)))))[1:0]));
SF := t_145[64:63];
ZF := bool2bv(0bv64 == t_145);

label_0x272:
if (bv2bool(ZF)) {
  goto label_0x275;
}

label_0x274:
assume false;

label_0x275:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x27a:
origDEST_149 := RAX;
origCOUNT_150 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_45);

label_0x27e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x285:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x289:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x28e:
origDEST_155 := RCX;
origCOUNT_156 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_47);

label_0x292:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0x296:
if (bv2bool(CF)) {
  goto label_0x299;
}

label_0x298:
assume false;

label_0x299:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x29e:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x2a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2aa:
t1_161 := RAX;
t2_162 := 40bv64;
RAX := PLUS_64(RAX, t2_162);
CF := bool2bv(LT_64(RAX, t1_161));
OF := AND_1((bool2bv((t1_161[64:63]) == (t2_162[64:63]))), (XOR_1((t1_161[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_161)), t2_162)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x2b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2b8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2be:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2c3:
t_169 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)), 2bv64)), (XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)), 2bv64)), (XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)))))[1:0]));
SF := t_169[64:63];
ZF := bool2bv(0bv64 == t_169);

label_0x2c6:
if (bv2bool(ZF)) {
  goto label_0x2c9;
}

label_0x2c8:
assume false;

label_0x2c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2ce:
origDEST_173 := RAX;
origCOUNT_174 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), CF, LSHIFT_64(origDEST_173, (MINUS_64(64bv64, origCOUNT_174)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv64)), origDEST_173[64:63], unconstrained_54));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), AF, unconstrained_55);

label_0x2d2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2d9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2dd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2e2:
origDEST_179 := RCX;
origCOUNT_180 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), CF, LSHIFT_64(origDEST_179, (MINUS_64(64bv64, origCOUNT_180)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_180 == 1bv64)), origDEST_179[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), AF, unconstrained_57);

label_0x2e6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_58;
SF := unconstrained_59;
AF := unconstrained_60;
PF := unconstrained_61;

label_0x2ea:
if (bv2bool(CF)) {
  goto label_0x2ed;
}

label_0x2ec:
assume false;

label_0x2ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2f2:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x2f9:
t_185 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 424bv64)))))), ((ITE_64(bv2bool(100000bv32[32:31]) ,(1bv32 ++ 100000bv32) ,(0bv32 ++ 100000bv32)))));
RAX := (0bv32 ++ t_185[32:0]);
OF := bool2bv(t_185 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_185 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_62;
SF := unconstrained_63;
ZF := unconstrained_64;
AF := unconstrained_65;

label_0x304:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x308:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)))));

label_0x30d:
origDEST_187 := RAX;
origCOUNT_188 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, RSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_67);

label_0x311:
mem := STORE_LE_64(mem, PLUS_64(RSP, 328bv64), RAX);

label_0x319:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x321:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 56bv64));

label_0x325:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RCX);

label_0x32d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x335:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 826bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x33a"} true;
call arbitrary_func();

label_0x33a:
R8 := (0bv32 ++ 1bv32);

label_0x340:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x348:
RDX := (0bv32 ++ RAX[32:0]);

label_0x34a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x352:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x356:

target_193 := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 861bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_193"} true;
call arbitrary_func();

label_0x35d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RAX);

label_0x365:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x36a:
t1_195 := RAX;
t2_196 := 24bv64;
RAX := PLUS_64(RAX, t2_196);
CF := bool2bv(LT_64(RAX, t1_195));
OF := AND_1((bool2bv((t1_195[64:63]) == (t2_196[64:63]))), (XOR_1((t1_195[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_195)), t2_196)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x36e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x373:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x378:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x383:
t_203 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)), 2bv64)), (XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)), 2bv64)), (XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)))))[1:0]));
SF := t_203[64:63];
ZF := bool2bv(0bv64 == t_203);

label_0x386:
if (bv2bool(ZF)) {
  goto label_0x389;
}

label_0x388:
assume false;

label_0x389:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x38e:
origDEST_207 := RAX;
origCOUNT_208 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, LSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), origDEST_207[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_71);

label_0x392:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x399:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x39d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3a2:
origDEST_213 := RCX;
origCOUNT_214 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_73);

label_0x3a6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x3aa:
if (bv2bool(CF)) {
  goto label_0x3ad;
}

label_0x3ac:
assume false;

label_0x3ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3b2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x3ba:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3bd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x3c1:
t1_219 := RAX[32:0];
t2_220 := 34bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_220));
CF := bool2bv(LT_32((RAX[32:0]), t1_219));
OF := AND_1((bool2bv((t1_219[32:31]) == (t2_220[32:31]))), (XOR_1((t1_219[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_219)), t2_220)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3c4:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3c6:
origDEST_225 := RAX;
origCOUNT_226 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), CF, RSHIFT_64(origDEST_225, (MINUS_64(64bv64, origCOUNT_226)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_226 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), AF, unconstrained_79);

label_0x3ca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 344bv64), RAX);

label_0x3d2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x3da:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 56bv64));

label_0x3de:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RCX);

label_0x3e6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x3ee:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1011bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3f3"} true;
call arbitrary_func();

label_0x3f3:
R8 := (0bv32 ++ 1bv32);

label_0x3f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x401:
RDX := (0bv32 ++ RAX[32:0]);

label_0x403:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x40b:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x40f:

target_231 := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1046bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_231"} true;
call arbitrary_func();

label_0x416:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RAX);

label_0x41e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x423:
t1_233 := RAX;
t2_234 := 32bv64;
RAX := PLUS_64(RAX, t2_234);
CF := bool2bv(LT_64(RAX, t1_233));
OF := AND_1((bool2bv((t1_233[64:63]) == (t2_234[64:63]))), (XOR_1((t1_233[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_233)), t2_234)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x427:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x42c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x431:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_80;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x437:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x43c:
t_241 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))))[1:0]));
SF := t_241[64:63];
ZF := bool2bv(0bv64 == t_241);

label_0x43f:
if (bv2bool(ZF)) {
  goto label_0x442;
}

label_0x441:
assume false;

label_0x442:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x447:
origDEST_245 := RAX;
origCOUNT_246 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_83);

label_0x44b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x452:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x456:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x45b:
origDEST_251 := RCX;
origCOUNT_252 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), CF, LSHIFT_64(origDEST_251, (MINUS_64(64bv64, origCOUNT_252)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv64)), origDEST_251[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), AF, unconstrained_85);

label_0x45f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_86;
SF := unconstrained_87;
AF := unconstrained_88;
PF := unconstrained_89;

label_0x463:
if (bv2bool(CF)) {
  goto label_0x466;
}

label_0x465:
assume false;

label_0x466:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x46b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x473:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x476:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x47e:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 56bv64));

label_0x482:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0x48a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x492:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1175bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x497"} true;
call arbitrary_func();

label_0x497:
R8 := (0bv32 ++ 1bv32);

label_0x49d:
RDX := (0bv32 ++ 262148bv32);

label_0x4a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x4aa:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x4ae:

target_257 := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1205bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_257"} true;
call arbitrary_func();

label_0x4b5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0x4bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4c2:
t1_259 := RAX;
t2_260 := 40bv64;
RAX := PLUS_64(RAX, t2_260);
CF := bool2bv(LT_64(RAX, t1_259));
OF := AND_1((bool2bv((t1_259[64:63]) == (t2_260[64:63]))), (XOR_1((t1_259[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_259)), t2_260)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x4cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4d0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4db:
t_267 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_267, 4bv64)), t_267)), 2bv64)), (XOR_64((RSHIFT_64(t_267, 4bv64)), t_267)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_267, 4bv64)), t_267)), 2bv64)), (XOR_64((RSHIFT_64(t_267, 4bv64)), t_267)))))[1:0]));
SF := t_267[64:63];
ZF := bool2bv(0bv64 == t_267);

label_0x4de:
if (bv2bool(ZF)) {
  goto label_0x4e1;
}

label_0x4e0:
assume false;

label_0x4e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4e6:
origDEST_271 := RAX;
origCOUNT_272 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), CF, LSHIFT_64(origDEST_271, (MINUS_64(64bv64, origCOUNT_272)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_272 == 1bv64)), origDEST_271[64:63], unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), AF, unconstrained_93);

label_0x4ea:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4f1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4fa:
origDEST_277 := RCX;
origCOUNT_278 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), CF, LSHIFT_64(origDEST_277, (MINUS_64(64bv64, origCOUNT_278)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_278 == 1bv64)), origDEST_277[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), AF, unconstrained_95);

label_0x4fe:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_96;
SF := unconstrained_97;
AF := unconstrained_98;
PF := unconstrained_99;

label_0x502:
if (bv2bool(CF)) {
  goto label_0x505;
}

label_0x504:
assume false;

label_0x505:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x50a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x512:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x515:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x51a:
t_283 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), t_283)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_283, (LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_283, 4bv64)), t_283)), 2bv64)), (XOR_64((RSHIFT_64(t_283, 4bv64)), t_283)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_283, 4bv64)), t_283)), 2bv64)), (XOR_64((RSHIFT_64(t_283, 4bv64)), t_283)))))[1:0]));
SF := t_283[64:63];
ZF := bool2bv(0bv64 == t_283);

label_0x51f:
if (bv2bool(ZF)) {
  goto label_0x53d;
}

label_0x521:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x526:
t_287 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), t_287)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_287, (LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x52b:
if (bv2bool(ZF)) {
  goto label_0x53d;
}

label_0x52d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x532:
t_291 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), t_291)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_291, (LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_291, 4bv64)), t_291)), 2bv64)), (XOR_64((RSHIFT_64(t_291, 4bv64)), t_291)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_291, 4bv64)), t_291)), 2bv64)), (XOR_64((RSHIFT_64(t_291, 4bv64)), t_291)))))[1:0]));
SF := t_291[64:63];
ZF := bool2bv(0bv64 == t_291);

label_0x537:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x663;
}

label_0x53d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x542:
t_295 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))), t_295)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_295, (LOAD_LE_64(mem, PLUS_64(RAX, 24bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)), 2bv64)), (XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)), 2bv64)), (XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)))))[1:0]));
SF := t_295[64:63];
ZF := bool2bv(0bv64 == t_295);

label_0x547:
if (bv2bool(ZF)) {
  goto label_0x586;
}

label_0x549:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x551:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 64bv64));

label_0x555:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0x55d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x565:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1386bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x56a"} true;
call arbitrary_func();

label_0x56a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x56f:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0x573:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x57b:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x57f:

target_299 := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1414bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_299"} true;
call arbitrary_func();

label_0x586:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x58b:
t_301 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))), t_301)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_301, (LOAD_LE_64(mem, PLUS_64(RAX, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_301, 4bv64)), t_301)), 2bv64)), (XOR_64((RSHIFT_64(t_301, 4bv64)), t_301)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_301, 4bv64)), t_301)), 2bv64)), (XOR_64((RSHIFT_64(t_301, 4bv64)), t_301)))))[1:0]));
SF := t_301[64:63];
ZF := bool2bv(0bv64 == t_301);

label_0x590:
if (bv2bool(ZF)) {
  goto label_0x5cf;
}

label_0x592:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x59a:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 64bv64));

label_0x59e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0x5a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x5ae:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1459bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5b3"} true;
call arbitrary_func();

label_0x5b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5b8:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 32bv64));

label_0x5bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x5c4:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x5c8:

target_305 := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1487bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_305"} true;
call arbitrary_func();

label_0x5cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5d4:
t_307 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))), t_307)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_307, (LOAD_LE_64(mem, PLUS_64(RAX, 40bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_307, 4bv64)), t_307)), 2bv64)), (XOR_64((RSHIFT_64(t_307, 4bv64)), t_307)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_307, 4bv64)), t_307)), 2bv64)), (XOR_64((RSHIFT_64(t_307, 4bv64)), t_307)))))[1:0]));
SF := t_307[64:63];
ZF := bool2bv(0bv64 == t_307);

label_0x5d9:
if (bv2bool(ZF)) {
  goto label_0x618;
}

label_0x5db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x5e3:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 64bv64));

label_0x5e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RAX);

label_0x5ef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x5f7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1532bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5fc"} true;
call arbitrary_func();

label_0x5fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x601:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 40bv64));

label_0x605:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x60d:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x611:

target_311 := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1560bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_311"} true;
call arbitrary_func();

label_0x618:
t_313 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_313)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_313, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)), 2bv64)), (XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)), 2bv64)), (XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)))))[1:0]));
SF := t_313[64:63];
ZF := bool2bv(0bv64 == t_313);

label_0x61e:
if (bv2bool(ZF)) {
  goto label_0x659;
}

label_0x620:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x628:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 64bv64));

label_0x62c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 320bv64), RAX);

label_0x634:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x63c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1601bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x641"} true;
call arbitrary_func();

label_0x641:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x646:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x64e:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 72bv64));

label_0x652:

target_317 := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1625bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_317"} true;
call arbitrary_func();

label_0x659:
RAX := (0bv32 ++ 4294967293bv32);

label_0x65e:
goto label_0xd6f;

label_0x663:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x668:
t1_319 := RAX;
t2_320 := 660bv64;
RAX := PLUS_64(RAX, t2_320);
CF := bool2bv(LT_64(RAX, t1_319));
OF := AND_1((bool2bv((t1_319[64:63]) == (t2_320[64:63]))), (XOR_1((t1_319[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_319)), t2_320)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x66e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x676:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x67e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x684:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x689:
t_327 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_327, 4bv64)), t_327)), 2bv64)), (XOR_64((RSHIFT_64(t_327, 4bv64)), t_327)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_327, 4bv64)), t_327)), 2bv64)), (XOR_64((RSHIFT_64(t_327, 4bv64)), t_327)))))[1:0]));
SF := t_327[64:63];
ZF := bool2bv(0bv64 == t_327);

label_0x68c:
if (bv2bool(ZF)) {
  goto label_0x68f;
}

label_0x68e:
assume false;

label_0x68f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x697:
origDEST_331 := RAX;
origCOUNT_332 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), CF, LSHIFT_64(origDEST_331, (MINUS_64(64bv64, origCOUNT_332)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_332 == 1bv64)), origDEST_331[64:63], unconstrained_102));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), AF, unconstrained_103);

label_0x69b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6a2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6ae:
origDEST_337 := RCX;
origCOUNT_338 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), CF, LSHIFT_64(origDEST_337, (MINUS_64(64bv64, origCOUNT_338)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_338 == 1bv64)), origDEST_337[64:63], unconstrained_104));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), AF, unconstrained_105);

label_0x6b2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_106;
SF := unconstrained_107;
AF := unconstrained_108;
PF := unconstrained_109;

label_0x6b6:
if (bv2bool(CF)) {
  goto label_0x6b9;
}

label_0x6b8:
assume false;

label_0x6b9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6c1:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x6c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x6cc:
t1_343 := RAX;
t2_344 := 12bv64;
RAX := PLUS_64(RAX, t2_344);
CF := bool2bv(LT_64(RAX, t1_343));
OF := AND_1((bool2bv((t1_343[64:63]) == (t2_344[64:63]))), (XOR_1((t1_343[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_343)), t2_344)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6d0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x6d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6e0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_110;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6eb:
t_351 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_111;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)), 2bv64)), (XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)), 2bv64)), (XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)))))[1:0]));
SF := t_351[64:63];
ZF := bool2bv(0bv64 == t_351);

label_0x6ee:
if (bv2bool(ZF)) {
  goto label_0x6f1;
}

label_0x6f0:
assume false;

label_0x6f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6f9:
origDEST_355 := RAX;
origCOUNT_356 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), CF, LSHIFT_64(origDEST_355, (MINUS_64(64bv64, origCOUNT_356)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_356 == 1bv64)), origDEST_355[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), AF, unconstrained_113);

label_0x6fd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x704:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x708:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x710:
origDEST_361 := RCX;
origCOUNT_362 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), CF, LSHIFT_64(origDEST_361, (MINUS_64(64bv64, origCOUNT_362)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_362 == 1bv64)), origDEST_361[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), AF, unconstrained_115);

label_0x714:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_116;
SF := unconstrained_117;
AF := unconstrained_118;
PF := unconstrained_119;

label_0x718:
if (bv2bool(CF)) {
  goto label_0x71b;
}

label_0x71a:
assume false;

label_0x71b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x723:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0x729:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x72e:
t1_367 := RAX;
t2_368 := 8bv64;
RAX := PLUS_64(RAX, t2_368);
CF := bool2bv(LT_64(RAX, t1_367));
OF := AND_1((bool2bv((t1_367[64:63]) == (t2_368[64:63]))), (XOR_1((t1_367[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_367)), t2_368)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x732:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x73a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x742:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_120;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x748:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x74d:
t_375 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_121;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)), 2bv64)), (XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)), 2bv64)), (XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)))))[1:0]));
SF := t_375[64:63];
ZF := bool2bv(0bv64 == t_375);

label_0x750:
if (bv2bool(ZF)) {
  goto label_0x753;
}

label_0x752:
assume false;

label_0x753:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x75b:
origDEST_379 := RAX;
origCOUNT_380 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), CF, LSHIFT_64(origDEST_379, (MINUS_64(64bv64, origCOUNT_380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_380 == 1bv64)), origDEST_379[64:63], unconstrained_122));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), AF, unconstrained_123);

label_0x75f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x766:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x76a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x772:
origDEST_385 := RCX;
origCOUNT_386 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), CF, LSHIFT_64(origDEST_385, (MINUS_64(64bv64, origCOUNT_386)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_386 == 1bv64)), origDEST_385[64:63], unconstrained_124));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), AF, unconstrained_125);

label_0x776:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_126;
SF := unconstrained_127;
AF := unconstrained_128;
PF := unconstrained_129;

label_0x77a:
if (bv2bool(CF)) {
  goto label_0x77d;
}

label_0x77c:
assume false;

label_0x77d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x785:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0x78b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x790:
t1_391 := RAX;
t2_392 := 652bv64;
RAX := PLUS_64(RAX, t2_392);
CF := bool2bv(LT_64(RAX, t1_391));
OF := AND_1((bool2bv((t1_391[64:63]) == (t2_392[64:63]))), (XOR_1((t1_391[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_391)), t2_392)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x796:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x79e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7a6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_130;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7ac:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7b1:
t_399 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_131;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_399, 4bv64)), t_399)), 2bv64)), (XOR_64((RSHIFT_64(t_399, 4bv64)), t_399)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_399, 4bv64)), t_399)), 2bv64)), (XOR_64((RSHIFT_64(t_399, 4bv64)), t_399)))))[1:0]));
SF := t_399[64:63];
ZF := bool2bv(0bv64 == t_399);

label_0x7b4:
if (bv2bool(ZF)) {
  goto label_0x7b7;
}

label_0x7b6:
assume false;

label_0x7b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7bf:
origDEST_403 := RAX;
origCOUNT_404 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), CF, LSHIFT_64(origDEST_403, (MINUS_64(64bv64, origCOUNT_404)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_404 == 1bv64)), origDEST_403[64:63], unconstrained_132));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), AF, unconstrained_133);

label_0x7c3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7ca:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7ce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7d6:
origDEST_409 := RCX;
origCOUNT_410 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), CF, LSHIFT_64(origDEST_409, (MINUS_64(64bv64, origCOUNT_410)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_410 == 1bv64)), origDEST_409[64:63], unconstrained_134));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_410 == 0bv64)), AF, unconstrained_135);

label_0x7da:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_136;
SF := unconstrained_137;
AF := unconstrained_138;
PF := unconstrained_139;

label_0x7de:
if (bv2bool(CF)) {
  goto label_0x7e1;
}

label_0x7e0:
assume false;

label_0x7e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7e9:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x7ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x7f4:
t1_415 := RAX;
t2_416 := 664bv64;
RAX := PLUS_64(RAX, t2_416);
CF := bool2bv(LT_64(RAX, t1_415));
OF := AND_1((bool2bv((t1_415[64:63]) == (t2_416[64:63]))), (XOR_1((t1_415[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_415)), t2_416)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x802:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x80a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_140;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x810:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x815:
t_423 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_141;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)), 2bv64)), (XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)), 2bv64)), (XOR_64((RSHIFT_64(t_423, 4bv64)), t_423)))))[1:0]));
SF := t_423[64:63];
ZF := bool2bv(0bv64 == t_423);

label_0x818:
if (bv2bool(ZF)) {
  goto label_0x81b;
}

label_0x81a:
assume false;

label_0x81b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x823:
origDEST_427 := RAX;
origCOUNT_428 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), CF, LSHIFT_64(origDEST_427, (MINUS_64(64bv64, origCOUNT_428)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_428 == 1bv64)), origDEST_427[64:63], unconstrained_142));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), AF, unconstrained_143);

label_0x827:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x82e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x832:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x83a:
origDEST_433 := RCX;
origCOUNT_434 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), CF, LSHIFT_64(origDEST_433, (MINUS_64(64bv64, origCOUNT_434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_434 == 1bv64)), origDEST_433[64:63], unconstrained_144));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), AF, unconstrained_145);

label_0x83e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_146;
SF := unconstrained_147;
AF := unconstrained_148;
PF := unconstrained_149;

label_0x842:
if (bv2bool(CF)) {
  goto label_0x845;
}

label_0x844:
assume false;

label_0x845:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x84d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 424bv64)));

label_0x854:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x856:
t_439 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 424bv64)))))), ((ITE_64(bv2bool(100000bv32[32:31]) ,(1bv32 ++ 100000bv32) ,(0bv32 ++ 100000bv32)))));
RAX := (0bv32 ++ t_439[32:0]);
OF := bool2bv(t_439 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_439 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_150;
SF := unconstrained_151;
ZF := unconstrained_152;
AF := unconstrained_153;

label_0x861:
t_441 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 19bv32));
CF := bool2bv(LT_32(t_441, 19bv32));
OF := AND_32((XOR_32(t_441, 19bv32)), (XOR_32(t_441, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_441)), 19bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x864:
mem := STORE_LE_32(mem, PLUS_64(RSP, 256bv64), RAX[32:0]);

label_0x86b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x870:
t1_445 := RAX;
t2_446 := 112bv64;
RAX := PLUS_64(RAX, t2_446);
CF := bool2bv(LT_64(RAX, t1_445));
OF := AND_1((bool2bv((t1_445[64:63]) == (t2_446[64:63]))), (XOR_1((t1_445[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_445)), t2_446)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x874:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x87c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x884:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_154;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x88a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x88f:
t_453 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_155;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)), 2bv64)), (XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)), 2bv64)), (XOR_64((RSHIFT_64(t_453, 4bv64)), t_453)))))[1:0]));
SF := t_453[64:63];
ZF := bool2bv(0bv64 == t_453);

label_0x892:
if (bv2bool(ZF)) {
  goto label_0x895;
}

label_0x894:
assume false;

label_0x895:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x89d:
origDEST_457 := RAX;
origCOUNT_458 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), CF, LSHIFT_64(origDEST_457, (MINUS_64(64bv64, origCOUNT_458)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_458 == 1bv64)), origDEST_457[64:63], unconstrained_156));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), AF, unconstrained_157);

label_0x8a1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8a8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8ac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x8b4:
origDEST_463 := RCX;
origCOUNT_464 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), CF, LSHIFT_64(origDEST_463, (MINUS_64(64bv64, origCOUNT_464)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_464 == 1bv64)), origDEST_463[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), AF, unconstrained_159);

label_0x8b8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_160;
SF := unconstrained_161;
AF := unconstrained_162;
PF := unconstrained_163;

label_0x8bc:
if (bv2bool(CF)) {
  goto label_0x8bf;
}

label_0x8be:
assume false;

label_0x8bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x8c7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 256bv64)));

label_0x8ce:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x8d5:
t1_469 := RAX;
t2_470 := 656bv64;
RAX := PLUS_64(RAX, t2_470);
CF := bool2bv(LT_64(RAX, t1_469));
OF := AND_1((bool2bv((t1_469[64:63]) == (t2_470[64:63]))), (XOR_1((t1_469[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_469)), t2_470)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8db:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x8e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x8eb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_164;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8f1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8f6:
t_477 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_165;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)), 2bv64)), (XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)), 2bv64)), (XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)))))[1:0]));
SF := t_477[64:63];
ZF := bool2bv(0bv64 == t_477);

label_0x8f9:
if (bv2bool(ZF)) {
  goto label_0x8fc;
}

label_0x8fb:
assume false;

label_0x8fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x904:
origDEST_481 := RAX;
origCOUNT_482 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), CF, LSHIFT_64(origDEST_481, (MINUS_64(64bv64, origCOUNT_482)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_482 == 1bv64)), origDEST_481[64:63], unconstrained_166));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), AF, unconstrained_167);

label_0x908:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x90f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x913:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x91b:
origDEST_487 := RCX;
origCOUNT_488 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), CF, LSHIFT_64(origDEST_487, (MINUS_64(64bv64, origCOUNT_488)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_488 == 1bv64)), origDEST_487[64:63], unconstrained_168));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), AF, unconstrained_169);

label_0x91f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_170;
SF := unconstrained_171;
AF := unconstrained_172;
PF := unconstrained_173;

label_0x923:
if (bv2bool(CF)) {
  goto label_0x926;
}

label_0x925:
assume false;

label_0x926:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x92e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 432bv64)));

label_0x935:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x937:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x93c:
t1_493 := RAX;
t2_494 := 88bv64;
RAX := PLUS_64(RAX, t2_494);
CF := bool2bv(LT_64(RAX, t1_493));
OF := AND_1((bool2bv((t1_493[64:63]) == (t2_494[64:63]))), (XOR_1((t1_493[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_493)), t2_494)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x940:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x948:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x950:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_174;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x956:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x95b:
t_501 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_175;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))))[1:0]));
SF := t_501[64:63];
ZF := bool2bv(0bv64 == t_501);

label_0x95e:
if (bv2bool(ZF)) {
  goto label_0x961;
}

label_0x960:
assume false;

label_0x961:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x969:
origDEST_505 := RAX;
origCOUNT_506 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), CF, LSHIFT_64(origDEST_505, (MINUS_64(64bv64, origCOUNT_506)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_506 == 1bv64)), origDEST_505[64:63], unconstrained_176));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), AF, unconstrained_177);

label_0x96d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x974:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x978:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x980:
origDEST_511 := RCX;
origCOUNT_512 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), CF, LSHIFT_64(origDEST_511, (MINUS_64(64bv64, origCOUNT_512)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_512 == 1bv64)), origDEST_511[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), AF, unconstrained_179);

label_0x984:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_180;
SF := unconstrained_181;
AF := unconstrained_182;
PF := unconstrained_183;

label_0x988:
if (bv2bool(CF)) {
  goto label_0x98b;
}

label_0x98a:
assume false;

label_0x98b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x993:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x997:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x999:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x99e:
t1_517 := RAX;
t2_518 := 32bv64;
RAX := PLUS_64(RAX, t2_518);
CF := bool2bv(LT_64(RAX, t1_517));
OF := AND_1((bool2bv((t1_517[64:63]) == (t2_518[64:63]))), (XOR_1((t1_517[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_517)), t2_518)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RAX);

label_0x9aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x9af:
t1_523 := RAX;
t2_524 := 64bv64;
RAX := PLUS_64(RAX, t2_524);
CF := bool2bv(LT_64(RAX, t1_523));
OF := AND_1((bool2bv((t1_523[64:63]) == (t2_524[64:63]))), (XOR_1((t1_523[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_523)), t2_524)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9b3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x9bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x9c3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_184;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9c9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9ce:
t_531 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_185;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))))[1:0]));
SF := t_531[64:63];
ZF := bool2bv(0bv64 == t_531);

label_0x9d1:
if (bv2bool(ZF)) {
  goto label_0x9d4;
}

label_0x9d3:
assume false;

label_0x9d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x9dc:
origDEST_535 := RAX;
origCOUNT_536 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), CF, LSHIFT_64(origDEST_535, (MINUS_64(64bv64, origCOUNT_536)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_536 == 1bv64)), origDEST_535[64:63], unconstrained_186));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), AF, unconstrained_187);

label_0x9e0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9e7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x9f3:
origDEST_541 := RCX;
origCOUNT_542 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), CF, LSHIFT_64(origDEST_541, (MINUS_64(64bv64, origCOUNT_542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_542 == 1bv64)), origDEST_541[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), AF, unconstrained_189);

label_0x9f7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_190;
SF := unconstrained_191;
AF := unconstrained_192;
PF := unconstrained_193;

label_0x9fb:
if (bv2bool(CF)) {
  goto label_0x9fe;
}

label_0x9fd:
assume false;

label_0x9fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xa06:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xa0e:
RCX := LOAD_LE_64(mem, RCX);

label_0xa11:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xa14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xa19:
t1_547 := RAX;
t2_548 := 24bv64;
RAX := PLUS_64(RAX, t2_548);
CF := bool2bv(LT_64(RAX, t1_547));
OF := AND_1((bool2bv((t1_547[64:63]) == (t2_548[64:63]))), (XOR_1((t1_547[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_547)), t2_548)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa1d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 376bv64), RAX);

label_0xa25:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xa2a:
t1_553 := RAX;
t2_554 := 72bv64;
RAX := PLUS_64(RAX, t2_554);
CF := bool2bv(LT_64(RAX, t1_553));
OF := AND_1((bool2bv((t1_553[64:63]) == (t2_554[64:63]))), (XOR_1((t1_553[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_553)), t2_554)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa2e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0xa36:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa3e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_194;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa44:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa49:
t_561 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_195;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))))[1:0]));
SF := t_561[64:63];
ZF := bool2bv(0bv64 == t_561);

label_0xa4c:
if (bv2bool(ZF)) {
  goto label_0xa4f;
}

label_0xa4e:
assume false;

label_0xa4f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa57:
origDEST_565 := RAX;
origCOUNT_566 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), CF, LSHIFT_64(origDEST_565, (MINUS_64(64bv64, origCOUNT_566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_566 == 1bv64)), origDEST_565[64:63], unconstrained_196));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), AF, unconstrained_197);

label_0xa5b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa62:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa66:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa6e:
origDEST_571 := RCX;
origCOUNT_572 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), CF, LSHIFT_64(origDEST_571, (MINUS_64(64bv64, origCOUNT_572)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_572 == 1bv64)), origDEST_571[64:63], unconstrained_198));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), AF, unconstrained_199);

label_0xa72:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_200;
SF := unconstrained_201;
AF := unconstrained_202;
PF := unconstrained_203;

label_0xa76:
if (bv2bool(CF)) {
  goto label_0xa79;
}

label_0xa78:
assume false;

label_0xa79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xa81:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xa89:
RCX := LOAD_LE_64(mem, RCX);

label_0xa8c:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xa8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xa94:
t1_577 := RAX;
t2_578 := 80bv64;
RAX := PLUS_64(RAX, t2_578);
CF := bool2bv(LT_64(RAX, t1_577));
OF := AND_1((bool2bv((t1_577[64:63]) == (t2_578[64:63]))), (XOR_1((t1_577[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_577)), t2_578)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa98:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0xaa0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xaa8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_204;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaae:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xab3:
t_585 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_205;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))))[1:0]));
SF := t_585[64:63];
ZF := bool2bv(0bv64 == t_585);

label_0xab6:
if (bv2bool(ZF)) {
  goto label_0xab9;
}

label_0xab8:
assume false;

label_0xab9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xac1:
origDEST_589 := RAX;
origCOUNT_590 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, LSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), origDEST_589[64:63], unconstrained_206));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_207);

label_0xac5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xacc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xad0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xad8:
origDEST_595 := RCX;
origCOUNT_596 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), CF, LSHIFT_64(origDEST_595, (MINUS_64(64bv64, origCOUNT_596)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_596 == 1bv64)), origDEST_595[64:63], unconstrained_208));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), AF, unconstrained_209);

label_0xadc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_210;
SF := unconstrained_211;
AF := unconstrained_212;
PF := unconstrained_213;

label_0xae0:
if (bv2bool(CF)) {
  goto label_0xae3;
}

label_0xae2:
assume false;

label_0xae3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xaeb:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0xaf2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xaf7:
t1_601 := RAX;
t2_602 := 24bv64;
RAX := PLUS_64(RAX, t2_602);
CF := bool2bv(LT_64(RAX, t1_601));
OF := AND_1((bool2bv((t1_601[64:63]) == (t2_602[64:63]))), (XOR_1((t1_601[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_601)), t2_602)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xafb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 384bv64), RAX);

label_0xb03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xb08:
t1_607 := RAX;
t2_608 := 56bv64;
RAX := PLUS_64(RAX, t2_608);
CF := bool2bv(LT_64(RAX, t1_607));
OF := AND_1((bool2bv((t1_607[64:63]) == (t2_608[64:63]))), (XOR_1((t1_607[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_607)), t2_608)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb0c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0xb14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xb1c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_214;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb22:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb27:
t_615 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_215;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)), 2bv64)), (XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)), 2bv64)), (XOR_64((RSHIFT_64(t_615, 4bv64)), t_615)))))[1:0]));
SF := t_615[64:63];
ZF := bool2bv(0bv64 == t_615);

label_0xb2a:
if (bv2bool(ZF)) {
  goto label_0xb2d;
}

label_0xb2c:
assume false;

label_0xb2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xb35:
origDEST_619 := RAX;
origCOUNT_620 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), CF, LSHIFT_64(origDEST_619, (MINUS_64(64bv64, origCOUNT_620)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_620 == 1bv64)), origDEST_619[64:63], unconstrained_216));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), AF, unconstrained_217);

label_0xb39:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb40:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb44:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xb4c:
origDEST_625 := RCX;
origCOUNT_626 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), CF, LSHIFT_64(origDEST_625, (MINUS_64(64bv64, origCOUNT_626)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_626 == 1bv64)), origDEST_625[64:63], unconstrained_218));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_626 == 0bv64)), AF, unconstrained_219);

label_0xb50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_220;
SF := unconstrained_221;
AF := unconstrained_222;
PF := unconstrained_223;

label_0xb54:
if (bv2bool(CF)) {
  goto label_0xb57;
}

label_0xb56:
assume false;

label_0xb57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xb5f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0xb67:
RCX := LOAD_LE_64(mem, RCX);

label_0xb6a:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xb6d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xb75:
t1_631 := RAX;
t2_632 := 48bv64;
RAX := PLUS_64(RAX, t2_632);
CF := bool2bv(LT_64(RAX, t1_631));
OF := AND_1((bool2bv((t1_631[64:63]) == (t2_632[64:63]))), (XOR_1((t1_631[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_631)), t2_632)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb79:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0xb81:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xb89:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_224;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb8f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb94:
t_639 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_225;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))))[1:0]));
SF := t_639[64:63];
ZF := bool2bv(0bv64 == t_639);

label_0xb97:
if (bv2bool(ZF)) {
  goto label_0xb9a;
}

label_0xb99:
assume false;

label_0xb9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xba2:
origDEST_643 := RAX;
origCOUNT_644 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), CF, LSHIFT_64(origDEST_643, (MINUS_64(64bv64, origCOUNT_644)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_644 == 1bv64)), origDEST_643[64:63], unconstrained_226));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), AF, unconstrained_227);

label_0xba6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbad:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbb1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xbb9:
origDEST_649 := RCX;
origCOUNT_650 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), CF, LSHIFT_64(origDEST_649, (MINUS_64(64bv64, origCOUNT_650)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_650 == 1bv64)), origDEST_649[64:63], unconstrained_228));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), AF, unconstrained_229);

label_0xbbd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_230;
SF := unconstrained_231;
AF := unconstrained_232;
PF := unconstrained_233;

label_0xbc1:
if (bv2bool(CF)) {
  goto label_0xbc4;
}

label_0xbc3:
assume false;

label_0xbc4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xbcc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xbd1:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xbd4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xbdc:
t1_655 := RAX;
t2_656 := 12bv64;
RAX := PLUS_64(RAX, t2_656);
CF := bool2bv(LT_64(RAX, t1_655));
OF := AND_1((bool2bv((t1_655[64:63]) == (t2_656[64:63]))), (XOR_1((t1_655[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_655)), t2_656)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbe0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0xbe8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xbf0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_234;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbf6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbfb:
t_663 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_235;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)), 2bv64)), (XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)), 2bv64)), (XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)))))[1:0]));
SF := t_663[64:63];
ZF := bool2bv(0bv64 == t_663);

label_0xbfe:
if (bv2bool(ZF)) {
  goto label_0xc01;
}

label_0xc00:
assume false;

label_0xc01:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc09:
origDEST_667 := RAX;
origCOUNT_668 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), CF, LSHIFT_64(origDEST_667, (MINUS_64(64bv64, origCOUNT_668)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_668 == 1bv64)), origDEST_667[64:63], unconstrained_236));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), AF, unconstrained_237);

label_0xc0d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc14:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc18:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc20:
origDEST_673 := RCX;
origCOUNT_674 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), CF, LSHIFT_64(origDEST_673, (MINUS_64(64bv64, origCOUNT_674)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_674 == 1bv64)), origDEST_673[64:63], unconstrained_238));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), AF, unconstrained_239);

label_0xc24:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_240;
SF := unconstrained_241;
AF := unconstrained_242;
PF := unconstrained_243;

label_0xc28:
if (bv2bool(CF)) {
  goto label_0xc2b;
}

label_0xc2a:
assume false;

label_0xc2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc33:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xc39:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xc41:
t1_679 := RAX;
t2_680 := 16bv64;
RAX := PLUS_64(RAX, t2_680);
CF := bool2bv(LT_64(RAX, t1_679));
OF := AND_1((bool2bv((t1_679[64:63]) == (t2_680[64:63]))), (XOR_1((t1_679[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_679)), t2_680)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc45:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0xc4d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc55:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_244;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc5b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc60:
t_687 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_245;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_687, 4bv64)), t_687)), 2bv64)), (XOR_64((RSHIFT_64(t_687, 4bv64)), t_687)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_687, 4bv64)), t_687)), 2bv64)), (XOR_64((RSHIFT_64(t_687, 4bv64)), t_687)))))[1:0]));
SF := t_687[64:63];
ZF := bool2bv(0bv64 == t_687);

label_0xc63:
if (bv2bool(ZF)) {
  goto label_0xc66;
}

label_0xc65:
assume false;

label_0xc66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc6e:
origDEST_691 := RAX;
origCOUNT_692 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), CF, LSHIFT_64(origDEST_691, (MINUS_64(64bv64, origCOUNT_692)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_692 == 1bv64)), origDEST_691[64:63], unconstrained_246));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), AF, unconstrained_247);

label_0xc72:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc79:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc7d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc85:
origDEST_697 := RCX;
origCOUNT_698 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), CF, LSHIFT_64(origDEST_697, (MINUS_64(64bv64, origCOUNT_698)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_698 == 1bv64)), origDEST_697[64:63], unconstrained_248));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), AF, unconstrained_249);

label_0xc89:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_250;
SF := unconstrained_251;
AF := unconstrained_252;
PF := unconstrained_253;

label_0xc8d:
if (bv2bool(CF)) {
  goto label_0xc90;
}

label_0xc8f:
assume false;

label_0xc90:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc98:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xc9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xca6:
t1_703 := RAX;
t2_704 := 36bv64;
RAX := PLUS_64(RAX, t2_704);
CF := bool2bv(LT_64(RAX, t1_703));
OF := AND_1((bool2bv((t1_703[64:63]) == (t2_704[64:63]))), (XOR_1((t1_703[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_703)), t2_704)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcaa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0xcb2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xcba:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_254;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcc0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcc5:
t_711 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_255;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)), 2bv64)), (XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)), 2bv64)), (XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)))))[1:0]));
SF := t_711[64:63];
ZF := bool2bv(0bv64 == t_711);

label_0xcc8:
if (bv2bool(ZF)) {
  goto label_0xccb;
}

label_0xcca:
assume false;

label_0xccb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xcd3:
origDEST_715 := RAX;
origCOUNT_716 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), CF, LSHIFT_64(origDEST_715, (MINUS_64(64bv64, origCOUNT_716)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_716 == 1bv64)), origDEST_715[64:63], unconstrained_256));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), AF, unconstrained_257);

label_0xcd7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcde:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xce2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xcea:
origDEST_721 := RCX;
origCOUNT_722 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), CF, LSHIFT_64(origDEST_721, (MINUS_64(64bv64, origCOUNT_722)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_722 == 1bv64)), origDEST_721[64:63], unconstrained_258));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), AF, unconstrained_259);

label_0xcee:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_260;
SF := unconstrained_261;
AF := unconstrained_262;
PF := unconstrained_263;

label_0xcf2:
if (bv2bool(CF)) {
  goto label_0xcf5;
}

label_0xcf4:
assume false;

label_0xcf5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xcfd:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xd03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xd0b:
t1_727 := RAX;
t2_728 := 40bv64;
RAX := PLUS_64(RAX, t2_728);
CF := bool2bv(LT_64(RAX, t1_727));
OF := AND_1((bool2bv((t1_727[64:63]) == (t2_728[64:63]))), (XOR_1((t1_727[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_727)), t2_728)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd0f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0xd14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xd19:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_264;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd1f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd24:
t_735 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_265;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_735, 4bv64)), t_735)), 2bv64)), (XOR_64((RSHIFT_64(t_735, 4bv64)), t_735)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_735, 4bv64)), t_735)), 2bv64)), (XOR_64((RSHIFT_64(t_735, 4bv64)), t_735)))))[1:0]));
SF := t_735[64:63];
ZF := bool2bv(0bv64 == t_735);

label_0xd27:
if (bv2bool(ZF)) {
  goto label_0xd2a;
}

label_0xd29:
assume false;

label_0xd2a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xd2f:
origDEST_739 := RAX;
origCOUNT_740 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), CF, LSHIFT_64(origDEST_739, (MINUS_64(64bv64, origCOUNT_740)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_740 == 1bv64)), origDEST_739[64:63], unconstrained_266));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_740 == 0bv64)), AF, unconstrained_267);

label_0xd33:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd3a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xd43:
origDEST_745 := RCX;
origCOUNT_746 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), CF, LSHIFT_64(origDEST_745, (MINUS_64(64bv64, origCOUNT_746)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_746 == 1bv64)), origDEST_745[64:63], unconstrained_268));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), AF, unconstrained_269);

label_0xd47:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_270;
SF := unconstrained_271;
AF := unconstrained_272;
PF := unconstrained_273;

label_0xd4b:
if (bv2bool(CF)) {
  goto label_0xd4e;
}

label_0xd4d:
assume false;

label_0xd4e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xd53:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xd59:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xd5e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3427bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd63"} true;
call arbitrary_func();

label_0xd63:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xd68:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3437bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd6d"} true;
call arbitrary_func();

label_0xd6d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_274;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xd6f:
t1_751 := RSP;
t2_752 := 408bv64;
RSP := PLUS_64(RSP, t2_752);
CF := bool2bv(LT_64(RSP, t1_751));
OF := AND_1((bool2bv((t1_751[64:63]) == (t2_752[64:63]))), (XOR_1((t1_751[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_751)), t2_752)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xd76:

ra_757 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_102,origCOUNT_108,origCOUNT_126,origCOUNT_132,origCOUNT_150,origCOUNT_156,origCOUNT_174,origCOUNT_180,origCOUNT_188,origCOUNT_208,origCOUNT_214,origCOUNT_226,origCOUNT_246,origCOUNT_252,origCOUNT_272,origCOUNT_278,origCOUNT_332,origCOUNT_338,origCOUNT_356,origCOUNT_362,origCOUNT_380,origCOUNT_386,origCOUNT_404,origCOUNT_410,origCOUNT_428,origCOUNT_434,origCOUNT_458,origCOUNT_464,origCOUNT_482,origCOUNT_488,origCOUNT_50,origCOUNT_506,origCOUNT_512,origCOUNT_536,origCOUNT_542,origCOUNT_56,origCOUNT_566,origCOUNT_572,origCOUNT_590,origCOUNT_596,origCOUNT_620,origCOUNT_626,origCOUNT_644,origCOUNT_650,origCOUNT_668,origCOUNT_674,origCOUNT_692,origCOUNT_698,origCOUNT_716,origCOUNT_722,origCOUNT_740,origCOUNT_746,origCOUNT_78,origCOUNT_84,origDEST_101,origDEST_107,origDEST_125,origDEST_131,origDEST_149,origDEST_155,origDEST_173,origDEST_179,origDEST_187,origDEST_207,origDEST_213,origDEST_225,origDEST_245,origDEST_251,origDEST_271,origDEST_277,origDEST_331,origDEST_337,origDEST_355,origDEST_361,origDEST_379,origDEST_385,origDEST_403,origDEST_409,origDEST_427,origDEST_433,origDEST_457,origDEST_463,origDEST_481,origDEST_487,origDEST_49,origDEST_505,origDEST_511,origDEST_535,origDEST_541,origDEST_55,origDEST_565,origDEST_571,origDEST_589,origDEST_595,origDEST_619,origDEST_625,origDEST_643,origDEST_649,origDEST_667,origDEST_673,origDEST_691,origDEST_697,origDEST_715,origDEST_721,origDEST_739,origDEST_745,origDEST_77,origDEST_83,ra_757,t1_113,t1_137,t1_161,t1_195,t1_219,t1_233,t1_259,t1_319,t1_343,t1_367,t1_37,t1_391,t1_415,t1_445,t1_469,t1_493,t1_517,t1_523,t1_547,t1_553,t1_577,t1_601,t1_607,t1_631,t1_65,t1_655,t1_679,t1_703,t1_727,t1_751,t2_114,t2_138,t2_162,t2_196,t2_220,t2_234,t2_260,t2_320,t2_344,t2_368,t2_38,t2_392,t2_416,t2_446,t2_470,t2_494,t2_518,t2_524,t2_548,t2_554,t2_578,t2_602,t2_608,t2_632,t2_656,t2_66,t2_680,t2_704,t2_728,t2_752,t_1,t_121,t_13,t_145,t_169,t_17,t_185,t_203,t_21,t_241,t_25,t_267,t_283,t_287,t_29,t_291,t_295,t_301,t_307,t_313,t_327,t_33,t_351,t_375,t_399,t_423,t_439,t_441,t_45,t_453,t_477,t_5,t_501,t_531,t_561,t_585,t_61,t_615,t_639,t_663,t_687,t_711,t_73,t_735,t_9,t_91,t_97,target_193,target_231,target_257,target_299,target_305,target_311,target_317,target_89;

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
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_102: bv64;
var origCOUNT_108: bv64;
var origCOUNT_126: bv64;
var origCOUNT_132: bv64;
var origCOUNT_150: bv64;
var origCOUNT_156: bv64;
var origCOUNT_174: bv64;
var origCOUNT_180: bv64;
var origCOUNT_188: bv64;
var origCOUNT_208: bv64;
var origCOUNT_214: bv64;
var origCOUNT_226: bv64;
var origCOUNT_246: bv64;
var origCOUNT_252: bv64;
var origCOUNT_272: bv64;
var origCOUNT_278: bv64;
var origCOUNT_332: bv64;
var origCOUNT_338: bv64;
var origCOUNT_356: bv64;
var origCOUNT_362: bv64;
var origCOUNT_380: bv64;
var origCOUNT_386: bv64;
var origCOUNT_404: bv64;
var origCOUNT_410: bv64;
var origCOUNT_428: bv64;
var origCOUNT_434: bv64;
var origCOUNT_458: bv64;
var origCOUNT_464: bv64;
var origCOUNT_482: bv64;
var origCOUNT_488: bv64;
var origCOUNT_50: bv64;
var origCOUNT_506: bv64;
var origCOUNT_512: bv64;
var origCOUNT_536: bv64;
var origCOUNT_542: bv64;
var origCOUNT_56: bv64;
var origCOUNT_566: bv64;
var origCOUNT_572: bv64;
var origCOUNT_590: bv64;
var origCOUNT_596: bv64;
var origCOUNT_620: bv64;
var origCOUNT_626: bv64;
var origCOUNT_644: bv64;
var origCOUNT_650: bv64;
var origCOUNT_668: bv64;
var origCOUNT_674: bv64;
var origCOUNT_692: bv64;
var origCOUNT_698: bv64;
var origCOUNT_716: bv64;
var origCOUNT_722: bv64;
var origCOUNT_740: bv64;
var origCOUNT_746: bv64;
var origCOUNT_78: bv64;
var origCOUNT_84: bv64;
var origDEST_101: bv64;
var origDEST_107: bv64;
var origDEST_125: bv64;
var origDEST_131: bv64;
var origDEST_149: bv64;
var origDEST_155: bv64;
var origDEST_173: bv64;
var origDEST_179: bv64;
var origDEST_187: bv64;
var origDEST_207: bv64;
var origDEST_213: bv64;
var origDEST_225: bv64;
var origDEST_245: bv64;
var origDEST_251: bv64;
var origDEST_271: bv64;
var origDEST_277: bv64;
var origDEST_331: bv64;
var origDEST_337: bv64;
var origDEST_355: bv64;
var origDEST_361: bv64;
var origDEST_379: bv64;
var origDEST_385: bv64;
var origDEST_403: bv64;
var origDEST_409: bv64;
var origDEST_427: bv64;
var origDEST_433: bv64;
var origDEST_457: bv64;
var origDEST_463: bv64;
var origDEST_481: bv64;
var origDEST_487: bv64;
var origDEST_49: bv64;
var origDEST_505: bv64;
var origDEST_511: bv64;
var origDEST_535: bv64;
var origDEST_541: bv64;
var origDEST_55: bv64;
var origDEST_565: bv64;
var origDEST_571: bv64;
var origDEST_589: bv64;
var origDEST_595: bv64;
var origDEST_619: bv64;
var origDEST_625: bv64;
var origDEST_643: bv64;
var origDEST_649: bv64;
var origDEST_667: bv64;
var origDEST_673: bv64;
var origDEST_691: bv64;
var origDEST_697: bv64;
var origDEST_715: bv64;
var origDEST_721: bv64;
var origDEST_739: bv64;
var origDEST_745: bv64;
var origDEST_77: bv64;
var origDEST_83: bv64;
var ra_757: bv64;
var t1_113: bv64;
var t1_137: bv64;
var t1_161: bv64;
var t1_195: bv64;
var t1_219: bv32;
var t1_233: bv64;
var t1_259: bv64;
var t1_319: bv64;
var t1_343: bv64;
var t1_367: bv64;
var t1_37: bv64;
var t1_391: bv64;
var t1_415: bv64;
var t1_445: bv64;
var t1_469: bv64;
var t1_493: bv64;
var t1_517: bv64;
var t1_523: bv64;
var t1_547: bv64;
var t1_553: bv64;
var t1_577: bv64;
var t1_601: bv64;
var t1_607: bv64;
var t1_631: bv64;
var t1_65: bv64;
var t1_655: bv64;
var t1_679: bv64;
var t1_703: bv64;
var t1_727: bv64;
var t1_751: bv64;
var t2_114: bv64;
var t2_138: bv64;
var t2_162: bv64;
var t2_196: bv64;
var t2_220: bv32;
var t2_234: bv64;
var t2_260: bv64;
var t2_320: bv64;
var t2_344: bv64;
var t2_368: bv64;
var t2_38: bv64;
var t2_392: bv64;
var t2_416: bv64;
var t2_446: bv64;
var t2_470: bv64;
var t2_494: bv64;
var t2_518: bv64;
var t2_524: bv64;
var t2_548: bv64;
var t2_554: bv64;
var t2_578: bv64;
var t2_602: bv64;
var t2_608: bv64;
var t2_632: bv64;
var t2_656: bv64;
var t2_66: bv64;
var t2_680: bv64;
var t2_704: bv64;
var t2_728: bv64;
var t2_752: bv64;
var t_1: bv64;
var t_121: bv64;
var t_13: bv32;
var t_145: bv64;
var t_169: bv64;
var t_17: bv32;
var t_185: bv64;
var t_203: bv64;
var t_21: bv32;
var t_241: bv64;
var t_25: bv32;
var t_267: bv64;
var t_283: bv64;
var t_287: bv64;
var t_29: bv32;
var t_291: bv64;
var t_295: bv64;
var t_301: bv64;
var t_307: bv64;
var t_313: bv64;
var t_327: bv64;
var t_33: bv64;
var t_351: bv64;
var t_375: bv64;
var t_399: bv64;
var t_423: bv64;
var t_439: bv64;
var t_441: bv32;
var t_45: bv64;
var t_453: bv64;
var t_477: bv64;
var t_5: bv32;
var t_501: bv64;
var t_531: bv64;
var t_561: bv64;
var t_585: bv64;
var t_61: bv64;
var t_615: bv64;
var t_639: bv64;
var t_663: bv64;
var t_687: bv64;
var t_711: bv64;
var t_73: bv64;
var t_735: bv64;
var t_9: bv64;
var t_91: bv64;
var t_97: bv64;
var target_193: bv64;
var target_231: bv64;
var target_257: bv64;
var target_299: bv64;
var target_305: bv64;
var target_311: bv64;
var target_317: bv64;
var target_89: bv64;


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
