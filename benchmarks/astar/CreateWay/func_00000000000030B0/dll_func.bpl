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
axiom _function_addr_low == 12464bv64;
axiom _function_addr_high == 13536bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x30b0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x30b5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x30ba:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x30be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x30c3:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x30c7:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x30cc:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x30d0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x30d5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12506bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x30da"} true;
call arbitrary_func();

label_0x30da:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x30dd:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x30df:
if (bv2bool(ZF)) {
  goto label_0x30ff;
}

label_0x30e1:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x30e6:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x30ea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x30ef:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12532bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x30f4"} true;
call arbitrary_func();

label_0x30f4:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x30f7:
t_9 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x30f9:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x319d;
}

label_0x30ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3104:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x310a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x310f:
t_15 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))))[1:0]));
SF := t_15[64:63];
ZF := bool2bv(0bv64 == t_15);

label_0x3112:
if (bv2bool(ZF)) {
  goto label_0x3115;
}

label_0x3114:
assume false;

label_0x3115:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x311a:
origDEST_19 := RAX;
origCOUNT_20 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_6);

label_0x311e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3125:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3129:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x312e:
origDEST_25 := RCX;
origCOUNT_26 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, LSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), origDEST_25[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_8);

label_0x3132:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_9;
SF := unconstrained_10;
AF := unconstrained_11;
PF := unconstrained_12;

label_0x3136:
if (bv2bool(CF)) {
  goto label_0x3139;
}

label_0x3138:
assume false;

label_0x3139:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x313e:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x3145:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x314d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3153:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3158:
t_33 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x315b:
if (bv2bool(ZF)) {
  goto label_0x315e;
}

label_0x315d:
assume false;

label_0x315e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3166:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_16);

label_0x316a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3171:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3175:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x317d:
origDEST_43 := RCX;
origCOUNT_44 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_18);

label_0x3181:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_19;
SF := unconstrained_20;
AF := unconstrained_21;
PF := unconstrained_22;

label_0x3185:
if (bv2bool(CF)) {
  goto label_0x3188;
}

label_0x3187:
assume false;

label_0x3188:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3190:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3196:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_23;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3198:
goto label_0x34d1;

label_0x319d:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x31a2:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x31a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x31ab:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12720bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x31b0"} true;
call arbitrary_func();

label_0x31b0:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x31b3:
t_49 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))))[1:0]));
SF := t_49[32:31];
ZF := bool2bv(0bv32 == t_49);

label_0x31b5:
if (bv2bool(ZF)) {
  goto label_0x3259;
}

label_0x31bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x31c0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31c6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x31cb:
t_55 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))))[1:0]));
SF := t_55[64:63];
ZF := bool2bv(0bv64 == t_55);

label_0x31ce:
if (bv2bool(ZF)) {
  goto label_0x31d1;
}

label_0x31d0:
assume false;

label_0x31d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x31d6:
origDEST_59 := RAX;
origCOUNT_60 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_28);

label_0x31da:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x31e1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x31e5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x31ea:
origDEST_65 := RCX;
origCOUNT_66 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_30);

label_0x31ee:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x31f2:
if (bv2bool(CF)) {
  goto label_0x31f5;
}

label_0x31f4:
assume false;

label_0x31f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x31fa:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x3201:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3209:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x320f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3214:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0x3217:
if (bv2bool(ZF)) {
  goto label_0x321a;
}

label_0x3219:
assume false;

label_0x321a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3222:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_38);

label_0x3226:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x322d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3231:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3239:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_40);

label_0x323d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x3241:
if (bv2bool(CF)) {
  goto label_0x3244;
}

label_0x3243:
assume false;

label_0x3244:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x324c:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3252:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_45;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3254:
goto label_0x34d1;

label_0x3259:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x325d:
t_89 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), t_89)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_89, (LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))))[1:0]));
SF := t_89[32:31];
ZF := bool2bv(0bv32 == t_89);

label_0x3261:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3323;
}

label_0x3267:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x326b:
t_93 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_93)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_93, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))))[1:0]));
SF := t_93[32:31];
ZF := bool2bv(0bv32 == t_93);

label_0x326f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3323;
}

label_0x3275:
RCX := (0bv32 ++ 4bv32);

label_0x327a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12927bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x327f"} true;
call arbitrary_func();

label_0x327f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x3284:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3289:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x328f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3294:
t_99 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)), 2bv64)), (XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)), 2bv64)), (XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)))))[1:0]));
SF := t_99[64:63];
ZF := bool2bv(0bv64 == t_99);

label_0x3297:
if (bv2bool(ZF)) {
  goto label_0x329a;
}

label_0x3299:
assume false;

label_0x329a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x329f:
origDEST_103 := RAX;
origCOUNT_104 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_49);

label_0x32a3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x32aa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x32ae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x32b3:
origDEST_109 := RCX;
origCOUNT_110 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_51);

label_0x32b7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_52;
SF := unconstrained_53;
AF := unconstrained_54;
PF := unconstrained_55;

label_0x32bb:
if (bv2bool(CF)) {
  goto label_0x32be;
}

label_0x32bd:
assume false;

label_0x32be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x32c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x32c8:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x32cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x32d3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x32d9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x32de:
t_117 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x32e1:
if (bv2bool(ZF)) {
  goto label_0x32e4;
}

label_0x32e3:
assume false;

label_0x32e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x32ec:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_59);

label_0x32f0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x32f7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x32fb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3303:
origDEST_127 := RCX;
origCOUNT_128 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_61);

label_0x3307:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_62;
SF := unconstrained_63;
AF := unconstrained_64;
PF := unconstrained_65;

label_0x330b:
if (bv2bool(CF)) {
  goto label_0x330e;
}

label_0x330d:
assume false;

label_0x330e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3316:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x331c:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x331e:
goto label_0x34d1;

label_0x3323:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x3327:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x332b:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x3330:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x3335:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x3339:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x333e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13123bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3343"} true;
call arbitrary_func();

label_0x3343:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3346:
t_133 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0x3348:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x33ec;
}

label_0x334e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3353:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_67;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3359:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x335e:
t_139 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x3361:
if (bv2bool(ZF)) {
  goto label_0x3364;
}

label_0x3363:
assume false;

label_0x3364:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3369:
origDEST_143 := RAX;
origCOUNT_144 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_70);

label_0x336d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3374:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3378:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x337d:
origDEST_149 := RCX;
origCOUNT_150 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_72);

label_0x3381:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_73;
SF := unconstrained_74;
AF := unconstrained_75;
PF := unconstrained_76;

label_0x3385:
if (bv2bool(CF)) {
  goto label_0x3388;
}

label_0x3387:
assume false;

label_0x3388:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x338d:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x3394:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x339c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33a2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x33a7:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x33aa:
if (bv2bool(ZF)) {
  goto label_0x33ad;
}

label_0x33ac:
assume false;

label_0x33ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x33b5:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_80);

label_0x33b9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x33c0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x33c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x33cc:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_82);

label_0x33d0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x33d4:
if (bv2bool(CF)) {
  goto label_0x33d7;
}

label_0x33d6:
assume false;

label_0x33d7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x33df:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x33e5:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_87;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x33e7:
goto label_0x34d1;

label_0x33ec:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x33f1:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x33f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x33fa:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13311bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x33ff"} true;
call arbitrary_func();

label_0x33ff:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3407:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0x340c:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3411:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3416:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 164bv64)));

label_0x341d:
RDX := (0bv32 ++ RAX[32:0]);

label_0x341f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3424:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13353bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3429"} true;
call arbitrary_func();

label_0x3429:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x342c:
t_173 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_88;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))))[1:0]));
SF := t_173[32:31];
ZF := bool2bv(0bv32 == t_173);

label_0x342e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x34cf;
}

label_0x3434:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3439:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_89;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x343f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3444:
t_179 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))))[1:0]));
SF := t_179[64:63];
ZF := bool2bv(0bv64 == t_179);

label_0x3447:
if (bv2bool(ZF)) {
  goto label_0x344a;
}

label_0x3449:
assume false;

label_0x344a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x344f:
origDEST_183 := RAX;
origCOUNT_184 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_92);

label_0x3453:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x345a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x345e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3463:
origDEST_189 := RCX;
origCOUNT_190 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_94);

label_0x3467:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_95;
SF := unconstrained_96;
AF := unconstrained_97;
PF := unconstrained_98;

label_0x346b:
if (bv2bool(CF)) {
  goto label_0x346e;
}

label_0x346d:
assume false;

label_0x346e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3473:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x347a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3482:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_99;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3488:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x348d:
t_197 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))))[1:0]));
SF := t_197[64:63];
ZF := bool2bv(0bv64 == t_197);

label_0x3490:
if (bv2bool(ZF)) {
  goto label_0x3493;
}

label_0x3492:
assume false;

label_0x3493:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x349b:
origDEST_201 := RAX;
origCOUNT_202 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), CF, LSHIFT_64(origDEST_201, (MINUS_64(64bv64, origCOUNT_202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_202 == 1bv64)), origDEST_201[64:63], unconstrained_101));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), AF, unconstrained_102);

label_0x349f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x34a6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x34aa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x34b2:
origDEST_207 := RCX;
origCOUNT_208 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, LSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), origDEST_207[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_104);

label_0x34b6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_105;
SF := unconstrained_106;
AF := unconstrained_107;
PF := unconstrained_108;

label_0x34ba:
if (bv2bool(CF)) {
  goto label_0x34bd;
}

label_0x34bc:
assume false;

label_0x34bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x34c5:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x34cb:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_109;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x34cd:
goto label_0x34d1;

label_0x34cf:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x34d1:
t1_213 := RSP;
t2_214 := 72bv64;
RSP := PLUS_64(RSP, t2_214);
CF := bool2bv(LT_64(RSP, t1_213));
OF := AND_1((bool2bv((t1_213[64:63]) == (t2_214[64:63]))), (XOR_1((t1_213[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_213)), t2_214)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x34d5:

ra_219 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_110,origCOUNT_122,origCOUNT_128,origCOUNT_144,origCOUNT_150,origCOUNT_162,origCOUNT_168,origCOUNT_184,origCOUNT_190,origCOUNT_20,origCOUNT_202,origCOUNT_208,origCOUNT_26,origCOUNT_38,origCOUNT_44,origCOUNT_60,origCOUNT_66,origCOUNT_78,origCOUNT_84,origDEST_103,origDEST_109,origDEST_121,origDEST_127,origDEST_143,origDEST_149,origDEST_161,origDEST_167,origDEST_183,origDEST_189,origDEST_19,origDEST_201,origDEST_207,origDEST_25,origDEST_37,origDEST_43,origDEST_59,origDEST_65,origDEST_77,origDEST_83,ra_219,t1_213,t2_214,t_1,t_117,t_133,t_139,t_15,t_157,t_173,t_179,t_197,t_33,t_49,t_5,t_55,t_73,t_89,t_9,t_93,t_99;

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
var origCOUNT_104: bv64;
var origCOUNT_110: bv64;
var origCOUNT_122: bv64;
var origCOUNT_128: bv64;
var origCOUNT_144: bv64;
var origCOUNT_150: bv64;
var origCOUNT_162: bv64;
var origCOUNT_168: bv64;
var origCOUNT_184: bv64;
var origCOUNT_190: bv64;
var origCOUNT_20: bv64;
var origCOUNT_202: bv64;
var origCOUNT_208: bv64;
var origCOUNT_26: bv64;
var origCOUNT_38: bv64;
var origCOUNT_44: bv64;
var origCOUNT_60: bv64;
var origCOUNT_66: bv64;
var origCOUNT_78: bv64;
var origCOUNT_84: bv64;
var origDEST_103: bv64;
var origDEST_109: bv64;
var origDEST_121: bv64;
var origDEST_127: bv64;
var origDEST_143: bv64;
var origDEST_149: bv64;
var origDEST_161: bv64;
var origDEST_167: bv64;
var origDEST_183: bv64;
var origDEST_189: bv64;
var origDEST_19: bv64;
var origDEST_201: bv64;
var origDEST_207: bv64;
var origDEST_25: bv64;
var origDEST_37: bv64;
var origDEST_43: bv64;
var origDEST_59: bv64;
var origDEST_65: bv64;
var origDEST_77: bv64;
var origDEST_83: bv64;
var ra_219: bv64;
var t1_213: bv64;
var t2_214: bv64;
var t_1: bv64;
var t_117: bv64;
var t_133: bv32;
var t_139: bv64;
var t_15: bv64;
var t_157: bv64;
var t_173: bv32;
var t_179: bv64;
var t_197: bv64;
var t_33: bv64;
var t_49: bv32;
var t_5: bv32;
var t_55: bv64;
var t_73: bv64;
var t_89: bv32;
var t_9: bv32;
var t_93: bv32;
var t_99: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3584bv64);
axiom policy(6992bv64);
axiom policy(12288bv64);
axiom policy(12464bv64);
axiom policy(13536bv64);
axiom policy(18656bv64);
