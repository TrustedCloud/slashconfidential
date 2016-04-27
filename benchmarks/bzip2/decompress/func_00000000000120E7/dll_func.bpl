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
axiom _function_addr_low == 73959bv64;
axiom _function_addr_high == 76638bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x120e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x120ef:
t1_1 := RAX;
t2_2 := 64036bv64;
RAX := PLUS_64(RAX, t2_2);
CF := bool2bv(LT_64(RAX, t1_1));
OF := AND_1((bool2bv((t1_1[64:63]) == (t2_2[64:63]))), (XOR_1((t1_1[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1)), t2_2)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x120f5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7112bv64), RAX);

label_0x120fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7112bv64));

label_0x12105:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1210b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12110:
t_9 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x12113:
if (bv2bool(ZF)) {
  goto label_0x12116;
}

label_0x12115:
assume false;

label_0x12116:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7112bv64));

label_0x1211e:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x12122:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12129:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1212d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7112bv64));

label_0x12135:
origDEST_19 := RCX;
origCOUNT_20 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_6);

label_0x12139:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x1213d:
if (bv2bool(CF)) {
  goto label_0x12140;
}

label_0x1213f:
assume false;

label_0x12140:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7112bv64));

label_0x12148:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x1214f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12151:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12159:
t1_25 := RAX;
t2_26 := 64040bv64;
RAX := PLUS_64(RAX, t2_26);
CF := bool2bv(LT_64(RAX, t1_25));
OF := AND_1((bool2bv((t1_25[64:63]) == (t2_26[64:63]))), (XOR_1((t1_25[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_25)), t2_26)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1215f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7120bv64), RAX);

label_0x12167:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7120bv64));

label_0x1216f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12175:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1217a:
t_33 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x1217d:
if (bv2bool(ZF)) {
  goto label_0x12180;
}

label_0x1217f:
assume false;

label_0x12180:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7120bv64));

label_0x12188:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_14);

label_0x1218c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12193:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12197:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7120bv64));

label_0x1219f:
origDEST_43 := RCX;
origCOUNT_44 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_16);

label_0x121a3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x121a7:
if (bv2bool(CF)) {
  goto label_0x121aa;
}

label_0x121a9:
assume false;

label_0x121aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7120bv64));

label_0x121b2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x121b9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x121bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x121c3:
t1_49 := RAX;
t2_50 := 64044bv64;
RAX := PLUS_64(RAX, t2_50);
CF := bool2bv(LT_64(RAX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x121c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7128bv64), RAX);

label_0x121d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7128bv64));

label_0x121d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x121df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x121e4:
t_57 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0x121e7:
if (bv2bool(ZF)) {
  goto label_0x121ea;
}

label_0x121e9:
assume false;

label_0x121ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7128bv64));

label_0x121f2:
origDEST_61 := RAX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_24);

label_0x121f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x121fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12201:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7128bv64));

label_0x12209:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_26);

label_0x1220d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x12211:
if (bv2bool(CF)) {
  goto label_0x12214;
}

label_0x12213:
assume false;

label_0x12214:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7128bv64));

label_0x1221c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x12223:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12225:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1222d:
t1_73 := RAX;
t2_74 := 64048bv64;
RAX := PLUS_64(RAX, t2_74);
CF := bool2bv(LT_64(RAX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12233:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7136bv64), RAX);

label_0x1223b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7136bv64));

label_0x12243:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12249:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1224e:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0x12251:
if (bv2bool(ZF)) {
  goto label_0x12254;
}

label_0x12253:
assume false;

label_0x12254:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7136bv64));

label_0x1225c:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_34);

label_0x12260:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12267:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1226b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7136bv64));

label_0x12273:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_36);

label_0x12277:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x1227b:
if (bv2bool(CF)) {
  goto label_0x1227e;
}

label_0x1227d:
assume false;

label_0x1227e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7136bv64));

label_0x12286:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)));

label_0x1228d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1228f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12297:
t1_97 := RAX;
t2_98 := 64052bv64;
RAX := PLUS_64(RAX, t2_98);
CF := bool2bv(LT_64(RAX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1229d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7144bv64), RAX);

label_0x122a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7144bv64));

label_0x122ad:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x122b3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x122b8:
t_105 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))))[1:0]));
SF := t_105[64:63];
ZF := bool2bv(0bv64 == t_105);

label_0x122bb:
if (bv2bool(ZF)) {
  goto label_0x122be;
}

label_0x122bd:
assume false;

label_0x122be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7144bv64));

label_0x122c6:
origDEST_109 := RAX;
origCOUNT_110 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_44);

label_0x122ca:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x122d1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x122d5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7144bv64));

label_0x122dd:
origDEST_115 := RCX;
origCOUNT_116 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), CF, LSHIFT_64(origDEST_115, (MINUS_64(64bv64, origCOUNT_116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_116 == 1bv64)), origDEST_115[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), AF, unconstrained_46);

label_0x122e1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x122e5:
if (bv2bool(CF)) {
  goto label_0x122e8;
}

label_0x122e7:
assume false;

label_0x122e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7144bv64));

label_0x122f0:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x122f7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x122f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12301:
t1_121 := RAX;
t2_122 := 64056bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12307:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7152bv64), RAX);

label_0x1230f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7152bv64));

label_0x12317:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1231d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12322:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x12325:
if (bv2bool(ZF)) {
  goto label_0x12328;
}

label_0x12327:
assume false;

label_0x12328:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7152bv64));

label_0x12330:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_54);

label_0x12334:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1233b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1233f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7152bv64));

label_0x12347:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_56);

label_0x1234b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x1234f:
if (bv2bool(CF)) {
  goto label_0x12352;
}

label_0x12351:
assume false;

label_0x12352:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7152bv64));

label_0x1235a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 156bv64)));

label_0x12361:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12363:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1236b:
t1_145 := RAX;
t2_146 := 64060bv64;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12371:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7160bv64), RAX);

label_0x12379:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7160bv64));

label_0x12381:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12387:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1238c:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0x1238f:
if (bv2bool(ZF)) {
  goto label_0x12392;
}

label_0x12391:
assume false;

label_0x12392:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7160bv64));

label_0x1239a:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_64);

label_0x1239e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x123a5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x123a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7160bv64));

label_0x123b1:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_66);

label_0x123b5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x123b9:
if (bv2bool(CF)) {
  goto label_0x123bc;
}

label_0x123bb:
assume false;

label_0x123bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7160bv64));

label_0x123c4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x123cb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x123cd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x123d5:
t1_169 := RAX;
t2_170 := 64064bv64;
RAX := PLUS_64(RAX, t2_170);
CF := bool2bv(LT_64(RAX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x123db:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7168bv64), RAX);

label_0x123e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7168bv64));

label_0x123eb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x123f1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x123f6:
t_177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))))[1:0]));
SF := t_177[64:63];
ZF := bool2bv(0bv64 == t_177);

label_0x123f9:
if (bv2bool(ZF)) {
  goto label_0x123fc;
}

label_0x123fb:
assume false;

label_0x123fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7168bv64));

label_0x12404:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_74);

label_0x12408:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1240f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12413:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7168bv64));

label_0x1241b:
origDEST_187 := RCX;
origCOUNT_188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_76);

label_0x1241f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_77;
SF := unconstrained_78;
AF := unconstrained_79;
PF := unconstrained_80;

label_0x12423:
if (bv2bool(CF)) {
  goto label_0x12426;
}

label_0x12425:
assume false;

label_0x12426:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7168bv64));

label_0x1242e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 164bv64)));

label_0x12435:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12437:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1243f:
t1_193 := RAX;
t2_194 := 64068bv64;
RAX := PLUS_64(RAX, t2_194);
CF := bool2bv(LT_64(RAX, t1_193));
OF := AND_1((bool2bv((t1_193[64:63]) == (t2_194[64:63]))), (XOR_1((t1_193[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_193)), t2_194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12445:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7176bv64), RAX);

label_0x1244d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7176bv64));

label_0x12455:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1245b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12460:
t_201 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))))[1:0]));
SF := t_201[64:63];
ZF := bool2bv(0bv64 == t_201);

label_0x12463:
if (bv2bool(ZF)) {
  goto label_0x12466;
}

label_0x12465:
assume false;

label_0x12466:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7176bv64));

label_0x1246e:
origDEST_205 := RAX;
origCOUNT_206 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_83));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_84);

label_0x12472:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12479:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1247d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7176bv64));

label_0x12485:
origDEST_211 := RCX;
origCOUNT_212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), CF, LSHIFT_64(origDEST_211, (MINUS_64(64bv64, origCOUNT_212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv64)), origDEST_211[64:63], unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), AF, unconstrained_86);

label_0x12489:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_87;
SF := unconstrained_88;
AF := unconstrained_89;
PF := unconstrained_90;

label_0x1248d:
if (bv2bool(CF)) {
  goto label_0x12490;
}

label_0x1248f:
assume false;

label_0x12490:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7176bv64));

label_0x12498:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x1249f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x124a1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x124a9:
t1_217 := RAX;
t2_218 := 64072bv64;
RAX := PLUS_64(RAX, t2_218);
CF := bool2bv(LT_64(RAX, t1_217));
OF := AND_1((bool2bv((t1_217[64:63]) == (t2_218[64:63]))), (XOR_1((t1_217[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_217)), t2_218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x124af:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7184bv64), RAX);

label_0x124b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7184bv64));

label_0x124bf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x124c5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x124ca:
t_225 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))))[1:0]));
SF := t_225[64:63];
ZF := bool2bv(0bv64 == t_225);

label_0x124cd:
if (bv2bool(ZF)) {
  goto label_0x124d0;
}

label_0x124cf:
assume false;

label_0x124d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7184bv64));

label_0x124d8:
origDEST_229 := RAX;
origCOUNT_230 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), CF, LSHIFT_64(origDEST_229, (MINUS_64(64bv64, origCOUNT_230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_230 == 1bv64)), origDEST_229[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), AF, unconstrained_94);

label_0x124dc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x124e3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x124e7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7184bv64));

label_0x124ef:
origDEST_235 := RCX;
origCOUNT_236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), CF, LSHIFT_64(origDEST_235, (MINUS_64(64bv64, origCOUNT_236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv64)), origDEST_235[64:63], unconstrained_95));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), AF, unconstrained_96);

label_0x124f3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x124f7:
if (bv2bool(CF)) {
  goto label_0x124fa;
}

label_0x124f9:
assume false;

label_0x124fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7184bv64));

label_0x12502:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 172bv64)));

label_0x12509:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1250b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12513:
t1_241 := RAX;
t2_242 := 64076bv64;
RAX := PLUS_64(RAX, t2_242);
CF := bool2bv(LT_64(RAX, t1_241));
OF := AND_1((bool2bv((t1_241[64:63]) == (t2_242[64:63]))), (XOR_1((t1_241[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_241)), t2_242)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12519:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7192bv64), RAX);

label_0x12521:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7192bv64));

label_0x12529:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1252f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12534:
t_249 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)), 2bv64)), (XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)), 2bv64)), (XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)))))[1:0]));
SF := t_249[64:63];
ZF := bool2bv(0bv64 == t_249);

label_0x12537:
if (bv2bool(ZF)) {
  goto label_0x1253a;
}

label_0x12539:
assume false;

label_0x1253a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7192bv64));

label_0x12542:
origDEST_253 := RAX;
origCOUNT_254 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), CF, LSHIFT_64(origDEST_253, (MINUS_64(64bv64, origCOUNT_254)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_254 == 1bv64)), origDEST_253[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), AF, unconstrained_104);

label_0x12546:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1254d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12551:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7192bv64));

label_0x12559:
origDEST_259 := RCX;
origCOUNT_260 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), CF, LSHIFT_64(origDEST_259, (MINUS_64(64bv64, origCOUNT_260)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_260 == 1bv64)), origDEST_259[64:63], unconstrained_105));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), AF, unconstrained_106);

label_0x1255d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_107;
SF := unconstrained_108;
AF := unconstrained_109;
PF := unconstrained_110;

label_0x12561:
if (bv2bool(CF)) {
  goto label_0x12564;
}

label_0x12563:
assume false;

label_0x12564:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7192bv64));

label_0x1256c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x12573:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12575:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1257d:
t1_265 := RAX;
t2_266 := 64080bv64;
RAX := PLUS_64(RAX, t2_266);
CF := bool2bv(LT_64(RAX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12583:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7200bv64), RAX);

label_0x1258b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7200bv64));

label_0x12593:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_111;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12599:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1259e:
t_273 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_112;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))))[1:0]));
SF := t_273[64:63];
ZF := bool2bv(0bv64 == t_273);

label_0x125a1:
if (bv2bool(ZF)) {
  goto label_0x125a4;
}

label_0x125a3:
assume false;

label_0x125a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7200bv64));

label_0x125ac:
origDEST_277 := RAX;
origCOUNT_278 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), CF, LSHIFT_64(origDEST_277, (MINUS_64(64bv64, origCOUNT_278)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_278 == 1bv64)), origDEST_277[64:63], unconstrained_113));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), AF, unconstrained_114);

label_0x125b0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x125b7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x125bb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7200bv64));

label_0x125c3:
origDEST_283 := RCX;
origCOUNT_284 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), CF, LSHIFT_64(origDEST_283, (MINUS_64(64bv64, origCOUNT_284)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_284 == 1bv64)), origDEST_283[64:63], unconstrained_115));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), AF, unconstrained_116);

label_0x125c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_117;
SF := unconstrained_118;
AF := unconstrained_119;
PF := unconstrained_120;

label_0x125cb:
if (bv2bool(CF)) {
  goto label_0x125ce;
}

label_0x125cd:
assume false;

label_0x125ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7200bv64));

label_0x125d6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 180bv64)));

label_0x125dd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x125df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x125e7:
t1_289 := RAX;
t2_290 := 64084bv64;
RAX := PLUS_64(RAX, t2_290);
CF := bool2bv(LT_64(RAX, t1_289));
OF := AND_1((bool2bv((t1_289[64:63]) == (t2_290[64:63]))), (XOR_1((t1_289[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_289)), t2_290)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x125ed:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7208bv64), RAX);

label_0x125f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7208bv64));

label_0x125fd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_121;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12603:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12608:
t_297 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_122;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)), 2bv64)), (XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)), 2bv64)), (XOR_64((RSHIFT_64(t_297, 4bv64)), t_297)))))[1:0]));
SF := t_297[64:63];
ZF := bool2bv(0bv64 == t_297);

label_0x1260b:
if (bv2bool(ZF)) {
  goto label_0x1260e;
}

label_0x1260d:
assume false;

label_0x1260e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7208bv64));

label_0x12616:
origDEST_301 := RAX;
origCOUNT_302 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), CF, LSHIFT_64(origDEST_301, (MINUS_64(64bv64, origCOUNT_302)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_302 == 1bv64)), origDEST_301[64:63], unconstrained_123));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_302 == 0bv64)), AF, unconstrained_124);

label_0x1261a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12621:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12625:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7208bv64));

label_0x1262d:
origDEST_307 := RCX;
origCOUNT_308 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), CF, LSHIFT_64(origDEST_307, (MINUS_64(64bv64, origCOUNT_308)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_308 == 1bv64)), origDEST_307[64:63], unconstrained_125));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), AF, unconstrained_126);

label_0x12631:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_127;
SF := unconstrained_128;
AF := unconstrained_129;
PF := unconstrained_130;

label_0x12635:
if (bv2bool(CF)) {
  goto label_0x12638;
}

label_0x12637:
assume false;

label_0x12638:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7208bv64));

label_0x12640:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x12647:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12649:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12651:
t1_313 := RAX;
t2_314 := 64088bv64;
RAX := PLUS_64(RAX, t2_314);
CF := bool2bv(LT_64(RAX, t1_313));
OF := AND_1((bool2bv((t1_313[64:63]) == (t2_314[64:63]))), (XOR_1((t1_313[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_313)), t2_314)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12657:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7216bv64), RAX);

label_0x1265f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7216bv64));

label_0x12667:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_131;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1266d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12672:
t_321 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))))[1:0]));
SF := t_321[64:63];
ZF := bool2bv(0bv64 == t_321);

label_0x12675:
if (bv2bool(ZF)) {
  goto label_0x12678;
}

label_0x12677:
assume false;

label_0x12678:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7216bv64));

label_0x12680:
origDEST_325 := RAX;
origCOUNT_326 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_133));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_134);

label_0x12684:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1268b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1268f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7216bv64));

label_0x12697:
origDEST_331 := RCX;
origCOUNT_332 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), CF, LSHIFT_64(origDEST_331, (MINUS_64(64bv64, origCOUNT_332)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_332 == 1bv64)), origDEST_331[64:63], unconstrained_135));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), AF, unconstrained_136);

label_0x1269b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_137;
SF := unconstrained_138;
AF := unconstrained_139;
PF := unconstrained_140;

label_0x1269f:
if (bv2bool(CF)) {
  goto label_0x126a2;
}

label_0x126a1:
assume false;

label_0x126a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7216bv64));

label_0x126aa:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64)));

label_0x126b1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x126b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x126bb:
t1_337 := RAX;
t2_338 := 64092bv64;
RAX := PLUS_64(RAX, t2_338);
CF := bool2bv(LT_64(RAX, t1_337));
OF := AND_1((bool2bv((t1_337[64:63]) == (t2_338[64:63]))), (XOR_1((t1_337[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_337)), t2_338)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x126c1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7224bv64), RAX);

label_0x126c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7224bv64));

label_0x126d1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_141;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x126d7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x126dc:
t_345 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_142;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)), 2bv64)), (XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)), 2bv64)), (XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)))))[1:0]));
SF := t_345[64:63];
ZF := bool2bv(0bv64 == t_345);

label_0x126df:
if (bv2bool(ZF)) {
  goto label_0x126e2;
}

label_0x126e1:
assume false;

label_0x126e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7224bv64));

label_0x126ea:
origDEST_349 := RAX;
origCOUNT_350 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, LSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), origDEST_349[64:63], unconstrained_143));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_144);

label_0x126ee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x126f5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x126f9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7224bv64));

label_0x12701:
origDEST_355 := RCX;
origCOUNT_356 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), CF, LSHIFT_64(origDEST_355, (MINUS_64(64bv64, origCOUNT_356)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_356 == 1bv64)), origDEST_355[64:63], unconstrained_145));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), AF, unconstrained_146);

label_0x12705:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_147;
SF := unconstrained_148;
AF := unconstrained_149;
PF := unconstrained_150;

label_0x12709:
if (bv2bool(CF)) {
  goto label_0x1270c;
}

label_0x1270b:
assume false;

label_0x1270c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7224bv64));

label_0x12714:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x1271b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1271d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12725:
t1_361 := RAX;
t2_362 := 64096bv64;
RAX := PLUS_64(RAX, t2_362);
CF := bool2bv(LT_64(RAX, t1_361));
OF := AND_1((bool2bv((t1_361[64:63]) == (t2_362[64:63]))), (XOR_1((t1_361[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_361)), t2_362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1272b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7232bv64), RAX);

label_0x12733:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7232bv64));

label_0x1273b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_151;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12741:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12746:
t_369 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_152;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))))[1:0]));
SF := t_369[64:63];
ZF := bool2bv(0bv64 == t_369);

label_0x12749:
if (bv2bool(ZF)) {
  goto label_0x1274c;
}

label_0x1274b:
assume false;

label_0x1274c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7232bv64));

label_0x12754:
origDEST_373 := RAX;
origCOUNT_374 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), CF, LSHIFT_64(origDEST_373, (MINUS_64(64bv64, origCOUNT_374)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_374 == 1bv64)), origDEST_373[64:63], unconstrained_153));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), AF, unconstrained_154);

label_0x12758:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1275f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12763:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7232bv64));

label_0x1276b:
origDEST_379 := RCX;
origCOUNT_380 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), CF, LSHIFT_64(origDEST_379, (MINUS_64(64bv64, origCOUNT_380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_380 == 1bv64)), origDEST_379[64:63], unconstrained_155));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), AF, unconstrained_156);

label_0x1276f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_157;
SF := unconstrained_158;
AF := unconstrained_159;
PF := unconstrained_160;

label_0x12773:
if (bv2bool(CF)) {
  goto label_0x12776;
}

label_0x12775:
assume false;

label_0x12776:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7232bv64));

label_0x1277e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 196bv64)));

label_0x12785:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12787:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1278f:
t1_385 := RAX;
t2_386 := 64100bv64;
RAX := PLUS_64(RAX, t2_386);
CF := bool2bv(LT_64(RAX, t1_385));
OF := AND_1((bool2bv((t1_385[64:63]) == (t2_386[64:63]))), (XOR_1((t1_385[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_385)), t2_386)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12795:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7240bv64), RAX);

label_0x1279d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7240bv64));

label_0x127a5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_161;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x127ab:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x127b0:
t_393 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_162;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_393, 4bv64)), t_393)), 2bv64)), (XOR_64((RSHIFT_64(t_393, 4bv64)), t_393)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_393, 4bv64)), t_393)), 2bv64)), (XOR_64((RSHIFT_64(t_393, 4bv64)), t_393)))))[1:0]));
SF := t_393[64:63];
ZF := bool2bv(0bv64 == t_393);

label_0x127b3:
if (bv2bool(ZF)) {
  goto label_0x127b6;
}

label_0x127b5:
assume false;

label_0x127b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7240bv64));

label_0x127be:
origDEST_397 := RAX;
origCOUNT_398 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), CF, LSHIFT_64(origDEST_397, (MINUS_64(64bv64, origCOUNT_398)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_398 == 1bv64)), origDEST_397[64:63], unconstrained_163));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), AF, unconstrained_164);

label_0x127c2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x127c9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x127cd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7240bv64));

label_0x127d5:
origDEST_403 := RCX;
origCOUNT_404 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), CF, LSHIFT_64(origDEST_403, (MINUS_64(64bv64, origCOUNT_404)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_404 == 1bv64)), origDEST_403[64:63], unconstrained_165));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_404 == 0bv64)), AF, unconstrained_166);

label_0x127d9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_167;
SF := unconstrained_168;
AF := unconstrained_169;
PF := unconstrained_170;

label_0x127dd:
if (bv2bool(CF)) {
  goto label_0x127e0;
}

label_0x127df:
assume false;

label_0x127e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7240bv64));

label_0x127e8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x127ef:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x127f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x127f9:
t1_409 := RAX;
t2_410 := 64104bv64;
RAX := PLUS_64(RAX, t2_410);
CF := bool2bv(LT_64(RAX, t1_409));
OF := AND_1((bool2bv((t1_409[64:63]) == (t2_410[64:63]))), (XOR_1((t1_409[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_409)), t2_410)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x127ff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7248bv64), RAX);

label_0x12807:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7248bv64));

label_0x1280f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_171;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12815:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1281a:
t_417 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_172;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)), 2bv64)), (XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)), 2bv64)), (XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)))))[1:0]));
SF := t_417[64:63];
ZF := bool2bv(0bv64 == t_417);

label_0x1281d:
if (bv2bool(ZF)) {
  goto label_0x12820;
}

label_0x1281f:
assume false;

label_0x12820:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7248bv64));

label_0x12828:
origDEST_421 := RAX;
origCOUNT_422 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), CF, LSHIFT_64(origDEST_421, (MINUS_64(64bv64, origCOUNT_422)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_422 == 1bv64)), origDEST_421[64:63], unconstrained_173));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), AF, unconstrained_174);

label_0x1282c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12833:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12837:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7248bv64));

label_0x1283f:
origDEST_427 := RCX;
origCOUNT_428 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), CF, LSHIFT_64(origDEST_427, (MINUS_64(64bv64, origCOUNT_428)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_428 == 1bv64)), origDEST_427[64:63], unconstrained_175));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_428 == 0bv64)), AF, unconstrained_176);

label_0x12843:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_177;
SF := unconstrained_178;
AF := unconstrained_179;
PF := unconstrained_180;

label_0x12847:
if (bv2bool(CF)) {
  goto label_0x1284a;
}

label_0x12849:
assume false;

label_0x1284a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7248bv64));

label_0x12852:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 204bv64)));

label_0x12859:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1285b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12863:
t1_433 := RAX;
t2_434 := 64108bv64;
RAX := PLUS_64(RAX, t2_434);
CF := bool2bv(LT_64(RAX, t1_433));
OF := AND_1((bool2bv((t1_433[64:63]) == (t2_434[64:63]))), (XOR_1((t1_433[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_433)), t2_434)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12869:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7256bv64), RAX);

label_0x12871:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7256bv64));

label_0x12879:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_181;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1287f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12884:
t_441 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_182;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)), 2bv64)), (XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)), 2bv64)), (XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)))))[1:0]));
SF := t_441[64:63];
ZF := bool2bv(0bv64 == t_441);

label_0x12887:
if (bv2bool(ZF)) {
  goto label_0x1288a;
}

label_0x12889:
assume false;

label_0x1288a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7256bv64));

label_0x12892:
origDEST_445 := RAX;
origCOUNT_446 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), CF, LSHIFT_64(origDEST_445, (MINUS_64(64bv64, origCOUNT_446)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_446 == 1bv64)), origDEST_445[64:63], unconstrained_183));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), AF, unconstrained_184);

label_0x12896:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1289d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x128a1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7256bv64));

label_0x128a9:
origDEST_451 := RCX;
origCOUNT_452 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), CF, LSHIFT_64(origDEST_451, (MINUS_64(64bv64, origCOUNT_452)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_452 == 1bv64)), origDEST_451[64:63], unconstrained_185));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), AF, unconstrained_186);

label_0x128ad:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_187;
SF := unconstrained_188;
AF := unconstrained_189;
PF := unconstrained_190;

label_0x128b1:
if (bv2bool(CF)) {
  goto label_0x128b4;
}

label_0x128b3:
assume false;

label_0x128b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7256bv64));

label_0x128bc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x128c3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x128c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x128cd:
t1_457 := RAX;
t2_458 := 64112bv64;
RAX := PLUS_64(RAX, t2_458);
CF := bool2bv(LT_64(RAX, t1_457));
OF := AND_1((bool2bv((t1_457[64:63]) == (t2_458[64:63]))), (XOR_1((t1_457[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_457)), t2_458)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x128d3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7264bv64), RAX);

label_0x128db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7264bv64));

label_0x128e3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_191;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x128e9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x128ee:
t_465 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_192;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)), 2bv64)), (XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)), 2bv64)), (XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)))))[1:0]));
SF := t_465[64:63];
ZF := bool2bv(0bv64 == t_465);

label_0x128f1:
if (bv2bool(ZF)) {
  goto label_0x128f4;
}

label_0x128f3:
assume false;

label_0x128f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7264bv64));

label_0x128fc:
origDEST_469 := RAX;
origCOUNT_470 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), CF, LSHIFT_64(origDEST_469, (MINUS_64(64bv64, origCOUNT_470)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_470 == 1bv64)), origDEST_469[64:63], unconstrained_193));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), AF, unconstrained_194);

label_0x12900:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12907:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1290b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7264bv64));

label_0x12913:
origDEST_475 := RCX;
origCOUNT_476 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), CF, LSHIFT_64(origDEST_475, (MINUS_64(64bv64, origCOUNT_476)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_476 == 1bv64)), origDEST_475[64:63], unconstrained_195));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), AF, unconstrained_196);

label_0x12917:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_197;
SF := unconstrained_198;
AF := unconstrained_199;
PF := unconstrained_200;

label_0x1291b:
if (bv2bool(CF)) {
  goto label_0x1291e;
}

label_0x1291d:
assume false;

label_0x1291e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7264bv64));

label_0x12926:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64)));

label_0x1292d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1292f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12937:
t1_481 := RAX;
t2_482 := 64116bv64;
RAX := PLUS_64(RAX, t2_482);
CF := bool2bv(LT_64(RAX, t1_481));
OF := AND_1((bool2bv((t1_481[64:63]) == (t2_482[64:63]))), (XOR_1((t1_481[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_481)), t2_482)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1293d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7272bv64), RAX);

label_0x12945:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7272bv64));

label_0x1294d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_201;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12953:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12958:
t_489 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_202;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))))[1:0]));
SF := t_489[64:63];
ZF := bool2bv(0bv64 == t_489);

label_0x1295b:
if (bv2bool(ZF)) {
  goto label_0x1295e;
}

label_0x1295d:
assume false;

label_0x1295e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7272bv64));

label_0x12966:
origDEST_493 := RAX;
origCOUNT_494 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), CF, LSHIFT_64(origDEST_493, (MINUS_64(64bv64, origCOUNT_494)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_494 == 1bv64)), origDEST_493[64:63], unconstrained_203));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), AF, unconstrained_204);

label_0x1296a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12971:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12975:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7272bv64));

label_0x1297d:
origDEST_499 := RCX;
origCOUNT_500 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), CF, LSHIFT_64(origDEST_499, (MINUS_64(64bv64, origCOUNT_500)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_500 == 1bv64)), origDEST_499[64:63], unconstrained_205));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), AF, unconstrained_206);

label_0x12981:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_207;
SF := unconstrained_208;
AF := unconstrained_209;
PF := unconstrained_210;

label_0x12985:
if (bv2bool(CF)) {
  goto label_0x12988;
}

label_0x12987:
assume false;

label_0x12988:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7272bv64));

label_0x12990:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)));

label_0x12997:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12999:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x129a1:
t1_505 := RAX;
t2_506 := 64120bv64;
RAX := PLUS_64(RAX, t2_506);
CF := bool2bv(LT_64(RAX, t1_505));
OF := AND_1((bool2bv((t1_505[64:63]) == (t2_506[64:63]))), (XOR_1((t1_505[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_505)), t2_506)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x129a7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7280bv64), RAX);

label_0x129af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7280bv64));

label_0x129b7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_211;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x129bd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x129c2:
t_513 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_212;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))))[1:0]));
SF := t_513[64:63];
ZF := bool2bv(0bv64 == t_513);

label_0x129c5:
if (bv2bool(ZF)) {
  goto label_0x129c8;
}

label_0x129c7:
assume false;

label_0x129c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7280bv64));

label_0x129d0:
origDEST_517 := RAX;
origCOUNT_518 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), CF, LSHIFT_64(origDEST_517, (MINUS_64(64bv64, origCOUNT_518)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_518 == 1bv64)), origDEST_517[64:63], unconstrained_213));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), AF, unconstrained_214);

label_0x129d4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x129db:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x129df:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7280bv64));

label_0x129e7:
origDEST_523 := RCX;
origCOUNT_524 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), CF, LSHIFT_64(origDEST_523, (MINUS_64(64bv64, origCOUNT_524)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_524 == 1bv64)), origDEST_523[64:63], unconstrained_215));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), AF, unconstrained_216);

label_0x129eb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_217;
SF := unconstrained_218;
AF := unconstrained_219;
PF := unconstrained_220;

label_0x129ef:
if (bv2bool(CF)) {
  goto label_0x129f2;
}

label_0x129f1:
assume false;

label_0x129f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7280bv64));

label_0x129fa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x12a02:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x12a05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12a0d:
t1_529 := RAX;
t2_530 := 64128bv64;
RAX := PLUS_64(RAX, t2_530);
CF := bool2bv(LT_64(RAX, t1_529));
OF := AND_1((bool2bv((t1_529[64:63]) == (t2_530[64:63]))), (XOR_1((t1_529[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_529)), t2_530)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12a13:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7288bv64), RAX);

label_0x12a1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7288bv64));

label_0x12a23:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_221;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12a29:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12a2e:
t_537 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_222;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)), 2bv64)), (XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)), 2bv64)), (XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)))))[1:0]));
SF := t_537[64:63];
ZF := bool2bv(0bv64 == t_537);

label_0x12a31:
if (bv2bool(ZF)) {
  goto label_0x12a34;
}

label_0x12a33:
assume false;

label_0x12a34:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7288bv64));

label_0x12a3c:
origDEST_541 := RAX;
origCOUNT_542 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), CF, LSHIFT_64(origDEST_541, (MINUS_64(64bv64, origCOUNT_542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_542 == 1bv64)), origDEST_541[64:63], unconstrained_223));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), AF, unconstrained_224);

label_0x12a40:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12a47:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12a4b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7288bv64));

label_0x12a53:
origDEST_547 := RCX;
origCOUNT_548 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), CF, LSHIFT_64(origDEST_547, (MINUS_64(64bv64, origCOUNT_548)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_548 == 1bv64)), origDEST_547[64:63], unconstrained_225));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), AF, unconstrained_226);

label_0x12a57:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_227;
SF := unconstrained_228;
AF := unconstrained_229;
PF := unconstrained_230;

label_0x12a5b:
if (bv2bool(CF)) {
  goto label_0x12a5e;
}

label_0x12a5d:
assume false;

label_0x12a5e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7288bv64));

label_0x12a66:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x12a6e:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x12a71:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x12a79:
t1_553 := RAX;
t2_554 := 64136bv64;
RAX := PLUS_64(RAX, t2_554);
CF := bool2bv(LT_64(RAX, t1_553));
OF := AND_1((bool2bv((t1_553[64:63]) == (t2_554[64:63]))), (XOR_1((t1_553[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_553)), t2_554)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12a7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7296bv64), RAX);

label_0x12a87:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7296bv64));

label_0x12a8f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_231;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12a95:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12a9a:
t_561 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_232;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))))[1:0]));
SF := t_561[64:63];
ZF := bool2bv(0bv64 == t_561);

label_0x12a9d:
if (bv2bool(ZF)) {
  goto label_0x12aa0;
}

label_0x12a9f:
assume false;

label_0x12aa0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7296bv64));

label_0x12aa8:
origDEST_565 := RAX;
origCOUNT_566 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), CF, LSHIFT_64(origDEST_565, (MINUS_64(64bv64, origCOUNT_566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_566 == 1bv64)), origDEST_565[64:63], unconstrained_233));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), AF, unconstrained_234);

label_0x12aac:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12ab3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12ab7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7296bv64));

label_0x12abf:
origDEST_571 := RCX;
origCOUNT_572 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), CF, LSHIFT_64(origDEST_571, (MINUS_64(64bv64, origCOUNT_572)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_572 == 1bv64)), origDEST_571[64:63], unconstrained_235));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), AF, unconstrained_236);

label_0x12ac3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_237;
SF := unconstrained_238;
AF := unconstrained_239;
PF := unconstrained_240;

label_0x12ac7:
if (bv2bool(CF)) {
  goto label_0x12aca;
}

label_0x12ac9:
assume false;

label_0x12aca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7296bv64));

label_0x12ad2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x12ada:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x12add:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x12ae4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7304bv64), RAX);

label_0x12aec:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x12af1:
origDEST_577 := RAX;
origCOUNT_578 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), CF, LSHIFT_64(origDEST_577, (MINUS_64(64bv64, origCOUNT_578)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_578 == 1bv64)), origDEST_577[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), AF, unconstrained_242);

label_0x12af5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7304bv64));

label_0x12afd:
t1_583 := RCX;
t2_584 := RAX;
RCX := PLUS_64(RCX, t2_584);
CF := bool2bv(LT_64(RCX, t1_583));
OF := AND_1((bool2bv((t1_583[64:63]) == (t2_584[64:63]))), (XOR_1((t1_583[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_583)), t2_584)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x12b00:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7312bv64), RCX);

label_0x12b08:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x12b0d:
origDEST_589 := RAX;
origCOUNT_590 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, LSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), origDEST_589[64:63], unconstrained_243));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_244);

label_0x12b11:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_245;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12b15:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x12b17:
mem := STORE_LE_8(mem, PLUS_64(RSP, 7320bv64), RCX[32:0][8:0]);

label_0x12b1e:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x12b21:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 7320bv64))));

label_0x12b29:
origDEST_597 := RAX[32:0][8:0];
origCOUNT_598 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), CF, RSHIFT_8(origDEST_597, (MINUS_8(8bv8, origCOUNT_598)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_598 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_246));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv8)), AF, unconstrained_247);

label_0x12b2b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7312bv64));

label_0x12b33:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_248;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x12b35:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7312bv64));

label_0x12b3d:
t_605 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_605, 1bv64)), (XOR_64(t_605, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_605)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12b40:
RDI := RAX;

label_0x12b43:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_249;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x12b45:
RCX := (0bv32 ++ 1bv32);

label_0x12b4a:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x12b4c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0x12b50:
t1_609 := RSP;
t2_610 := 7328bv64;
RSP := PLUS_64(RSP, t2_610);
CF := bool2bv(LT_64(RSP, t1_609));
OF := AND_1((bool2bv((t1_609[64:63]) == (t2_610[64:63]))), (XOR_1((t1_609[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_609)), t2_610)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x12b57:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x12b58:

ra_615 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x12b59:


label_0x12b5c:
t1_617 := LOAD_LE_8(mem, RAX);
t2_618 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_618));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_617));
OF := AND_1((bool2bv((t1_617[8:7]) == (t2_618[8:7]))), (XOR_1((t1_617[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_617)), t2_618)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDI,RSP,SF,ZF,mem,origCOUNT_110,origCOUNT_116,origCOUNT_134,origCOUNT_14,origCOUNT_140,origCOUNT_158,origCOUNT_164,origCOUNT_182,origCOUNT_188,origCOUNT_20,origCOUNT_206,origCOUNT_212,origCOUNT_230,origCOUNT_236,origCOUNT_254,origCOUNT_260,origCOUNT_278,origCOUNT_284,origCOUNT_302,origCOUNT_308,origCOUNT_326,origCOUNT_332,origCOUNT_350,origCOUNT_356,origCOUNT_374,origCOUNT_38,origCOUNT_380,origCOUNT_398,origCOUNT_404,origCOUNT_422,origCOUNT_428,origCOUNT_44,origCOUNT_446,origCOUNT_452,origCOUNT_470,origCOUNT_476,origCOUNT_494,origCOUNT_500,origCOUNT_518,origCOUNT_524,origCOUNT_542,origCOUNT_548,origCOUNT_566,origCOUNT_572,origCOUNT_578,origCOUNT_590,origCOUNT_598,origCOUNT_62,origCOUNT_68,origCOUNT_86,origCOUNT_92,origDEST_109,origDEST_115,origDEST_13,origDEST_133,origDEST_139,origDEST_157,origDEST_163,origDEST_181,origDEST_187,origDEST_19,origDEST_205,origDEST_211,origDEST_229,origDEST_235,origDEST_253,origDEST_259,origDEST_277,origDEST_283,origDEST_301,origDEST_307,origDEST_325,origDEST_331,origDEST_349,origDEST_355,origDEST_37,origDEST_373,origDEST_379,origDEST_397,origDEST_403,origDEST_421,origDEST_427,origDEST_43,origDEST_445,origDEST_451,origDEST_469,origDEST_475,origDEST_493,origDEST_499,origDEST_517,origDEST_523,origDEST_541,origDEST_547,origDEST_565,origDEST_571,origDEST_577,origDEST_589,origDEST_597,origDEST_61,origDEST_67,origDEST_85,origDEST_91,ra_615,t1_1,t1_121,t1_145,t1_169,t1_193,t1_217,t1_241,t1_25,t1_265,t1_289,t1_313,t1_337,t1_361,t1_385,t1_409,t1_433,t1_457,t1_481,t1_49,t1_505,t1_529,t1_553,t1_583,t1_609,t1_617,t1_73,t1_97,t2_122,t2_146,t2_170,t2_194,t2_2,t2_218,t2_242,t2_26,t2_266,t2_290,t2_314,t2_338,t2_362,t2_386,t2_410,t2_434,t2_458,t2_482,t2_50,t2_506,t2_530,t2_554,t2_584,t2_610,t2_618,t2_74,t2_98,t_105,t_129,t_153,t_177,t_201,t_225,t_249,t_273,t_297,t_321,t_33,t_345,t_369,t_393,t_417,t_441,t_465,t_489,t_513,t_537,t_561,t_57,t_605,t_81,t_9;

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
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var RAX: bv64;
var RCX: bv64;
var RDI: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_110: bv64;
var origCOUNT_116: bv64;
var origCOUNT_134: bv64;
var origCOUNT_14: bv64;
var origCOUNT_140: bv64;
var origCOUNT_158: bv64;
var origCOUNT_164: bv64;
var origCOUNT_182: bv64;
var origCOUNT_188: bv64;
var origCOUNT_20: bv64;
var origCOUNT_206: bv64;
var origCOUNT_212: bv64;
var origCOUNT_230: bv64;
var origCOUNT_236: bv64;
var origCOUNT_254: bv64;
var origCOUNT_260: bv64;
var origCOUNT_278: bv64;
var origCOUNT_284: bv64;
var origCOUNT_302: bv64;
var origCOUNT_308: bv64;
var origCOUNT_326: bv64;
var origCOUNT_332: bv64;
var origCOUNT_350: bv64;
var origCOUNT_356: bv64;
var origCOUNT_374: bv64;
var origCOUNT_38: bv64;
var origCOUNT_380: bv64;
var origCOUNT_398: bv64;
var origCOUNT_404: bv64;
var origCOUNT_422: bv64;
var origCOUNT_428: bv64;
var origCOUNT_44: bv64;
var origCOUNT_446: bv64;
var origCOUNT_452: bv64;
var origCOUNT_470: bv64;
var origCOUNT_476: bv64;
var origCOUNT_494: bv64;
var origCOUNT_500: bv64;
var origCOUNT_518: bv64;
var origCOUNT_524: bv64;
var origCOUNT_542: bv64;
var origCOUNT_548: bv64;
var origCOUNT_566: bv64;
var origCOUNT_572: bv64;
var origCOUNT_578: bv64;
var origCOUNT_590: bv64;
var origCOUNT_598: bv8;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_109: bv64;
var origDEST_115: bv64;
var origDEST_13: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_181: bv64;
var origDEST_187: bv64;
var origDEST_19: bv64;
var origDEST_205: bv64;
var origDEST_211: bv64;
var origDEST_229: bv64;
var origDEST_235: bv64;
var origDEST_253: bv64;
var origDEST_259: bv64;
var origDEST_277: bv64;
var origDEST_283: bv64;
var origDEST_301: bv64;
var origDEST_307: bv64;
var origDEST_325: bv64;
var origDEST_331: bv64;
var origDEST_349: bv64;
var origDEST_355: bv64;
var origDEST_37: bv64;
var origDEST_373: bv64;
var origDEST_379: bv64;
var origDEST_397: bv64;
var origDEST_403: bv64;
var origDEST_421: bv64;
var origDEST_427: bv64;
var origDEST_43: bv64;
var origDEST_445: bv64;
var origDEST_451: bv64;
var origDEST_469: bv64;
var origDEST_475: bv64;
var origDEST_493: bv64;
var origDEST_499: bv64;
var origDEST_517: bv64;
var origDEST_523: bv64;
var origDEST_541: bv64;
var origDEST_547: bv64;
var origDEST_565: bv64;
var origDEST_571: bv64;
var origDEST_577: bv64;
var origDEST_589: bv64;
var origDEST_597: bv8;
var origDEST_61: bv64;
var origDEST_67: bv64;
var origDEST_85: bv64;
var origDEST_91: bv64;
var ra_615: bv64;
var t1_1: bv64;
var t1_121: bv64;
var t1_145: bv64;
var t1_169: bv64;
var t1_193: bv64;
var t1_217: bv64;
var t1_241: bv64;
var t1_25: bv64;
var t1_265: bv64;
var t1_289: bv64;
var t1_313: bv64;
var t1_337: bv64;
var t1_361: bv64;
var t1_385: bv64;
var t1_409: bv64;
var t1_433: bv64;
var t1_457: bv64;
var t1_481: bv64;
var t1_49: bv64;
var t1_505: bv64;
var t1_529: bv64;
var t1_553: bv64;
var t1_583: bv64;
var t1_609: bv64;
var t1_617: bv8;
var t1_73: bv64;
var t1_97: bv64;
var t2_122: bv64;
var t2_146: bv64;
var t2_170: bv64;
var t2_194: bv64;
var t2_2: bv64;
var t2_218: bv64;
var t2_242: bv64;
var t2_26: bv64;
var t2_266: bv64;
var t2_290: bv64;
var t2_314: bv64;
var t2_338: bv64;
var t2_362: bv64;
var t2_386: bv64;
var t2_410: bv64;
var t2_434: bv64;
var t2_458: bv64;
var t2_482: bv64;
var t2_50: bv64;
var t2_506: bv64;
var t2_530: bv64;
var t2_554: bv64;
var t2_584: bv64;
var t2_610: bv64;
var t2_618: bv8;
var t2_74: bv64;
var t2_98: bv64;
var t_105: bv64;
var t_129: bv64;
var t_153: bv64;
var t_177: bv64;
var t_201: bv64;
var t_225: bv64;
var t_249: bv64;
var t_273: bv64;
var t_297: bv64;
var t_321: bv64;
var t_33: bv64;
var t_345: bv64;
var t_369: bv64;
var t_393: bv64;
var t_417: bv64;
var t_441: bv64;
var t_465: bv64;
var t_489: bv64;
var t_513: bv64;
var t_537: bv64;
var t_561: bv64;
var t_57: bv64;
var t_605: bv64;
var t_81: bv64;
var t_9: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3271bv64);
axiom policy(4483bv64);
axiom policy(5695bv64);
axiom policy(6907bv64);
axiom policy(9187bv64);
axiom policy(10414bv64);
axiom policy(11626bv64);
axiom policy(12838bv64);
axiom policy(14050bv64);
axiom policy(15262bv64);
axiom policy(16777bv64);
axiom policy(18105bv64);
axiom policy(19433bv64);
axiom policy(20761bv64);
axiom policy(22089bv64);
axiom policy(23468bv64);
axiom policy(24792bv64);
axiom policy(26116bv64);
axiom policy(27563bv64);
axiom policy(29283bv64);
axiom policy(30684bv64);
axiom policy(31906bv64);
axiom policy(33191bv64);
axiom policy(35319bv64);
axiom policy(36601bv64);
axiom policy(37800bv64);
axiom policy(40872bv64);
axiom policy(42188bv64);
axiom policy(44072bv64);
axiom policy(45388bv64);
axiom policy(51419bv64);
axiom policy(52735bv64);
axiom policy(62337bv64);
axiom policy(63549bv64);
axiom policy(64761bv64);
axiom policy(65973bv64);
axiom policy(67185bv64);
axiom policy(68502bv64);
axiom policy(69830bv64);
axiom policy(71158bv64);
axiom policy(72486bv64);
axiom policy(73959bv64);
axiom policy(76636bv64);
axiom policy(76816bv64);
