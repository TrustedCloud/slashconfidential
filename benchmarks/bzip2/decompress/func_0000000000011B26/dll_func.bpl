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
axiom _function_addr_low == 72486bv64;
axiom _function_addr_high == 73959bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x11b26:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11b2e:
t1_1 := RAX;
t2_2 := 8bv64;
RAX := PLUS_64(RAX, t2_2);
CF := bool2bv(LT_64(RAX, t1_1));
OF := AND_1((bool2bv((t1_1[64:63]) == (t2_2[64:63]))), (XOR_1((t1_1[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1)), t2_2)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11b32:
mem := STORE_LE_64(mem, PLUS_64(RSP, 6968bv64), RAX);

label_0x11b3a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6968bv64));

label_0x11b42:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11b48:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11b4d:
t_9 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x11b50:
if (bv2bool(ZF)) {
  goto label_0x11b53;
}

label_0x11b52:
assume false;

label_0x11b53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6968bv64));

label_0x11b5b:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x11b5f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11b66:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11b6a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 6968bv64));

label_0x11b72:
origDEST_19 := RCX;
origCOUNT_20 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_6);

label_0x11b76:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x11b7a:
if (bv2bool(CF)) {
  goto label_0x11b7d;
}

label_0x11b7c:
assume false;

label_0x11b7d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6968bv64));

label_0x11b85:
mem := STORE_LE_32(mem, RAX, 50bv32);

label_0x11b8b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x11b8d:
t_25 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x11b90:
if (bv2bool(ZF)) {
  goto label_0x11fcb;
}

label_0x11b96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11b9e:
t1_29 := RAX;
t2_30 := 36bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11ba2:
t_35 := MINUS_32((LOAD_LE_32(mem, RAX)), 8bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 8bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 8bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_35)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_35, (LOAD_LE_32(mem, RAX)))), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)), 2bv32)), (XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)), 2bv32)), (XOR_32((RSHIFT_32(t_35, 4bv32)), t_35)))))[1:0]));
SF := t_35[32:31];
ZF := bool2bv(0bv32 == t_35);

label_0x11ba5:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x11c69;
}

label_0x11bab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11bb3:
t1_39 := RAX;
t2_40 := 32bv64;
RAX := PLUS_64(RAX, t2_40);
CF := bool2bv(LT_64(RAX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11bb7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11bbf:
t1_45 := RCX;
t2_46 := 36bv64;
RCX := PLUS_64(RCX, t2_46);
CF := bool2bv(LT_64(RCX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x11bc3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x11bc5:
t_51 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), 8bv32));
CF := bool2bv(LT_32(t_51, 8bv32));
OF := AND_32((XOR_32(t_51, 8bv32)), (XOR_32(t_51, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_51)), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x11bc8:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11bca:
origDEST_55 := RAX[32:0];
origCOUNT_56 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), CF, LSHIFT_32(origDEST_55, (MINUS_32(32bv32, origCOUNT_56)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv32)), origDEST_55[32:31], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), AF, unconstrained_13);

label_0x11bcc:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11bd1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 460bv64), RAX[32:0]);

label_0x11bd8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11be0:
t1_63 := RAX;
t2_64 := 36bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11be4:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11be6:
t_69 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 8bv32));
CF := bool2bv(LT_32(t_69, 8bv32));
OF := AND_32((XOR_32(t_69, 8bv32)), (XOR_32(t_69, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_69)), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11be9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 6976bv64), RAX[32:0]);

label_0x11bf0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11bf8:
t1_73 := RAX;
t2_74 := 36bv64;
RAX := PLUS_64(RAX, t2_74);
CF := bool2bv(LT_64(RAX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11bfc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 6984bv64), RAX);

label_0x11c04:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6984bv64));

label_0x11c0c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11c12:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11c17:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0x11c1a:
if (bv2bool(ZF)) {
  goto label_0x11c1d;
}

label_0x11c1c:
assume false;

label_0x11c1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6984bv64));

label_0x11c25:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_18);

label_0x11c29:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11c30:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11c34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 6984bv64));

label_0x11c3c:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_20);

label_0x11c40:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_21;
SF := unconstrained_22;
AF := unconstrained_23;
PF := unconstrained_24;

label_0x11c44:
if (bv2bool(CF)) {
  goto label_0x11c47;
}

label_0x11c46:
assume false;

label_0x11c47:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 6984bv64));

label_0x11c4f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 6976bv64)));

label_0x11c56:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11c58:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 460bv64))));

label_0x11c60:
mem := STORE_LE_8(mem, PLUS_64(RSP, 112bv64), RAX[32:0][8:0]);

label_0x11c64:
goto label_0x11fcb;

label_0x11c69:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11c71:
RAX := LOAD_LE_64(mem, RAX);

label_0x11c74:
t1_97 := RAX;
t2_98 := 8bv64;
RAX := PLUS_64(RAX, t2_98);
CF := bool2bv(LT_64(RAX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11c78:
t_103 := MINUS_32((LOAD_LE_32(mem, RAX)), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 0bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_103)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_103, (LOAD_LE_32(mem, RAX)))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))))[1:0]));
SF := t_103[32:31];
ZF := bool2bv(0bv32 == t_103);

label_0x11c7b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x11c8a;
}

label_0x11c7d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), 0bv32);

label_0x11c85:
assert {:SlashVerifyCommandType "remotejmp"} {:SlashVerifyJmpTarget "0x120e7"} true;
return;

label_0x11c8a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11c92:
t1_107 := RAX;
t2_108 := 32bv64;
RAX := PLUS_64(RAX, t2_108);
CF := bool2bv(LT_64(RAX, t1_107));
OF := AND_1((bool2bv((t1_107[64:63]) == (t2_108[64:63]))), (XOR_1((t1_107[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_107)), t2_108)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11c96:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11c98:
origDEST_113 := RAX[32:0];
origCOUNT_114 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), CF, RSHIFT_32(origDEST_113, (MINUS_32(32bv32, origCOUNT_114)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv32)), AF, unconstrained_26);

label_0x11c9b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11ca3:
RCX := LOAD_LE_64(mem, RCX);

label_0x11ca6:
RCX := LOAD_LE_64(mem, RCX);

label_0x11ca9:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x11cac:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11cae:
mem := STORE_LE_32(mem, PLUS_64(RSP, 6992bv64), RAX[32:0]);

label_0x11cb5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11cbd:
t1_121 := RAX;
t2_122 := 32bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11cc1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7000bv64), RAX);

label_0x11cc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7000bv64));

label_0x11cd1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11cd7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11cdc:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x11cdf:
if (bv2bool(ZF)) {
  goto label_0x11ce2;
}

label_0x11ce1:
assume false;

label_0x11ce2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7000bv64));

label_0x11cea:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_31);

label_0x11cee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11cf5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11cf9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7000bv64));

label_0x11d01:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_33);

label_0x11d05:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_34;
SF := unconstrained_35;
AF := unconstrained_36;
PF := unconstrained_37;

label_0x11d09:
if (bv2bool(CF)) {
  goto label_0x11d0c;
}

label_0x11d0b:
assume false;

label_0x11d0c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7000bv64));

label_0x11d14:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 6992bv64)));

label_0x11d1b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11d1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11d25:
t1_145 := RAX;
t2_146 := 36bv64;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11d29:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11d2b:
t1_151 := RAX[32:0];
t2_152 := 8bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_152));
CF := bool2bv(LT_32((RAX[32:0]), t1_151));
OF := AND_1((bool2bv((t1_151[32:31]) == (t2_152[32:31]))), (XOR_1((t1_151[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_151)), t2_152)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11d2e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 7008bv64), RAX[32:0]);

label_0x11d35:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11d3d:
t1_157 := RAX;
t2_158 := 36bv64;
RAX := PLUS_64(RAX, t2_158);
CF := bool2bv(LT_64(RAX, t1_157));
OF := AND_1((bool2bv((t1_157[64:63]) == (t2_158[64:63]))), (XOR_1((t1_157[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_157)), t2_158)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11d41:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7016bv64), RAX);

label_0x11d49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7016bv64));

label_0x11d51:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11d57:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11d5c:
t_165 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_39;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)), 2bv64)), (XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)), 2bv64)), (XOR_64((RSHIFT_64(t_165, 4bv64)), t_165)))))[1:0]));
SF := t_165[64:63];
ZF := bool2bv(0bv64 == t_165);

label_0x11d5f:
if (bv2bool(ZF)) {
  goto label_0x11d62;
}

label_0x11d61:
assume false;

label_0x11d62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7016bv64));

label_0x11d6a:
origDEST_169 := RAX;
origCOUNT_170 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), CF, LSHIFT_64(origDEST_169, (MINUS_64(64bv64, origCOUNT_170)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv64)), origDEST_169[64:63], unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), AF, unconstrained_41);

label_0x11d6e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11d75:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11d79:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7016bv64));

label_0x11d81:
origDEST_175 := RCX;
origCOUNT_176 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_43);

label_0x11d85:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_44;
SF := unconstrained_45;
AF := unconstrained_46;
PF := unconstrained_47;

label_0x11d89:
if (bv2bool(CF)) {
  goto label_0x11d8c;
}

label_0x11d8b:
assume false;

label_0x11d8c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7016bv64));

label_0x11d94:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 7008bv64)));

label_0x11d9b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11d9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11da5:
RAX := LOAD_LE_64(mem, RAX);

label_0x11da8:
RAX := LOAD_LE_64(mem, RAX);

label_0x11dab:
t_181 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_181[64:63]) == (1bv64[64:63]))), (XOR_1((t_181[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_181)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11dae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7024bv64), RAX);

label_0x11db6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11dbe:
RAX := LOAD_LE_64(mem, RAX);

label_0x11dc1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7032bv64), RAX);

label_0x11dc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7032bv64));

label_0x11dd1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11dd7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11ddc:
t_187 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))))[1:0]));
SF := t_187[64:63];
ZF := bool2bv(0bv64 == t_187);

label_0x11ddf:
if (bv2bool(ZF)) {
  goto label_0x11de2;
}

label_0x11de1:
assume false;

label_0x11de2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7032bv64));

label_0x11dea:
origDEST_191 := RAX;
origCOUNT_192 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_51);

label_0x11dee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11df5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11df9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7032bv64));

label_0x11e01:
origDEST_197 := RCX;
origCOUNT_198 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), CF, LSHIFT_64(origDEST_197, (MINUS_64(64bv64, origCOUNT_198)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_198 == 1bv64)), origDEST_197[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), AF, unconstrained_53);

label_0x11e05:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x11e09:
if (bv2bool(CF)) {
  goto label_0x11e0c;
}

label_0x11e0b:
assume false;

label_0x11e0c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7032bv64));

label_0x11e14:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7024bv64));

label_0x11e1c:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x11e1f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11e27:
RAX := LOAD_LE_64(mem, RAX);

label_0x11e2a:
t1_203 := RAX;
t2_204 := 8bv64;
RAX := PLUS_64(RAX, t2_204);
CF := bool2bv(LT_64(RAX, t1_203));
OF := AND_1((bool2bv((t1_203[64:63]) == (t2_204[64:63]))), (XOR_1((t1_203[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_203)), t2_204)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11e2e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11e30:
t_209 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_209, 1bv32)), (XOR_32(t_209, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_209)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11e32:
mem := STORE_LE_32(mem, PLUS_64(RSP, 7040bv64), RAX[32:0]);

label_0x11e39:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11e41:
RAX := LOAD_LE_64(mem, RAX);

label_0x11e44:
t1_213 := RAX;
t2_214 := 8bv64;
RAX := PLUS_64(RAX, t2_214);
CF := bool2bv(LT_64(RAX, t1_213));
OF := AND_1((bool2bv((t1_213[64:63]) == (t2_214[64:63]))), (XOR_1((t1_213[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_213)), t2_214)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11e48:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7048bv64), RAX);

label_0x11e50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7048bv64));

label_0x11e58:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11e5e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11e63:
t_221 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))))[1:0]));
SF := t_221[64:63];
ZF := bool2bv(0bv64 == t_221);

label_0x11e66:
if (bv2bool(ZF)) {
  goto label_0x11e69;
}

label_0x11e68:
assume false;

label_0x11e69:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7048bv64));

label_0x11e71:
origDEST_225 := RAX;
origCOUNT_226 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), CF, LSHIFT_64(origDEST_225, (MINUS_64(64bv64, origCOUNT_226)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_226 == 1bv64)), origDEST_225[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), AF, unconstrained_61);

label_0x11e75:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11e7c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11e80:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7048bv64));

label_0x11e88:
origDEST_231 := RCX;
origCOUNT_232 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), CF, LSHIFT_64(origDEST_231, (MINUS_64(64bv64, origCOUNT_232)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_232 == 1bv64)), origDEST_231[64:63], unconstrained_62));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), AF, unconstrained_63);

label_0x11e8c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_64;
SF := unconstrained_65;
AF := unconstrained_66;
PF := unconstrained_67;

label_0x11e90:
if (bv2bool(CF)) {
  goto label_0x11e93;
}

label_0x11e92:
assume false;

label_0x11e93:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7048bv64));

label_0x11e9b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 7040bv64)));

label_0x11ea2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11ea4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11eac:
RAX := LOAD_LE_64(mem, RAX);

label_0x11eaf:
t1_237 := RAX;
t2_238 := 12bv64;
RAX := PLUS_64(RAX, t2_238);
CF := bool2bv(LT_64(RAX, t1_237));
OF := AND_1((bool2bv((t1_237[64:63]) == (t2_238[64:63]))), (XOR_1((t1_237[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_237)), t2_238)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11eb3:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11eb5:
t_243 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_243[32:31]) == (1bv32[32:31]))), (XOR_1((t_243[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_243)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11eb7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 7056bv64), RAX[32:0]);

label_0x11ebe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11ec6:
RAX := LOAD_LE_64(mem, RAX);

label_0x11ec9:
t1_247 := RAX;
t2_248 := 12bv64;
RAX := PLUS_64(RAX, t2_248);
CF := bool2bv(LT_64(RAX, t1_247));
OF := AND_1((bool2bv((t1_247[64:63]) == (t2_248[64:63]))), (XOR_1((t1_247[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_247)), t2_248)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11ecd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7064bv64), RAX);

label_0x11ed5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7064bv64));

label_0x11edd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11ee3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11ee8:
t_255 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_255, 4bv64)), t_255)), 2bv64)), (XOR_64((RSHIFT_64(t_255, 4bv64)), t_255)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_255, 4bv64)), t_255)), 2bv64)), (XOR_64((RSHIFT_64(t_255, 4bv64)), t_255)))))[1:0]));
SF := t_255[64:63];
ZF := bool2bv(0bv64 == t_255);

label_0x11eeb:
if (bv2bool(ZF)) {
  goto label_0x11eee;
}

label_0x11eed:
assume false;

label_0x11eee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7064bv64));

label_0x11ef6:
origDEST_259 := RAX;
origCOUNT_260 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), CF, LSHIFT_64(origDEST_259, (MINUS_64(64bv64, origCOUNT_260)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_260 == 1bv64)), origDEST_259[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), AF, unconstrained_71);

label_0x11efa:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11f01:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11f05:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7064bv64));

label_0x11f0d:
origDEST_265 := RCX;
origCOUNT_266 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), CF, LSHIFT_64(origDEST_265, (MINUS_64(64bv64, origCOUNT_266)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_266 == 1bv64)), origDEST_265[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_266 == 0bv64)), AF, unconstrained_73);

label_0x11f11:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x11f15:
if (bv2bool(CF)) {
  goto label_0x11f18;
}

label_0x11f17:
assume false;

label_0x11f18:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7064bv64));

label_0x11f20:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 7056bv64)));

label_0x11f27:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11f29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11f31:
RAX := LOAD_LE_64(mem, RAX);

label_0x11f34:
t1_271 := RAX;
t2_272 := 12bv64;
RAX := PLUS_64(RAX, t2_272);
CF := bool2bv(LT_64(RAX, t1_271));
OF := AND_1((bool2bv((t1_271[64:63]) == (t2_272[64:63]))), (XOR_1((t1_271[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_271)), t2_272)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11f38:
t_277 := MINUS_32((LOAD_LE_32(mem, RAX)), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 0bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_277)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_277, (LOAD_LE_32(mem, RAX)))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))))[1:0]));
SF := t_277[32:31];
ZF := bool2bv(0bv32 == t_277);

label_0x11f3b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x11fc6;
}

label_0x11f41:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11f49:
RAX := LOAD_LE_64(mem, RAX);

label_0x11f4c:
t1_281 := RAX;
t2_282 := 16bv64;
RAX := PLUS_64(RAX, t2_282);
CF := bool2bv(LT_64(RAX, t1_281));
OF := AND_1((bool2bv((t1_281[64:63]) == (t2_282[64:63]))), (XOR_1((t1_281[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_281)), t2_282)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11f50:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11f52:
t_287 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_287[32:31]) == (1bv32[32:31]))), (XOR_1((t_287[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_287)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11f54:
mem := STORE_LE_32(mem, PLUS_64(RSP, 7072bv64), RAX[32:0]);

label_0x11f5b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11f63:
RAX := LOAD_LE_64(mem, RAX);

label_0x11f66:
t1_291 := RAX;
t2_292 := 16bv64;
RAX := PLUS_64(RAX, t2_292);
CF := bool2bv(LT_64(RAX, t1_291));
OF := AND_1((bool2bv((t1_291[64:63]) == (t2_292[64:63]))), (XOR_1((t1_291[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_291)), t2_292)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11f6a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7080bv64), RAX);

label_0x11f72:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7080bv64));

label_0x11f7a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11f80:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11f85:
t_299 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)), 2bv64)), (XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)), 2bv64)), (XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)))))[1:0]));
SF := t_299[64:63];
ZF := bool2bv(0bv64 == t_299);

label_0x11f88:
if (bv2bool(ZF)) {
  goto label_0x11f8b;
}

label_0x11f8a:
assume false;

label_0x11f8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7080bv64));

label_0x11f93:
origDEST_303 := RAX;
origCOUNT_304 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), CF, LSHIFT_64(origDEST_303, (MINUS_64(64bv64, origCOUNT_304)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_304 == 1bv64)), origDEST_303[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), AF, unconstrained_81);

label_0x11f97:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11f9e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11fa2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7080bv64));

label_0x11faa:
origDEST_309 := RCX;
origCOUNT_310 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), CF, LSHIFT_64(origDEST_309, (MINUS_64(64bv64, origCOUNT_310)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv64)), origDEST_309[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), AF, unconstrained_83);

label_0x11fae:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_84;
SF := unconstrained_85;
AF := unconstrained_86;
PF := unconstrained_87;

label_0x11fb2:
if (bv2bool(CF)) {
  goto label_0x11fb5;
}

label_0x11fb4:
assume false;

label_0x11fb5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7080bv64));

label_0x11fbd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 7072bv64)));

label_0x11fc4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11fc6:
goto label_0x11b8b;

label_0x11fcb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11fd3:
t1_315 := RAX;
t2_316 := 3180bv64;
RAX := PLUS_64(RAX, t2_316);
CF := bool2bv(LT_64(RAX, t1_315));
OF := AND_1((bool2bv((t1_315[64:63]) == (t2_316[64:63]))), (XOR_1((t1_315[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_315)), t2_316)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11fd9:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x11fdb:
origDEST_321 := RAX[32:0];
origCOUNT_322 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), CF, RSHIFT_32(origDEST_321, (MINUS_32(32bv32, origCOUNT_322)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_322 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv32)), AF, unconstrained_89);

label_0x11fde:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 112bv64))));

label_0x11fe3:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x11fe5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 7088bv64), RAX[32:0]);

label_0x11fec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x11ff4:
t1_329 := RAX;
t2_330 := 3180bv64;
RAX := PLUS_64(RAX, t2_330);
CF := bool2bv(LT_64(RAX, t1_329));
OF := AND_1((bool2bv((t1_329[64:63]) == (t2_330[64:63]))), (XOR_1((t1_329[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_329)), t2_330)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11ffa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7096bv64), RAX);

label_0x12002:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7096bv64));

label_0x1200a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12010:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x12015:
t_337 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)), 2bv64)), (XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)), 2bv64)), (XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)))))[1:0]));
SF := t_337[64:63];
ZF := bool2bv(0bv64 == t_337);

label_0x12018:
if (bv2bool(ZF)) {
  goto label_0x1201b;
}

label_0x1201a:
assume false;

label_0x1201b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7096bv64));

label_0x12023:
origDEST_341 := RAX;
origCOUNT_342 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), CF, LSHIFT_64(origDEST_341, (MINUS_64(64bv64, origCOUNT_342)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_342 == 1bv64)), origDEST_341[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), AF, unconstrained_94);

label_0x12027:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1202e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x12032:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7096bv64));

label_0x1203a:
origDEST_347 := RCX;
origCOUNT_348 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), CF, LSHIFT_64(origDEST_347, (MINUS_64(64bv64, origCOUNT_348)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_348 == 1bv64)), origDEST_347[64:63], unconstrained_95));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), AF, unconstrained_96);

label_0x1203e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x12042:
if (bv2bool(CF)) {
  goto label_0x12045;
}

label_0x12044:
assume false;

label_0x12045:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7096bv64));

label_0x1204d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 7088bv64)));

label_0x12054:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x12056:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7344bv64));

label_0x1205e:
t1_353 := RAX;
t2_354 := 8bv64;
RAX := PLUS_64(RAX, t2_354);
CF := bool2bv(LT_64(RAX, t1_353));
OF := AND_1((bool2bv((t1_353[64:63]) == (t2_354[64:63]))), (XOR_1((t1_353[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_353)), t2_354)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12062:
mem := STORE_LE_64(mem, PLUS_64(RSP, 7104bv64), RAX);

label_0x1206a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7104bv64));

label_0x12072:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12078:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1207d:
t_361 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)), 2bv64)), (XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)), 2bv64)), (XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)))))[1:0]));
SF := t_361[64:63];
ZF := bool2bv(0bv64 == t_361);

label_0x12080:
if (bv2bool(ZF)) {
  goto label_0x12083;
}

label_0x12082:
assume false;

label_0x12083:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7104bv64));

label_0x1208b:
origDEST_365 := RAX;
origCOUNT_366 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), CF, LSHIFT_64(origDEST_365, (MINUS_64(64bv64, origCOUNT_366)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_366 == 1bv64)), origDEST_365[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), AF, unconstrained_104);

label_0x1208f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x12096:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1209a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 7104bv64));

label_0x120a2:
origDEST_371 := RCX;
origCOUNT_372 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), CF, LSHIFT_64(origDEST_371, (MINUS_64(64bv64, origCOUNT_372)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_372 == 1bv64)), origDEST_371[64:63], unconstrained_105));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), AF, unconstrained_106);

label_0x120a6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_107;
SF := unconstrained_108;
AF := unconstrained_109;
PF := unconstrained_110;

label_0x120aa:
if (bv2bool(CF)) {
  goto label_0x120ad;
}

label_0x120ac:
assume false;

label_0x120ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 7104bv64));

label_0x120b5:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x120bb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), 4bv32);

label_0x120c3:
assert {:SlashVerifyCommandType "remotejmp"} {:SlashVerifyJmpTarget "0x120e7"} true;
return;

label_0x120c5:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_111;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x120c7:
t_377 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_377)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_377, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))))[1:0]));
SF := t_377[32:31];
ZF := bool2bv(0bv32 == t_377);

label_0x120ca:
if (bv2bool(ZF)) {
  goto label_0x120d6;
}

label_0x120cc:
RCX := (0bv32 ++ 4001bv32);

label_0x120d1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 73942bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x120d6"} true;
call arbitrary_func();

label_0x120d6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_112;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x120d8:
t_381 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_381)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_381, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))))[1:0]));
SF := t_381[32:31];
ZF := bool2bv(0bv32 == t_381);

label_0x120db:
if (bv2bool(ZF)) {
  assert {:SlashVerifyCommandType "remotejmp"} {:SlashVerifyJmpTarget "0x120e7"} true;
return;
}

label_0x120dd:
RCX := (0bv32 ++ 4002bv32);

label_0x120e2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 73959bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x120e7"} true;
call arbitrary_func();

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RSP,SF,ZF,mem,origCOUNT_114,origCOUNT_134,origCOUNT_14,origCOUNT_140,origCOUNT_170,origCOUNT_176,origCOUNT_192,origCOUNT_198,origCOUNT_20,origCOUNT_226,origCOUNT_232,origCOUNT_260,origCOUNT_266,origCOUNT_304,origCOUNT_310,origCOUNT_322,origCOUNT_342,origCOUNT_348,origCOUNT_366,origCOUNT_372,origCOUNT_56,origCOUNT_86,origCOUNT_92,origDEST_113,origDEST_13,origDEST_133,origDEST_139,origDEST_169,origDEST_175,origDEST_19,origDEST_191,origDEST_197,origDEST_225,origDEST_231,origDEST_259,origDEST_265,origDEST_303,origDEST_309,origDEST_321,origDEST_341,origDEST_347,origDEST_365,origDEST_371,origDEST_55,origDEST_85,origDEST_91,t1_1,t1_107,t1_121,t1_145,t1_151,t1_157,t1_203,t1_213,t1_237,t1_247,t1_271,t1_281,t1_29,t1_291,t1_315,t1_329,t1_353,t1_39,t1_45,t1_63,t1_73,t1_97,t2_108,t2_122,t2_146,t2_152,t2_158,t2_2,t2_204,t2_214,t2_238,t2_248,t2_272,t2_282,t2_292,t2_30,t2_316,t2_330,t2_354,t2_40,t2_46,t2_64,t2_74,t2_98,t_103,t_129,t_165,t_181,t_187,t_209,t_221,t_243,t_25,t_255,t_277,t_287,t_299,t_337,t_35,t_361,t_377,t_381,t_51,t_69,t_81,t_9;

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
var RAX: bv64;
var RCX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_114: bv32;
var origCOUNT_134: bv64;
var origCOUNT_14: bv64;
var origCOUNT_140: bv64;
var origCOUNT_170: bv64;
var origCOUNT_176: bv64;
var origCOUNT_192: bv64;
var origCOUNT_198: bv64;
var origCOUNT_20: bv64;
var origCOUNT_226: bv64;
var origCOUNT_232: bv64;
var origCOUNT_260: bv64;
var origCOUNT_266: bv64;
var origCOUNT_304: bv64;
var origCOUNT_310: bv64;
var origCOUNT_322: bv32;
var origCOUNT_342: bv64;
var origCOUNT_348: bv64;
var origCOUNT_366: bv64;
var origCOUNT_372: bv64;
var origCOUNT_56: bv32;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_113: bv32;
var origDEST_13: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_169: bv64;
var origDEST_175: bv64;
var origDEST_19: bv64;
var origDEST_191: bv64;
var origDEST_197: bv64;
var origDEST_225: bv64;
var origDEST_231: bv64;
var origDEST_259: bv64;
var origDEST_265: bv64;
var origDEST_303: bv64;
var origDEST_309: bv64;
var origDEST_321: bv32;
var origDEST_341: bv64;
var origDEST_347: bv64;
var origDEST_365: bv64;
var origDEST_371: bv64;
var origDEST_55: bv32;
var origDEST_85: bv64;
var origDEST_91: bv64;
var t1_1: bv64;
var t1_107: bv64;
var t1_121: bv64;
var t1_145: bv64;
var t1_151: bv32;
var t1_157: bv64;
var t1_203: bv64;
var t1_213: bv64;
var t1_237: bv64;
var t1_247: bv64;
var t1_271: bv64;
var t1_281: bv64;
var t1_29: bv64;
var t1_291: bv64;
var t1_315: bv64;
var t1_329: bv64;
var t1_353: bv64;
var t1_39: bv64;
var t1_45: bv64;
var t1_63: bv64;
var t1_73: bv64;
var t1_97: bv64;
var t2_108: bv64;
var t2_122: bv64;
var t2_146: bv64;
var t2_152: bv32;
var t2_158: bv64;
var t2_2: bv64;
var t2_204: bv64;
var t2_214: bv64;
var t2_238: bv64;
var t2_248: bv64;
var t2_272: bv64;
var t2_282: bv64;
var t2_292: bv64;
var t2_30: bv64;
var t2_316: bv64;
var t2_330: bv64;
var t2_354: bv64;
var t2_40: bv64;
var t2_46: bv64;
var t2_64: bv64;
var t2_74: bv64;
var t2_98: bv64;
var t_103: bv32;
var t_129: bv64;
var t_165: bv64;
var t_181: bv64;
var t_187: bv64;
var t_209: bv32;
var t_221: bv64;
var t_243: bv32;
var t_25: bv32;
var t_255: bv64;
var t_277: bv32;
var t_287: bv32;
var t_299: bv64;
var t_337: bv64;
var t_35: bv32;
var t_361: bv64;
var t_377: bv32;
var t_381: bv32;
var t_51: bv32;
var t_69: bv32;
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
