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
axiom _function_addr_low == 1312bv64;
axiom _function_addr_high == 3344bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x520:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x525:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x52a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x52e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x533:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x534:
t_3 := RSP;
RSP := MINUS_64(RSP, 256bv64);
CF := bool2bv(LT_64(t_3, 256bv64));
OF := AND_64((XOR_64(t_3, 256bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 256bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x53b:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x542:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x54a:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x54f:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0x553:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x55b:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x560:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x564:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x568:
RCX := (0bv32 ++ 51bv32);

label_0x56d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RCX);

label_0x575:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x578:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x580:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x583:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x58b:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x593:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x597:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x59f:
t1_29 := RAX;
t2_30 := 20bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5a3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x5ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5b3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5b9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5be:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x5c1:
if (bv2bool(ZF)) {
  goto label_0x5c4;
}

label_0x5c3:
assume false;

label_0x5c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5cc:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_12);

label_0x5d0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5d7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5db:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5e3:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_14);

label_0x5e7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_15;
SF := unconstrained_16;
AF := unconstrained_17;
PF := unconstrained_18;

label_0x5eb:
if (bv2bool(CF)) {
  goto label_0x5ee;
}

label_0x5ed:
assume false;

label_0x5ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5f6:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x5f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x601:
t1_53 := RAX;
t2_54 := 8bv64;
RAX := PLUS_64(RAX, t2_54);
CF := bool2bv(LT_64(RAX, t1_53));
OF := AND_1((bool2bv((t1_53[64:63]) == (t2_54[64:63]))), (XOR_1((t1_53[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_53)), t2_54)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x605:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x608:
t_59 := RAX[32:0][16:0];
RAX := (RAX[64:16]) ++ (PLUS_16((RAX[32:0][16:0]), 1bv16));
OF := AND_1((bool2bv((t_59[16:15]) == (1bv16[16:15]))), (XOR_1((t_59[16:15]), (RAX[32:0][16:0][16:15]))));
AF := bool2bv(16bv16 == (AND_16(16bv16, (XOR_16((XOR_16((RAX[32:0][16:0]), t_59)), 1bv16)))));
PF := NOT_1((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))), 1bv16)), (XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))))[1:0]));
SF := RAX[32:0][16:0][16:15];
ZF := bool2bv(0bv16 == (RAX[32:0][16:0]));

label_0x60b:
mem := STORE_LE_16(mem, PLUS_64(RSP, 176bv64), RAX[32:0][16:0]);

label_0x613:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x61b:
t1_63 := RAX;
t2_64 := 8bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x61f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x627:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x62f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x635:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x63a:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x63d:
if (bv2bool(ZF)) {
  goto label_0x640;
}

label_0x63f:
assume false;

label_0x640:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x648:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_22);

label_0x64c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x653:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x657:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x65f:
origDEST_81 := RCX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_24);

label_0x663:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x667:
if (bv2bool(CF)) {
  goto label_0x66a;
}

label_0x669:
assume false;

label_0x66a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x672:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 176bv64))));

label_0x67a:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x67d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x685:
t1_87 := RAX;
t2_88 := 8bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x689:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x68c:
t_93 := MINUS_32((RAX[32:0]), 65535bv32);
CF := bool2bv(LT_32((RAX[32:0]), 65535bv32));
OF := AND_32((XOR_32((RAX[32:0]), 65535bv32)), (XOR_32((RAX[32:0]), t_93)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_93, (RAX[32:0]))), 65535bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))))[1:0]));
SF := t_93[32:31];
ZF := bool2bv(0bv32 == t_93);

label_0x691:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x73b;
}

label_0x697:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x69f:
t1_97 := RAX;
t2_98 := 332bv64;
RAX := PLUS_64(RAX, t2_98);
CF := bool2bv(LT_64(RAX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6a5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x6ad:
t1_103 := RCX;
t2_104 := 336bv64;
RCX := PLUS_64(RCX, t2_104);
CF := bool2bv(LT_64(RCX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6b4:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x6b6:
t_109 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RAX := (0bv32 ++ t_109[32:0]);
OF := bool2bv(t_109 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_109 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_29;
SF := unconstrained_30;
ZF := unconstrained_31;
AF := unconstrained_32;

label_0x6b9:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x6bb:
t_111 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_111[64:0];
OF := bool2bv(t_111 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_111 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_33;
SF := unconstrained_34;
ZF := unconstrained_35;
AF := unconstrained_36;

label_0x6bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x6c7:
R8 := RAX;

label_0x6ca:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_37;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x6cc:
RCX := LOAD_LE_64(mem, RCX);

label_0x6cf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1748bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x6d4"} true;
call arbitrary_func();

label_0x6d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x6dc:
t1_113 := RAX;
t2_114 := 8bv64;
RAX := PLUS_64(RAX, t2_114);
CF := bool2bv(LT_64(RAX, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x6e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x6f0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6f6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6fb:
t_121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_39;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x6fe:
if (bv2bool(ZF)) {
  goto label_0x701;
}

label_0x700:
assume false;

label_0x701:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x709:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_41);

label_0x70d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x714:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x718:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x720:
origDEST_131 := RCX;
origCOUNT_132 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_43);

label_0x724:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_44;
SF := unconstrained_45;
AF := unconstrained_46;
PF := unconstrained_47;

label_0x728:
if (bv2bool(CF)) {
  goto label_0x72b;
}

label_0x72a:
assume false;

label_0x72b:
RAX := (0bv32 ++ 1bv32);

label_0x730:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x738:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x73b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x743:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x749:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x74e:
t_139 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x751:
if (bv2bool(ZF)) {
  goto label_0x754;
}

label_0x753:
assume false;

label_0x754:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x75c:
origDEST_143 := RAX;
origCOUNT_144 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_51);

label_0x760:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x767:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x76b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x773:
origDEST_149 := RCX;
origCOUNT_150 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_53);

label_0x777:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x77b:
if (bv2bool(CF)) {
  goto label_0x77e;
}

label_0x77d:
assume false;

label_0x77e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x786:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x78c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x794:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x79a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x79f:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x7a2:
if (bv2bool(ZF)) {
  goto label_0x7a5;
}

label_0x7a4:
assume false;

label_0x7a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x7ad:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_61);

label_0x7b1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7b8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x7c4:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_62));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_63);

label_0x7c8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_64;
SF := unconstrained_65;
AF := unconstrained_66;
PF := unconstrained_67;

label_0x7cc:
if (bv2bool(CF)) {
  goto label_0x7cf;
}

label_0x7ce:
assume false;

label_0x7cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x7d7:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x7dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x7e5:
t1_173 := RAX;
t2_174 := 12bv64;
RAX := PLUS_64(RAX, t2_174);
CF := bool2bv(LT_64(RAX, t1_173));
OF := AND_1((bool2bv((t1_173[64:63]) == (t2_174[64:63]))), (XOR_1((t1_173[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_173)), t2_174)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7e9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x7f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7f9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7ff:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x804:
t_181 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))))[1:0]));
SF := t_181[64:63];
ZF := bool2bv(0bv64 == t_181);

label_0x807:
if (bv2bool(ZF)) {
  goto label_0x80a;
}

label_0x809:
assume false;

label_0x80a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x812:
origDEST_185 := RAX;
origCOUNT_186 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), CF, LSHIFT_64(origDEST_185, (MINUS_64(64bv64, origCOUNT_186)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv64)), origDEST_185[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), AF, unconstrained_71);

label_0x816:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x81d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x821:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x829:
origDEST_191 := RCX;
origCOUNT_192 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_73);

label_0x82d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x831:
if (bv2bool(CF)) {
  goto label_0x834;
}

label_0x833:
assume false;

label_0x834:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x83c:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x842:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x84a:
t1_197 := RAX;
t2_198 := 16bv64;
RAX := PLUS_64(RAX, t2_198);
CF := bool2bv(LT_64(RAX, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x84e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x856:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x85e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x864:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x869:
t_205 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))))[1:0]));
SF := t_205[64:63];
ZF := bool2bv(0bv64 == t_205);

label_0x86c:
if (bv2bool(ZF)) {
  goto label_0x86f;
}

label_0x86e:
assume false;

label_0x86f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x877:
origDEST_209 := RAX;
origCOUNT_210 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_81);

label_0x87b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x882:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x886:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x88e:
origDEST_215 := RCX;
origCOUNT_216 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), CF, LSHIFT_64(origDEST_215, (MINUS_64(64bv64, origCOUNT_216)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_216 == 1bv64)), origDEST_215[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), AF, unconstrained_83);

label_0x892:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_84;
SF := unconstrained_85;
AF := unconstrained_86;
PF := unconstrained_87;

label_0x896:
if (bv2bool(CF)) {
  goto label_0x899;
}

label_0x898:
assume false;

label_0x899:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x8a1:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x8a7:
RDX := (0bv32 ++ 128bv32);

label_0x8ac:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x8b1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2230bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8b6"} true;
call arbitrary_func();

label_0x8b6:
RDX := (0bv32 ++ 128bv32);

label_0x8bb:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x8c0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2245bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8c5"} true;
call arbitrary_func();

label_0x8c5:
t_221 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), t_221)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_221, (LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))))[1:0]));
SF := t_221[32:31];
ZF := bool2bv(0bv32 == t_221);

label_0x8cd:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x98a;
}

label_0x8d3:
t_225 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), t_225)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_225, (LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))))[1:0]));
SF := t_225[32:31];
ZF := bool2bv(0bv32 == t_225);

label_0x8db:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x98a;
}

label_0x8e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x8e9:
t1_229 := RAX;
t2_230 := 316bv64;
RAX := PLUS_64(RAX, t2_230);
CF := bool2bv(LT_64(RAX, t1_229));
OF := AND_1((bool2bv((t1_229[64:63]) == (t2_230[64:63]))), (XOR_1((t1_229[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_229)), t2_230)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8ef:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x8f1:
t_235 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))), t_235)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_235, (LOAD_LE_32(mem, PLUS_64(RSP, 280bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)), 2bv32)), (XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)), 2bv32)), (XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)))))[1:0]));
SF := t_235[32:31];
ZF := bool2bv(0bv32 == t_235);

label_0x8f8:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x98a;
}

label_0x8fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x906:
t1_239 := RAX;
t2_240 := 320bv64;
RAX := PLUS_64(RAX, t2_240);
CF := bool2bv(LT_64(RAX, t1_239));
OF := AND_1((bool2bv((t1_239[64:63]) == (t2_240[64:63]))), (XOR_1((t1_239[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_239)), t2_240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x90c:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x90e:
t_245 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))), t_245)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_245, (LOAD_LE_32(mem, PLUS_64(RSP, 288bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))))[1:0]));
SF := t_245[32:31];
ZF := bool2bv(0bv32 == t_245);

label_0x915:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x98a;
}

label_0x917:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x91f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x927:
t1_249 := RCX;
t2_250 := 332bv64;
RCX := PLUS_64(RCX, t2_250);
CF := bool2bv(LT_64(RCX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x92e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x935:
t_255 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_255[32:0]);
OF := bool2bv(t_255 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_255 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_88;
SF := unconstrained_89;
ZF := unconstrained_90;
AF := unconstrained_91;

label_0x938:
RCX := (0bv32 ++ RDX[32:0]);

label_0x93a:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x941:
t1_257 := RDX[32:0];
t2_258 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_258));
CF := bool2bv(LT_32((RDX[32:0]), t1_257));
OF := AND_1((bool2bv((t1_257[32:31]) == (t2_258[32:31]))), (XOR_1((t1_257[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_257)), t2_258)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x943:
RCX := (0bv32 ++ RDX[32:0]);

label_0x945:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x948:
t_263 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RCX := t_263[64:0];
OF := bool2bv(t_263 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_263 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_92;
SF := unconstrained_93;
ZF := unconstrained_94;
AF := unconstrained_95;

label_0x94c:
RAX := LOAD_LE_64(mem, RAX);

label_0x94f:
t1_265 := RAX;
t2_266 := RCX;
RAX := PLUS_64(RAX, t2_266);
CF := bool2bv(LT_64(RAX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x952:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x955:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x95d:
t1_271 := RCX;
t2_272 := 8bv64;
RCX := PLUS_64(RCX, t2_272);
CF := bool2bv(LT_64(RCX, t1_271));
OF := AND_1((bool2bv((t1_271[64:63]) == (t2_272[64:63]))), (XOR_1((t1_271[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_271)), t2_272)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x961:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x964:
t_277 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_277)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_277, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))))[1:0]));
SF := t_277[32:31];
ZF := bool2bv(0bv32 == t_277);

label_0x966:
if (bv2bool(ZF)) {
  goto label_0x98a;
}

label_0x968:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x970:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x978:
RDX := PLUS_64(RSP, 80bv64)[64:0];

label_0x97d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x985:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2442bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x98a"} true;
call arbitrary_func();

label_0x98a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x991:
t_281 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_281, 1bv32)), (XOR_32(t_281, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_281)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x993:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), RAX[32:0]);

label_0x99a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x9a1:
t_285 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_285, 1bv32)), (XOR_32(t_285, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_285)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9a3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), RAX[32:0]);

label_0x9aa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x9b1:
t_289 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_289[32:31]) == (1bv32[32:31]))), (XOR_1((t_289[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_289)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9b3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0x9ba:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x9c1:
t_293 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_293[32:31]) == (1bv32[32:31]))), (XOR_1((t_293[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_293)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9c3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 140bv64), RAX[32:0]);

label_0x9ca:
t_297 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), t_297)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_297, (LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)), 2bv32)), (XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)), 2bv32)), (XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)))))[1:0]));
SF := t_297[32:31];
ZF := bool2bv(0bv32 == t_297);

label_0x9d2:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x9df;
}

label_0x9d4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), 0bv32);

label_0x9df:
t_301 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), t_301)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_301, (LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)), 2bv32)), (XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)), 2bv32)), (XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)))))[1:0]));
SF := t_301[32:31];
ZF := bool2bv(0bv32 == t_301);

label_0x9e7:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x9f4;
}

label_0x9e9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), 0bv32);

label_0x9f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x9fc:
t1_305 := RAX;
t2_306 := 316bv64;
RAX := PLUS_64(RAX, t2_306);
CF := bool2bv(LT_64(RAX, t1_305));
OF := AND_1((bool2bv((t1_305[64:63]) == (t2_306[64:63]))), (XOR_1((t1_305[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_305)), t2_306)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa02:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xa04:
t_311 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), t_311)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_311, (LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))))[1:0]));
SF := t_311[32:31];
ZF := bool2bv(0bv32 == t_311);

label_0xa0b:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xa24;
}

label_0xa0d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xa15:
t1_315 := RAX;
t2_316 := 316bv64;
RAX := PLUS_64(RAX, t2_316);
CF := bool2bv(LT_64(RAX, t1_315));
OF := AND_1((bool2bv((t1_315[64:63]) == (t2_316[64:63]))), (XOR_1((t1_315[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_315)), t2_316)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa1b:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xa1d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0xa24:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xa2c:
t1_321 := RAX;
t2_322 := 320bv64;
RAX := PLUS_64(RAX, t2_322);
CF := bool2bv(LT_64(RAX, t1_321));
OF := AND_1((bool2bv((t1_321[64:63]) == (t2_322[64:63]))), (XOR_1((t1_321[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_321)), t2_322)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa32:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xa34:
t_327 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), t_327)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_327, (LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))))[1:0]));
SF := t_327[32:31];
ZF := bool2bv(0bv32 == t_327);

label_0xa3b:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xa54;
}

label_0xa3d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xa45:
t1_331 := RAX;
t2_332 := 320bv64;
RAX := PLUS_64(RAX, t2_332);
CF := bool2bv(LT_64(RAX, t1_331));
OF := AND_1((bool2bv((t1_331[64:63]) == (t2_332[64:63]))), (XOR_1((t1_331[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_331)), t2_332)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa4b:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xa4d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 140bv64), RAX[32:0]);

label_0xa54:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 132bv64)));

label_0xa5b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), RAX[32:0]);

label_0xa5f:
goto label_0xa6b;

label_0xa61:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0xa65:
t_337 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_337[32:31]) == (1bv32[32:31]))), (XOR_1((t_337[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_337)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa67:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), RAX[32:0]);

label_0xa6b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0xa72:
t_341 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), t_341)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_341, (LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)), 2bv32)), (XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)), 2bv32)), (XOR_32((RSHIFT_32(t_341, 4bv32)), t_341)))))[1:0]));
SF := t_341[32:31];
ZF := bool2bv(0bv32 == t_341);

label_0xa76:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0xb0e;
}

label_0xa7c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0xa83:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), RAX[32:0]);

label_0xa87:
goto label_0xa93;

label_0xa89:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0xa8d:
t_345 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_345[32:31]) == (1bv32[32:31]))), (XOR_1((t_345[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_345)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa8f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), RAX[32:0]);

label_0xa93:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0xa9a:
t_349 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), t_349)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_349, (LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_349, 4bv32)), t_349)), 2bv32)), (XOR_32((RSHIFT_32(t_349, 4bv32)), t_349)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_349, 4bv32)), t_349)), 2bv32)), (XOR_32((RSHIFT_32(t_349, 4bv32)), t_349)))))[1:0]));
SF := t_349[32:31];
ZF := bool2bv(0bv32 == t_349);

label_0xa9e:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0xb09;
}

label_0xaa0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xaa8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xab0:
t1_353 := RCX;
t2_354 := 332bv64;
RCX := PLUS_64(RCX, t2_354);
CF := bool2bv(LT_64(RCX, t1_353));
OF := AND_1((bool2bv((t1_353[64:63]) == (t2_354[64:63]))), (XOR_1((t1_353[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_353)), t2_354)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xab7:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0xabb:
t_359 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_359[32:0]);
OF := bool2bv(t_359 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_359 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_96;
SF := unconstrained_97;
ZF := unconstrained_98;
AF := unconstrained_99;

label_0xabe:
RCX := (0bv32 ++ RDX[32:0]);

label_0xac0:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0xac4:
t1_361 := RDX[32:0];
t2_362 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_362));
CF := bool2bv(LT_32((RDX[32:0]), t1_361));
OF := AND_1((bool2bv((t1_361[32:31]) == (t2_362[32:31]))), (XOR_1((t1_361[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_361)), t2_362)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xac6:
RCX := (0bv32 ++ RDX[32:0]);

label_0xac8:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0xacb:
t_367 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RCX := t_367[64:0];
OF := bool2bv(t_367 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_367 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_100;
SF := unconstrained_101;
ZF := unconstrained_102;
AF := unconstrained_103;

label_0xacf:
RAX := LOAD_LE_64(mem, RAX);

label_0xad2:
t1_369 := RAX;
t2_370 := RCX;
RAX := PLUS_64(RAX, t2_370);
CF := bool2bv(LT_64(RAX, t1_369));
OF := AND_1((bool2bv((t1_369[64:63]) == (t2_370[64:63]))), (XOR_1((t1_369[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_369)), t2_370)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xad5:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0xad8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xae0:
t1_375 := RCX;
t2_376 := 8bv64;
RCX := PLUS_64(RCX, t2_376);
CF := bool2bv(LT_64(RCX, t1_375));
OF := AND_1((bool2bv((t1_375[64:63]) == (t2_376[64:63]))), (XOR_1((t1_375[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_375)), t2_376)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xae4:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xae7:
t_381 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_381)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_381, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)), 2bv32)), (XOR_32((RSHIFT_32(t_381, 4bv32)), t_381)))))[1:0]));
SF := t_381[32:31];
ZF := bool2bv(0bv32 == t_381);

label_0xae9:
if (bv2bool(ZF)) {
  goto label_0xb07;
}

label_0xaeb:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0xaf0:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0xaf5:
RDX := PLUS_64(RSP, 80bv64)[64:0];

label_0xafa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xb02:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2823bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb07"} true;
call arbitrary_func();

label_0xb07:
goto label_0xa89;

label_0xb09:
goto label_0xa61;

label_0xb0e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0xb12:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0xb16:
mem := STORE_LE_8(mem, PLUS_64(RSP, 124bv64), 0bv8);

label_0xb1b:
t_385 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), t_385)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_385, (LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))))[1:0]));
SF := t_385[32:31];
ZF := bool2bv(0bv32 == t_385);

label_0xb20:
if (bv2bool(ZF)) {
  goto label_0xb93;
}

label_0xb22:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xb2a:
t1_389 := RAX;
t2_390 := 20bv64;
RAX := PLUS_64(RAX, t2_390);
CF := bool2bv(LT_64(RAX, t1_389));
OF := AND_1((bool2bv((t1_389[64:63]) == (t2_390[64:63]))), (XOR_1((t1_389[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_389)), t2_390)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb2e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0xb31:
t_395 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_104;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)), 2bv32)), (XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)), 2bv32)), (XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)))))[1:0]));
SF := t_395[32:31];
ZF := bool2bv(0bv32 == t_395);

label_0xb33:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb93;
}

label_0xb35:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 124bv64))));

label_0xb3a:
t_399 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)), 2bv32)), (XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)), 2bv32)), (XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)))))[1:0]));
SF := t_399[32:31];
ZF := bool2bv(0bv32 == t_399);

label_0xb3c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb64;
}

label_0xb3e:
R8 := PLUS_64(RSP, 48bv64)[64:0];

label_0xb43:
RDX := PLUS_64(RSP, 80bv64)[64:0];

label_0xb48:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xb50:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2901bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb55"} true;
call arbitrary_func();

label_0xb55:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0xb59:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0xb5d:
mem := STORE_LE_8(mem, PLUS_64(RSP, 125bv64), 1bv8);

label_0xb62:
goto label_0xb88;

label_0xb64:
R8 := PLUS_64(RSP, 80bv64)[64:0];

label_0xb69:
RDX := PLUS_64(RSP, 48bv64)[64:0];

label_0xb6e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xb76:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2939bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb7b"} true;
call arbitrary_func();

label_0xb7b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0xb7f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0xb83:
mem := STORE_LE_8(mem, PLUS_64(RSP, 125bv64), 0bv8);

label_0xb88:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 125bv64))));

label_0xb8d:
mem := STORE_LE_8(mem, PLUS_64(RSP, 124bv64), RAX[32:0][8:0]);

label_0xb91:
goto label_0xb1b;

label_0xb93:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xb98:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2973bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb9d"} true;
call arbitrary_func();

label_0xb9d:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0xba2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2983bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xba7"} true;
call arbitrary_func();

label_0xba7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xbaf:
t1_403 := RAX;
t2_404 := 12bv64;
RAX := PLUS_64(RAX, t2_404);
CF := bool2bv(LT_64(RAX, t1_403));
OF := AND_1((bool2bv((t1_403[64:63]) == (t2_404[64:63]))), (XOR_1((t1_403[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_403)), t2_404)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbb3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0xbbb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xbc3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbc9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbce:
t_411 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_411, 4bv64)), t_411)), 2bv64)), (XOR_64((RSHIFT_64(t_411, 4bv64)), t_411)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_411, 4bv64)), t_411)), 2bv64)), (XOR_64((RSHIFT_64(t_411, 4bv64)), t_411)))))[1:0]));
SF := t_411[64:63];
ZF := bool2bv(0bv64 == t_411);

label_0xbd1:
if (bv2bool(ZF)) {
  goto label_0xbd4;
}

label_0xbd3:
assume false;

label_0xbd4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xbdc:
origDEST_415 := RAX;
origCOUNT_416 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), CF, LSHIFT_64(origDEST_415, (MINUS_64(64bv64, origCOUNT_416)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_416 == 1bv64)), origDEST_415[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_416 == 0bv64)), AF, unconstrained_109);

label_0xbe0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbe7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbeb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xbf3:
origDEST_421 := RCX;
origCOUNT_422 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), CF, LSHIFT_64(origDEST_421, (MINUS_64(64bv64, origCOUNT_422)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_422 == 1bv64)), origDEST_421[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_422 == 0bv64)), AF, unconstrained_111);

label_0xbf7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_112;
SF := unconstrained_113;
AF := unconstrained_114;
PF := unconstrained_115;

label_0xbfb:
if (bv2bool(CF)) {
  goto label_0xbfe;
}

label_0xbfd:
assume false;

label_0xbfe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xc06:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xc0e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xc10:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc12:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc1a:
t1_427 := RAX;
t2_428 := 16bv64;
RAX := PLUS_64(RAX, t2_428);
CF := bool2bv(LT_64(RAX, t1_427));
OF := AND_1((bool2bv((t1_427[64:63]) == (t2_428[64:63]))), (XOR_1((t1_427[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_427)), t2_428)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc1e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0xc26:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xc2e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc34:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc39:
t_435 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_435, 4bv64)), t_435)), 2bv64)), (XOR_64((RSHIFT_64(t_435, 4bv64)), t_435)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_435, 4bv64)), t_435)), 2bv64)), (XOR_64((RSHIFT_64(t_435, 4bv64)), t_435)))))[1:0]));
SF := t_435[64:63];
ZF := bool2bv(0bv64 == t_435);

label_0xc3c:
if (bv2bool(ZF)) {
  goto label_0xc3f;
}

label_0xc3e:
assume false;

label_0xc3f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xc47:
origDEST_439 := RAX;
origCOUNT_440 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), CF, LSHIFT_64(origDEST_439, (MINUS_64(64bv64, origCOUNT_440)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_440 == 1bv64)), origDEST_439[64:63], unconstrained_118));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), AF, unconstrained_119);

label_0xc4b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc52:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc56:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xc5e:
origDEST_445 := RCX;
origCOUNT_446 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), CF, LSHIFT_64(origDEST_445, (MINUS_64(64bv64, origCOUNT_446)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_446 == 1bv64)), origDEST_445[64:63], unconstrained_120));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), AF, unconstrained_121);

label_0xc62:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_122;
SF := unconstrained_123;
AF := unconstrained_124;
PF := unconstrained_125;

label_0xc66:
if (bv2bool(CF)) {
  goto label_0xc69;
}

label_0xc68:
assume false;

label_0xc69:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xc71:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xc79:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xc7b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc7d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc85:
t1_451 := RAX;
t2_452 := 20bv64;
RAX := PLUS_64(RAX, t2_452);
CF := bool2bv(LT_64(RAX, t1_451));
OF := AND_1((bool2bv((t1_451[64:63]) == (t2_452[64:63]))), (XOR_1((t1_451[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_451)), t2_452)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc89:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0xc91:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc98:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RCX);

label_0xca0:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0xca5:
origDEST_457 := RCX;
origCOUNT_458 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), CF, LSHIFT_64(origDEST_457, (MINUS_64(64bv64, origCOUNT_458)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_458 == 1bv64)), origDEST_457[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_458 == 0bv64)), AF, unconstrained_127);

label_0xca9:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xcb1:
t1_463 := RDX;
t2_464 := RCX;
RDX := PLUS_64(RDX, t2_464);
CF := bool2bv(LT_64(RDX, t1_463));
OF := AND_1((bool2bv((t1_463[64:63]) == (t2_464[64:63]))), (XOR_1((t1_463[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_463)), t2_464)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0xcb4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RDX);

label_0xcbc:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0xcc1:
origDEST_469 := RCX;
origCOUNT_470 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), CF, LSHIFT_64(origDEST_469, (MINUS_64(64bv64, origCOUNT_470)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_470 == 1bv64)), origDEST_469[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), AF, unconstrained_129);

label_0xcc5:
RCX := AND_64(RCX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_130;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xcc9:
RDX := (RDX[64:8]) ++ 254bv8;

label_0xccb:
origDEST_477 := RDX[32:0][8:0];
origCOUNT_478 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), CF, RSHIFT_8(origDEST_477, (MINUS_8(8bv8, origCOUNT_478)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_478 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv8)), AF, unconstrained_132);

label_0xccd:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xcd0:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xcd8:
mem := STORE_LE_8(mem, RDX, AND_8((LOAD_LE_8(mem, RDX)), (RCX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RDX)), 4bv8)), (LOAD_LE_8(mem, RDX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RDX)), 4bv8)), (LOAD_LE_8(mem, RDX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RDX)), 4bv8)), (LOAD_LE_8(mem, RDX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RDX)), 4bv8)), (LOAD_LE_8(mem, RDX)))))))[1:0]));
SF := LOAD_LE_8(mem, RDX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RDX)));

label_0xcda:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xce2:
t_485 := RCX;
RCX := MINUS_64(RCX, 2bv64);
CF := bool2bv(LT_64(t_485, 2bv64));
OF := AND_64((XOR_64(t_485, 2bv64)), (XOR_64(t_485, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_485)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xce6:
RDI := RCX;

label_0xce9:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_134;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xceb:
RCX := (0bv32 ++ 2bv32);

label_0xcf0:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xcf2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xcfa:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0xcfd:
t1_489 := RSP;
t2_490 := 256bv64;
RSP := PLUS_64(RSP, t2_490);
CF := bool2bv(LT_64(RSP, t1_489));
OF := AND_1((bool2bv((t1_489[64:63]) == (t2_490[64:63]))), (XOR_1((t1_489[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_489)), t2_490)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xd04:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0xd05:

ra_495 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_126,origCOUNT_132,origCOUNT_14,origCOUNT_144,origCOUNT_150,origCOUNT_162,origCOUNT_168,origCOUNT_186,origCOUNT_192,origCOUNT_210,origCOUNT_216,origCOUNT_22,origCOUNT_416,origCOUNT_42,origCOUNT_422,origCOUNT_440,origCOUNT_446,origCOUNT_458,origCOUNT_470,origCOUNT_478,origCOUNT_48,origCOUNT_76,origCOUNT_8,origCOUNT_82,origDEST_125,origDEST_13,origDEST_131,origDEST_143,origDEST_149,origDEST_161,origDEST_167,origDEST_185,origDEST_191,origDEST_209,origDEST_21,origDEST_215,origDEST_41,origDEST_415,origDEST_421,origDEST_439,origDEST_445,origDEST_457,origDEST_469,origDEST_47,origDEST_477,origDEST_7,origDEST_75,origDEST_81,ra_495,t1_103,t1_113,t1_173,t1_197,t1_229,t1_239,t1_249,t1_257,t1_265,t1_271,t1_29,t1_305,t1_315,t1_321,t1_331,t1_353,t1_361,t1_369,t1_375,t1_389,t1_403,t1_427,t1_451,t1_463,t1_489,t1_53,t1_63,t1_87,t1_97,t2_104,t2_114,t2_174,t2_198,t2_230,t2_240,t2_250,t2_258,t2_266,t2_272,t2_30,t2_306,t2_316,t2_322,t2_332,t2_354,t2_362,t2_370,t2_376,t2_390,t2_404,t2_428,t2_452,t2_464,t2_490,t2_54,t2_64,t2_88,t2_98,t_1,t_109,t_111,t_121,t_139,t_157,t_181,t_205,t_221,t_225,t_235,t_245,t_255,t_263,t_277,t_281,t_285,t_289,t_293,t_297,t_3,t_301,t_311,t_327,t_337,t_341,t_345,t_349,t_359,t_367,t_37,t_381,t_385,t_395,t_399,t_411,t_435,t_485,t_59,t_71,t_93;

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
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_126: bv64;
var origCOUNT_132: bv64;
var origCOUNT_14: bv64;
var origCOUNT_144: bv64;
var origCOUNT_150: bv64;
var origCOUNT_162: bv64;
var origCOUNT_168: bv64;
var origCOUNT_186: bv64;
var origCOUNT_192: bv64;
var origCOUNT_210: bv64;
var origCOUNT_216: bv64;
var origCOUNT_22: bv64;
var origCOUNT_416: bv64;
var origCOUNT_42: bv64;
var origCOUNT_422: bv64;
var origCOUNT_440: bv64;
var origCOUNT_446: bv64;
var origCOUNT_458: bv64;
var origCOUNT_470: bv64;
var origCOUNT_478: bv8;
var origCOUNT_48: bv64;
var origCOUNT_76: bv64;
var origCOUNT_8: bv64;
var origCOUNT_82: bv64;
var origDEST_125: bv64;
var origDEST_13: bv64;
var origDEST_131: bv64;
var origDEST_143: bv64;
var origDEST_149: bv64;
var origDEST_161: bv64;
var origDEST_167: bv64;
var origDEST_185: bv64;
var origDEST_191: bv64;
var origDEST_209: bv64;
var origDEST_21: bv64;
var origDEST_215: bv64;
var origDEST_41: bv64;
var origDEST_415: bv64;
var origDEST_421: bv64;
var origDEST_439: bv64;
var origDEST_445: bv64;
var origDEST_457: bv64;
var origDEST_469: bv64;
var origDEST_47: bv64;
var origDEST_477: bv8;
var origDEST_7: bv64;
var origDEST_75: bv64;
var origDEST_81: bv64;
var ra_495: bv64;
var t1_103: bv64;
var t1_113: bv64;
var t1_173: bv64;
var t1_197: bv64;
var t1_229: bv64;
var t1_239: bv64;
var t1_249: bv64;
var t1_257: bv32;
var t1_265: bv64;
var t1_271: bv64;
var t1_29: bv64;
var t1_305: bv64;
var t1_315: bv64;
var t1_321: bv64;
var t1_331: bv64;
var t1_353: bv64;
var t1_361: bv32;
var t1_369: bv64;
var t1_375: bv64;
var t1_389: bv64;
var t1_403: bv64;
var t1_427: bv64;
var t1_451: bv64;
var t1_463: bv64;
var t1_489: bv64;
var t1_53: bv64;
var t1_63: bv64;
var t1_87: bv64;
var t1_97: bv64;
var t2_104: bv64;
var t2_114: bv64;
var t2_174: bv64;
var t2_198: bv64;
var t2_230: bv64;
var t2_240: bv64;
var t2_250: bv64;
var t2_258: bv32;
var t2_266: bv64;
var t2_272: bv64;
var t2_30: bv64;
var t2_306: bv64;
var t2_316: bv64;
var t2_322: bv64;
var t2_332: bv64;
var t2_354: bv64;
var t2_362: bv32;
var t2_370: bv64;
var t2_376: bv64;
var t2_390: bv64;
var t2_404: bv64;
var t2_428: bv64;
var t2_452: bv64;
var t2_464: bv64;
var t2_490: bv64;
var t2_54: bv64;
var t2_64: bv64;
var t2_88: bv64;
var t2_98: bv64;
var t_1: bv64;
var t_109: bv64;
var t_111: bv128;
var t_121: bv64;
var t_139: bv64;
var t_157: bv64;
var t_181: bv64;
var t_205: bv64;
var t_221: bv32;
var t_225: bv32;
var t_235: bv32;
var t_245: bv32;
var t_255: bv64;
var t_263: bv128;
var t_277: bv32;
var t_281: bv32;
var t_285: bv32;
var t_289: bv32;
var t_293: bv32;
var t_297: bv32;
var t_3: bv64;
var t_301: bv32;
var t_311: bv32;
var t_327: bv32;
var t_337: bv32;
var t_341: bv32;
var t_345: bv32;
var t_349: bv32;
var t_359: bv64;
var t_367: bv128;
var t_37: bv64;
var t_381: bv32;
var t_385: bv32;
var t_395: bv32;
var t_399: bv32;
var t_411: bv64;
var t_435: bv64;
var t_485: bv64;
var t_59: bv16;
var t_71: bv64;
var t_93: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(896bv64);
axiom policy(1312bv64);
axiom policy(3344bv64);
axiom policy(4224bv64);
axiom policy(4608bv64);
axiom policy(5136bv64);
axiom policy(7296bv64);
