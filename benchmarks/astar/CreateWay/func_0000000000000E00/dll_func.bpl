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
axiom _function_addr_low == 3584bv64;
axiom _function_addr_high == 5078bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xe00:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0xe05:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0xe0a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0xe0e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xe13:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0xe14:
t_3 := RSP;
RSP := MINUS_64(RSP, 384bv64);
CF := bool2bv(LT_64(t_3, 384bv64));
OF := AND_64((XOR_64(t_3, 384bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 384bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xe1b:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0xe20:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0xe28:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xe2f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0xe37:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xe3f:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0xe43:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0xe4b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xe53:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0xe57:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe5b:
RCX := (0bv32 ++ 245bv32);

label_0xe60:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RCX);

label_0xe68:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xe73:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0xe76:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xe7e:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xe86:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0xe8a:
R8 := (R8[64:16]) ++ 1bv16;

label_0xe8f:
RDX := (RDX[64:16]) ++ 65535bv16;

label_0xe93:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xe98:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3741bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe9d"} true;
call arbitrary_func();

label_0xe9d:
R8 := (R8[64:16]) ++ 1bv16;

label_0xea2:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_9;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xea4:
RCX := PLUS_64(RSP, 84bv64)[64:0];

label_0xea9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3758bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xeae"} true;
call arbitrary_func();

label_0xeae:
R8 := (R8[64:16]) ++ 1bv16;

label_0xeb3:
RDX := (RDX[64:16]) ++ 1bv16;

label_0xeb7:
RCX := PLUS_64(RSP, 88bv64)[64:0];

label_0xebc:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3777bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xec1"} true;
call arbitrary_func();

label_0xec1:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xec4:
RDX := (RDX[64:16]) ++ 1bv16;

label_0xec8:
RCX := PLUS_64(RSP, 92bv64)[64:0];

label_0xecd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3794bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xed2"} true;
call arbitrary_func();

label_0xed2:
R8 := (R8[64:16]) ++ 65535bv16;

label_0xed7:
RDX := (RDX[64:16]) ++ 1bv16;

label_0xedb:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0xee0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3813bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xee5"} true;
call arbitrary_func();

label_0xee5:
R8 := (R8[64:16]) ++ 65535bv16;

label_0xeea:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xeec:
RCX := PLUS_64(RSP, 100bv64)[64:0];

label_0xef1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3830bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xef6"} true;
call arbitrary_func();

label_0xef6:
R8 := (R8[64:16]) ++ 65535bv16;

label_0xefb:
RDX := (RDX[64:16]) ++ 65535bv16;

label_0xeff:
RCX := PLUS_64(RSP, 104bv64)[64:0];

label_0xf04:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3849bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf09"} true;
call arbitrary_func();

label_0xf09:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_12;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xf0c:
RDX := (RDX[64:16]) ++ 65535bv16;

label_0xf10:
RCX := PLUS_64(RSP, 108bv64)[64:0];

label_0xf15:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3866bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf1a"} true;
call arbitrary_func();

label_0xf1a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xf22:
t1_29 := RAX;
t2_30 := 168bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf28:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0xf2b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), RAX[32:0]);

label_0xf32:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0xf3a:
t_35 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_35[64:0];
OF := bool2bv(t_35 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_35 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_13;
SF := unconstrained_14;
ZF := unconstrained_15;
AF := unconstrained_16;

label_0xf3e:
RCX := RAX;

label_0xf41:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3910bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf46"} true;
call arbitrary_func();

label_0xf46:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0xf4e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xf56:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf5c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xf61:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0xf64:
if (bv2bool(ZF)) {
  goto label_0xf67;
}

label_0xf66:
assume false;

label_0xf67:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xf6f:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_20);

label_0xf73:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf7a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf7e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xf86:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_22);

label_0xf8a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_23;
SF := unconstrained_24;
AF := unconstrained_25;
PF := unconstrained_26;

label_0xf8e:
if (bv2bool(CF)) {
  goto label_0xf91;
}

label_0xf90:
assume false;

label_0xf91:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xf99:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xfa1:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xfa4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xfac:
t1_55 := RAX;
t2_56 := 32bv64;
RAX := PLUS_64(RAX, t2_56);
CF := bool2bv(LT_64(RAX, t1_55));
OF := AND_1((bool2bv((t1_55[64:63]) == (t2_56[64:63]))), (XOR_1((t1_55[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_55)), t2_56)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfb0:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xfb2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), RAX[32:0]);

label_0xfb9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xfc1:
t1_61 := RAX;
t2_62 := 128bv64;
RAX := PLUS_64(RAX, t2_62);
CF := bool2bv(LT_64(RAX, t1_61));
OF := AND_1((bool2bv((t1_61[64:63]) == (t2_62[64:63]))), (XOR_1((t1_61[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_61)), t2_62)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfc7:
RAX := LOAD_LE_64(mem, RAX);

label_0xfca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0xfd2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 416bv64)));

label_0xfd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0xfe0:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 408bv64)));

label_0xfe7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xfef:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4084bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xff4"} true;
call arbitrary_func();

label_0xff4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 152bv64), RAX[32:0]);

label_0xffb:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 408bv64)));

label_0x1002:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x100a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4111bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x100f"} true;
call arbitrary_func();

label_0x100f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 156bv64), RAX[32:0]);

label_0x1016:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x101d:
t_67 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 2bv32));
CF := bool2bv(LT_32(t_67, 2bv32));
OF := AND_32((XOR_32(t_67, 2bv32)), (XOR_32(t_67, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_67)), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1020:
mem := STORE_LE_32(mem, PLUS_64(RSP, 220bv64), RAX[32:0]);

label_0x1027:
goto label_0x1039;

label_0x1029:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)));

label_0x1030:
t_71 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_71, 1bv32)), (XOR_32(t_71, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_71)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1032:
mem := STORE_LE_32(mem, PLUS_64(RSP, 220bv64), RAX[32:0]);

label_0x1039:
t_75 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))), t_75)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_75, (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))))[1:0]));
SF := t_75[32:31];
ZF := bool2bv(0bv32 == t_75);

label_0x1041:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x18e2;
}

label_0x1047:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x104e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x1056:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4187bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x105b"} true;
call arbitrary_func();

label_0x105b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 160bv64), RAX[32:0]);

label_0x1062:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x1069:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x1071:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4214bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1076"} true;
call arbitrary_func();

label_0x1076:
mem := STORE_LE_32(mem, PLUS_64(RSP, 164bv64), RAX[32:0]);

label_0x107d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x1084:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x108b:
t_79 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_79, (RAX[32:0])));
OF := AND_32((XOR_32(t_79, (RAX[32:0]))), (XOR_32(t_79, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_79)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x108d:
RAX := (0bv32 ++ RCX[32:0]);

label_0x108f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 184bv64), RAX[32:0]);

label_0x1096:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 164bv64)));

label_0x109d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 156bv64)));

label_0x10a4:
t_83 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_83, (RAX[32:0])));
OF := AND_32((XOR_32(t_83, (RAX[32:0]))), (XOR_32(t_83, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_83)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x10a6:
RAX := (0bv32 ++ RCX[32:0]);

label_0x10a8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 188bv64), RAX[32:0]);

label_0x10af:
t_87 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), t_87)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_87, (LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))))[1:0]));
SF := t_87[32:31];
ZF := bool2bv(0bv32 == t_87);

label_0x10b7:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x10c6;
}

label_0x10b9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 184bv64), 1bv32);

label_0x10c4:
goto label_0x10db;

label_0x10c6:
t_91 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))), t_91)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_91, (LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))))[1:0]));
SF := t_91[32:31];
ZF := bool2bv(0bv32 == t_91);

label_0x10ce:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x10db;
}

label_0x10d0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 184bv64), 4294967295bv32);

label_0x10db:
t_95 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), t_95)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_95, (LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))))[1:0]));
SF := t_95[32:31];
ZF := bool2bv(0bv32 == t_95);

label_0x10e3:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x10f2;
}

label_0x10e5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 188bv64), 1bv32);

label_0x10f0:
goto label_0x1107;

label_0x10f2:
t_99 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))), t_99)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_99, (LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))))[1:0]));
SF := t_99[32:31];
ZF := bool2bv(0bv32 == t_99);

label_0x10fa:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1107;
}

label_0x10fc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 188bv64), 4294967295bv32);

label_0x1107:
t_103 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_103[32:0]);
OF := bool2bv(t_103 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_103 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_27;
SF := unconstrained_28;
ZF := unconstrained_29;
AF := unconstrained_30;

label_0x110f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4373bv64)), 0bv64)));

label_0x1115:
t_105 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)))))));
RCX := (0bv32 ++ t_105[32:0]);
OF := bool2bv(t_105 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_105 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_31;
SF := unconstrained_32;
ZF := unconstrained_33;
AF := unconstrained_34;

label_0x111d:
t_107 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_107)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_107, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))))[1:0]));
SF := t_107[32:31];
ZF := bool2bv(0bv32 == t_107);

label_0x111f:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x112e;
}

label_0x1121:
mem := STORE_LE_32(mem, PLUS_64(RSP, 192bv64), 1bv32);

label_0x112c:
goto label_0x1139;

label_0x112e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 192bv64), 4294967295bv32);

label_0x1139:
t_111 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_111[32:0]);
OF := bool2bv(t_111 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_111 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_35;
SF := unconstrained_36;
ZF := unconstrained_37;
AF := unconstrained_38;

label_0x1141:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4423bv64)), 0bv64)));

label_0x1147:
t_113 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)))))));
RCX := (0bv32 ++ t_113[32:0]);
OF := bool2bv(t_113 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_113 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_39;
SF := unconstrained_40;
ZF := unconstrained_41;
AF := unconstrained_42;

label_0x114f:
t_115 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_115)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_115, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)), 2bv32)), (XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)), 2bv32)), (XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)))))[1:0]));
SF := t_115[32:31];
ZF := bool2bv(0bv32 == t_115);

label_0x1151:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1160;
}

label_0x1153:
mem := STORE_LE_32(mem, PLUS_64(RSP, 196bv64), 1bv32);

label_0x115e:
goto label_0x116b;

label_0x1160:
mem := STORE_LE_32(mem, PLUS_64(RSP, 196bv64), 4294967295bv32);

label_0x116b:
t_119 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_119[32:0]);
OF := bool2bv(t_119 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_119 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_43;
SF := unconstrained_44;
ZF := unconstrained_45;
AF := unconstrained_46;

label_0x1173:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4473bv64)), 0bv64)));

label_0x1179:
t_121 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)))))));
RCX := (0bv32 ++ t_121[32:0]);
OF := bool2bv(t_121 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_121 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_47;
SF := unconstrained_48;
ZF := unconstrained_49;
AF := unconstrained_50;

label_0x1181:
t_123 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_123)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_123, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)), 2bv32)), (XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)), 2bv32)), (XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)))))[1:0]));
SF := t_123[32:31];
ZF := bool2bv(0bv32 == t_123);

label_0x1183:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1192;
}

label_0x1185:
mem := STORE_LE_32(mem, PLUS_64(RSP, 200bv64), 1bv32);

label_0x1190:
goto label_0x119d;

label_0x1192:
mem := STORE_LE_32(mem, PLUS_64(RSP, 200bv64), 4294967295bv32);

label_0x119d:
t_127 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 188bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_127[32:0]);
OF := bool2bv(t_127 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_127 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_51;
SF := unconstrained_52;
ZF := unconstrained_53;
AF := unconstrained_54;

label_0x11a5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4523bv64)), 0bv64)));

label_0x11ab:
t_129 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)))))));
RCX := (0bv32 ++ t_129[32:0]);
OF := bool2bv(t_129 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_129 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_55;
SF := unconstrained_56;
ZF := unconstrained_57;
AF := unconstrained_58;

label_0x11b3:
t_131 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_131)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_131, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))))[1:0]));
SF := t_131[32:31];
ZF := bool2bv(0bv32 == t_131);

label_0x11b5:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x11c4;
}

label_0x11b7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 204bv64), 1bv32);

label_0x11c2:
goto label_0x11cf;

label_0x11c4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 204bv64), 4294967295bv32);

label_0x11cf:
t_135 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), t_135)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_135, (LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))))[1:0]));
SF := t_135[32:31];
ZF := bool2bv(0bv32 == t_135);

label_0x11d7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x120e;
}

label_0x11d9:
t_139 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), t_139)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_139, (LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_139, 4bv32)), t_139)), 2bv32)), (XOR_32((RSHIFT_32(t_139, 4bv32)), t_139)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_139, 4bv32)), t_139)), 2bv32)), (XOR_32((RSHIFT_32(t_139, 4bv32)), t_139)))))[1:0]));
SF := t_139[32:31];
ZF := bool2bv(0bv32 == t_139);

label_0x11e1:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x120e;
}

label_0x11e3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 0bv32);

label_0x11ee:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 1bv32);

label_0x11f9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 1bv32);

label_0x1204:
goto label_0x13dc;

label_0x1209:
goto label_0x13dc;

label_0x120e:
t_143 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), t_143)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_143, (LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))))[1:0]));
SF := t_143[32:31];
ZF := bool2bv(0bv32 == t_143);

label_0x1216:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x124d;
}

label_0x1218:
t_147 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), t_147)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_147, (LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_147, 4bv32)), t_147)), 2bv32)), (XOR_32((RSHIFT_32(t_147, 4bv32)), t_147)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_147, 4bv32)), t_147)), 2bv32)), (XOR_32((RSHIFT_32(t_147, 4bv32)), t_147)))))[1:0]));
SF := t_147[32:31];
ZF := bool2bv(0bv32 == t_147);

label_0x1220:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x124d;
}

label_0x1222:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 1bv32);

label_0x122d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 1bv32);

label_0x1238:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 2bv32);

label_0x1243:
goto label_0x13dc;

label_0x1248:
goto label_0x13dc;

label_0x124d:
t_151 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_151)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_151, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)), 2bv32)), (XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)), 2bv32)), (XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)))))[1:0]));
SF := t_151[32:31];
ZF := bool2bv(0bv32 == t_151);

label_0x1255:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x128c;
}

label_0x1257:
t_155 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), t_155)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_155, (LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)), 2bv32)), (XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)), 2bv32)), (XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)))))[1:0]));
SF := t_155[32:31];
ZF := bool2bv(0bv32 == t_155);

label_0x125f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x128c;
}

label_0x1261:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 1bv32);

label_0x126c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 0bv32);

label_0x1277:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 3bv32);

label_0x1282:
goto label_0x13dc;

label_0x1287:
goto label_0x13dc;

label_0x128c:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x1294:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x12cb;
}

label_0x1296:
t_163 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_163)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_163, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_163, 4bv32)), t_163)), 2bv32)), (XOR_32((RSHIFT_32(t_163, 4bv32)), t_163)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_163, 4bv32)), t_163)), 2bv32)), (XOR_32((RSHIFT_32(t_163, 4bv32)), t_163)))))[1:0]));
SF := t_163[32:31];
ZF := bool2bv(0bv32 == t_163);

label_0x129e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x12cb;
}

label_0x12a0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 1bv32);

label_0x12ab:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 4294967295bv32);

label_0x12b6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 4bv32);

label_0x12c1:
goto label_0x13dc;

label_0x12c6:
goto label_0x13dc;

label_0x12cb:
t_167 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), t_167)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_167, (LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_167, 4bv32)), t_167)), 2bv32)), (XOR_32((RSHIFT_32(t_167, 4bv32)), t_167)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_167, 4bv32)), t_167)), 2bv32)), (XOR_32((RSHIFT_32(t_167, 4bv32)), t_167)))))[1:0]));
SF := t_167[32:31];
ZF := bool2bv(0bv32 == t_167);

label_0x12d3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x130a;
}

label_0x12d5:
t_171 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), t_171)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_171, (LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))))[1:0]));
SF := t_171[32:31];
ZF := bool2bv(0bv32 == t_171);

label_0x12dd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x130a;
}

label_0x12df:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 0bv32);

label_0x12ea:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 4294967295bv32);

label_0x12f5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 5bv32);

label_0x1300:
goto label_0x13dc;

label_0x1305:
goto label_0x13dc;

label_0x130a:
t_175 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))), t_175)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_175, (LOAD_LE_32(mem, PLUS_64(RSP, 192bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))))[1:0]));
SF := t_175[32:31];
ZF := bool2bv(0bv32 == t_175);

label_0x1312:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1349;
}

label_0x1314:
t_179 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), t_179)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_179, (LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))))[1:0]));
SF := t_179[32:31];
ZF := bool2bv(0bv32 == t_179);

label_0x131c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1349;
}

label_0x131e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 4294967295bv32);

label_0x1329:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 4294967295bv32);

label_0x1334:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 6bv32);

label_0x133f:
goto label_0x13dc;

label_0x1344:
goto label_0x13dc;

label_0x1349:
t_183 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))), t_183)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_183, (LOAD_LE_32(mem, PLUS_64(RSP, 196bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))))[1:0]));
SF := t_183[32:31];
ZF := bool2bv(0bv32 == t_183);

label_0x1351:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1382;
}

label_0x1353:
t_187 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_187)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_187, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))))[1:0]));
SF := t_187[32:31];
ZF := bool2bv(0bv32 == t_187);

label_0x135b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1382;
}

label_0x135d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 4294967295bv32);

label_0x1368:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 0bv32);

label_0x1373:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 7bv32);

label_0x137e:
goto label_0x13dc;

label_0x1380:
goto label_0x13dc;

label_0x1382:
t_191 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_191)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_191, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))))[1:0]));
SF := t_191[32:31];
ZF := bool2bv(0bv32 == t_191);

label_0x138a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13bb;
}

label_0x138c:
t_195 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))), t_195)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_195, (LOAD_LE_32(mem, PLUS_64(RSP, 204bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_195, 4bv32)), t_195)), 2bv32)), (XOR_32((RSHIFT_32(t_195, 4bv32)), t_195)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_195, 4bv32)), t_195)), 2bv32)), (XOR_32((RSHIFT_32(t_195, 4bv32)), t_195)))))[1:0]));
SF := t_195[32:31];
ZF := bool2bv(0bv32 == t_195);

label_0x1394:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13bb;
}

label_0x1396:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 4294967295bv32);

label_0x13a1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 1bv32);

label_0x13ac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), 0bv32);

label_0x13b7:
goto label_0x13dc;

label_0x13b9:
goto label_0x13dc;

label_0x13bb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 176bv64), 4294967295bv32);

label_0x13c6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 180bv64), 4294967295bv32);

label_0x13d1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4294967295bv32 ++ 2223702224bv32), 53284bv32);

label_0x13dc:
t1_199 := LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64));
t2_200 := RCX[32:0][8:0];
mem := STORE_LE_8(mem, PLUS_64(RCX, 13902980bv64), PLUS_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), t2_200));
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), t1_199));
OF := AND_1((bool2bv((t1_199[8:7]) == (t2_200[8:7]))), (XOR_1((t1_199[8:7]), (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), t1_199)), t2_200)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))))))))[1:0]));
SF := LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, PLUS_64(RCX, 13902980bv64))));

label_0x13e2:
t1_205 := LOAD_LE_8(mem, RAX);
t2_206 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_206));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_205));
OF := AND_1((bool2bv((t1_205[8:7]) == (t2_206[8:7]))), (XOR_1((t1_205[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_205)), t2_206)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x13e4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x13eb:
t_211 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_211[32:31]) == (1bv32[32:31]))), (XOR_1((t_211[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_211)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x13ed:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x13f0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 216bv64), RAX[32:0]);

label_0x13f7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 224bv64), 0bv32);

label_0x1402:
goto label_0x1414;

label_0x1404:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 224bv64)));

label_0x140b:
t_217 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_217[32:31]) == (1bv32[32:31]))), (XOR_1((t_217[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_217)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x140d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 224bv64), RAX[32:0]);

label_0x1414:
t_221 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))), t_221)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_221, (LOAD_LE_32(mem, PLUS_64(RSP, 224bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))))[1:0]));
SF := t_221[32:31];
ZF := bool2bv(0bv32 == t_221);

label_0x141c:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x184b;
}

label_0x1422:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64)))));

label_0x142a:
t_225 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_225[64:0];
OF := bool2bv(t_225 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_225 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_60;
SF := unconstrained_61;
ZF := unconstrained_62;
AF := unconstrained_63;

label_0x142e:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1433:
t1_227 := RCX;
t2_228 := RAX;
RCX := PLUS_64(RCX, t2_228);
CF := bool2bv(LT_64(RCX, t1_227));
OF := AND_1((bool2bv((t1_227[64:63]) == (t2_228[64:63]))), (XOR_1((t1_227[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_227)), t2_228)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1436:
RAX := RCX;

label_0x1439:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x143c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x1443:
t1_233 := RCX[32:0];
t2_234 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_234));
CF := bool2bv(LT_32((RCX[32:0]), t1_233));
OF := AND_1((bool2bv((t1_233[32:31]) == (t2_234[32:31]))), (XOR_1((t1_233[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_233)), t2_234)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1445:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1447:
mem := STORE_LE_32(mem, PLUS_64(RSP, 168bv64), RAX[32:0]);

label_0x144e:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64)))));

label_0x1456:
t_239 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_239[64:0];
OF := bool2bv(t_239 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_239 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_64;
SF := unconstrained_65;
ZF := unconstrained_66;
AF := unconstrained_67;

label_0x145a:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x145f:
t1_241 := RCX;
t2_242 := RAX;
RCX := PLUS_64(RCX, t2_242);
CF := bool2bv(LT_64(RCX, t1_241));
OF := AND_1((bool2bv((t1_241[64:63]) == (t2_242[64:63]))), (XOR_1((t1_241[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_241)), t2_242)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1462:
RAX := RCX;

label_0x1465:
t1_247 := RAX;
t2_248 := 2bv64;
RAX := PLUS_64(RAX, t2_248);
CF := bool2bv(LT_64(RAX, t1_247));
OF := AND_1((bool2bv((t1_247[64:63]) == (t2_248[64:63]))), (XOR_1((t1_247[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_247)), t2_248)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1469:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x146c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 164bv64)));

label_0x1473:
t1_253 := RCX[32:0];
t2_254 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_254));
CF := bool2bv(LT_32((RCX[32:0]), t1_253));
OF := AND_1((bool2bv((t1_253[32:31]) == (t2_254[32:31]))), (XOR_1((t1_253[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_253)), t2_254)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1475:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1477:
mem := STORE_LE_32(mem, PLUS_64(RSP, 172bv64), RAX[32:0]);

label_0x147e:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 172bv64)));

label_0x1486:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x148d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x1495:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5274bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x149a"} true;
call arbitrary_func();

label_0x149a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), RAX[32:0]);

label_0x14a1:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));

label_0x14a9:
t_259 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_259[64:0];
OF := bool2bv(t_259 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_259 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_68;
SF := unconstrained_69;
ZF := unconstrained_70;
AF := unconstrained_71;

label_0x14ad:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x14b5:
t1_261 := RCX;
t2_262 := RAX;
RCX := PLUS_64(RCX, t2_262);
CF := bool2bv(LT_64(RCX, t1_261));
OF := AND_1((bool2bv((t1_261[64:63]) == (t2_262[64:63]))), (XOR_1((t1_261[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_261)), t2_262)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x14b8:
RAX := RCX;

label_0x14bb:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x14be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x14c6:
t1_267 := RCX;
t2_268 := 170bv64;
RCX := PLUS_64(RCX, t2_268);
CF := bool2bv(LT_64(RCX, t1_267));
OF := AND_1((bool2bv((t1_267[64:63]) == (t2_268[64:63]))), (XOR_1((t1_267[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_267)), t2_268)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x14cd:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x14d0:
t_273 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_273)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_273, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)), 2bv32)), (XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)), 2bv32)), (XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)))))[1:0]));
SF := t_273[32:31];
ZF := bool2bv(0bv32 == t_273);

label_0x14d2:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1618;
}

label_0x14d8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));

label_0x14e0:
t_277 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_277[64:0];
OF := bool2bv(t_277 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_277 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_72;
SF := unconstrained_73;
ZF := unconstrained_74;
AF := unconstrained_75;

label_0x14e4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x14ec:
t1_279 := RCX;
t2_280 := RAX;
RCX := PLUS_64(RCX, t2_280);
CF := bool2bv(LT_64(RCX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x14ef:
RAX := RCX;

label_0x14f2:
t1_285 := RAX;
t2_286 := 2bv64;
RAX := PLUS_64(RAX, t2_286);
CF := bool2bv(LT_64(RAX, t1_285));
OF := AND_1((bool2bv((t1_285[64:63]) == (t2_286[64:63]))), (XOR_1((t1_285[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_285)), t2_286)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14f6:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x14f9:
t_291 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))))), (XOR_32((RAX[32:0]), t_291)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_291, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)), 2bv32)), (XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)), 2bv32)), (XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)))))[1:0]));
SF := t_291[32:31];
ZF := bool2bv(0bv32 == t_291);

label_0x1500:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1618;
}

label_0x1506:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));

label_0x150e:
t_295 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_295[64:0];
OF := bool2bv(t_295 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_295 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_76;
SF := unconstrained_77;
ZF := unconstrained_78;
AF := unconstrained_79;

label_0x1512:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x151a:
RCX := LOAD_LE_64(mem, RCX);

label_0x151d:
t1_297 := RCX;
t2_298 := RAX;
RCX := PLUS_64(RCX, t2_298);
CF := bool2bv(LT_64(RCX, t1_297));
OF := AND_1((bool2bv((t1_297[64:63]) == (t2_298[64:63]))), (XOR_1((t1_297[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_297)), t2_298)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1520:
RAX := RCX;

label_0x1523:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0x152b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1533:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_80;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1539:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x153e:
t_305 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))))[1:0]));
SF := t_305[64:63];
ZF := bool2bv(0bv64 == t_305);

label_0x1541:
if (bv2bool(ZF)) {
  goto label_0x1544;
}

label_0x1543:
assume false;

label_0x1544:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x154c:
origDEST_309 := RAX;
origCOUNT_310 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), CF, LSHIFT_64(origDEST_309, (MINUS_64(64bv64, origCOUNT_310)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv64)), origDEST_309[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), AF, unconstrained_83);

label_0x1550:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 5463bv64)), 0bv64));

label_0x1557:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x155b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1563:
origDEST_315 := RCX;
origCOUNT_316 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_85);

label_0x1567:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_86;
SF := unconstrained_87;
AF := unconstrained_88;
PF := unconstrained_89;

label_0x156b:
if (bv2bool(CF)) {
  goto label_0x156e;
}

label_0x156d:
assume false;

label_0x156e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1576:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 168bv64))));

label_0x157e:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1581:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));

label_0x1589:
t_321 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_321[64:0];
OF := bool2bv(t_321 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_321 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_90;
SF := unconstrained_91;
ZF := unconstrained_92;
AF := unconstrained_93;

label_0x158d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x1595:
RCX := LOAD_LE_64(mem, RCX);

label_0x1598:
t1_323 := RCX;
t2_324 := RAX;
RCX := PLUS_64(RCX, t2_324);
CF := bool2bv(LT_64(RCX, t1_323));
OF := AND_1((bool2bv((t1_323[64:63]) == (t2_324[64:63]))), (XOR_1((t1_323[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_323)), t2_324)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x159b:
RAX := RCX;

label_0x159e:
t1_329 := RAX;
t2_330 := 2bv64;
RAX := PLUS_64(RAX, t2_330);
CF := bool2bv(LT_64(RAX, t1_329));
OF := AND_1((bool2bv((t1_329[64:63]) == (t2_330[64:63]))), (XOR_1((t1_329[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_329)), t2_330)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RAX);

label_0x15aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x15b2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15b8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15bd:
t_337 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)), 2bv64)), (XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)), 2bv64)), (XOR_64((RSHIFT_64(t_337, 4bv64)), t_337)))))[1:0]));
SF := t_337[64:63];
ZF := bool2bv(0bv64 == t_337);

label_0x15c0:
if (bv2bool(ZF)) {
  goto label_0x15c3;
}

label_0x15c2:
assume false;

label_0x15c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x15cb:
origDEST_341 := RAX;
origCOUNT_342 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), CF, LSHIFT_64(origDEST_341, (MINUS_64(64bv64, origCOUNT_342)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_342 == 1bv64)), origDEST_341[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), AF, unconstrained_97);

label_0x15cf:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 5590bv64)), 0bv64));

label_0x15d6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x15da:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x15e2:
origDEST_347 := RCX;
origCOUNT_348 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), CF, LSHIFT_64(origDEST_347, (MINUS_64(64bv64, origCOUNT_348)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_348 == 1bv64)), origDEST_347[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_348 == 0bv64)), AF, unconstrained_99);

label_0x15e6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_100;
SF := unconstrained_101;
AF := unconstrained_102;
PF := unconstrained_103;

label_0x15ea:
if (bv2bool(CF)) {
  goto label_0x15ed;
}

label_0x15ec:
assume false;

label_0x15ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x15f5:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 172bv64))));

label_0x15fd:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1600:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)));

label_0x1607:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x160e:
goto label_0x18d2;

label_0x1613:
goto label_0x18d2;

label_0x1618:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)))));

label_0x1620:
t_353 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_353[64:0];
OF := bool2bv(t_353 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_353 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_104;
SF := unconstrained_105;
ZF := unconstrained_106;
AF := unconstrained_107;

label_0x1624:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1629:
t1_355 := RCX;
t2_356 := RAX;
RCX := PLUS_64(RCX, t2_356);
CF := bool2bv(LT_64(RCX, t1_355));
OF := AND_1((bool2bv((t1_355[64:63]) == (t2_356[64:63]))), (XOR_1((t1_355[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_355)), t2_356)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x162c:
RAX := RCX;

label_0x162f:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x1632:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x1639:
t1_361 := RCX[32:0];
t2_362 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_362));
CF := bool2bv(LT_32((RCX[32:0]), t1_361));
OF := AND_1((bool2bv((t1_361[32:31]) == (t2_362[32:31]))), (XOR_1((t1_361[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_361)), t2_362)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x163b:
RAX := (0bv32 ++ RCX[32:0]);

label_0x163d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 168bv64), RAX[32:0]);

label_0x1644:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)))));

label_0x164c:
t_367 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_367[64:0];
OF := bool2bv(t_367 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_367 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_108;
SF := unconstrained_109;
ZF := unconstrained_110;
AF := unconstrained_111;

label_0x1650:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1655:
t1_369 := RCX;
t2_370 := RAX;
RCX := PLUS_64(RCX, t2_370);
CF := bool2bv(LT_64(RCX, t1_369));
OF := AND_1((bool2bv((t1_369[64:63]) == (t2_370[64:63]))), (XOR_1((t1_369[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_369)), t2_370)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1658:
RAX := RCX;

label_0x165b:
t1_375 := RAX;
t2_376 := 2bv64;
RAX := PLUS_64(RAX, t2_376);
CF := bool2bv(LT_64(RAX, t1_375));
OF := AND_1((bool2bv((t1_375[64:63]) == (t2_376[64:63]))), (XOR_1((t1_375[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_375)), t2_376)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x165f:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x1662:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 164bv64)));

label_0x1669:
t1_381 := RCX[32:0];
t2_382 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_382));
CF := bool2bv(LT_32((RCX[32:0]), t1_381));
OF := AND_1((bool2bv((t1_381[32:31]) == (t2_382[32:31]))), (XOR_1((t1_381[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_381)), t2_382)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x166b:
RAX := (0bv32 ++ RCX[32:0]);

label_0x166d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 172bv64), RAX[32:0]);

label_0x1674:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 172bv64)));

label_0x167c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x1683:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x168b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5776bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1690"} true;
call arbitrary_func();

label_0x1690:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), RAX[32:0]);

label_0x1697:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));

label_0x169f:
t_387 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_387[64:0];
OF := bool2bv(t_387 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_387 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_112;
SF := unconstrained_113;
ZF := unconstrained_114;
AF := unconstrained_115;

label_0x16a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x16ab:
t1_389 := RCX;
t2_390 := RAX;
RCX := PLUS_64(RCX, t2_390);
CF := bool2bv(LT_64(RCX, t1_389));
OF := AND_1((bool2bv((t1_389[64:63]) == (t2_390[64:63]))), (XOR_1((t1_389[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_389)), t2_390)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x16ae:
RAX := RCX;

label_0x16b1:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x16b4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x16bc:
t1_395 := RCX;
t2_396 := 170bv64;
RCX := PLUS_64(RCX, t2_396);
CF := bool2bv(LT_64(RCX, t1_395));
OF := AND_1((bool2bv((t1_395[64:63]) == (t2_396[64:63]))), (XOR_1((t1_395[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_395)), t2_396)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x16c3:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x16c6:
t_401 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_401)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_401, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_401, 4bv32)), t_401)), 2bv32)), (XOR_32((RSHIFT_32(t_401, 4bv32)), t_401)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_401, 4bv32)), t_401)), 2bv32)), (XOR_32((RSHIFT_32(t_401, 4bv32)), t_401)))))[1:0]));
SF := t_401[32:31];
ZF := bool2bv(0bv32 == t_401);

label_0x16c8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x180e;
}

label_0x16ce:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));

label_0x16d6:
t_405 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_405[64:0];
OF := bool2bv(t_405 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_405 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_116;
SF := unconstrained_117;
ZF := unconstrained_118;
AF := unconstrained_119;

label_0x16da:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x16e2:
t1_407 := RCX;
t2_408 := RAX;
RCX := PLUS_64(RCX, t2_408);
CF := bool2bv(LT_64(RCX, t1_407));
OF := AND_1((bool2bv((t1_407[64:63]) == (t2_408[64:63]))), (XOR_1((t1_407[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_407)), t2_408)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x16e5:
RAX := RCX;

label_0x16e8:
t1_413 := RAX;
t2_414 := 2bv64;
RAX := PLUS_64(RAX, t2_414);
CF := bool2bv(LT_64(RAX, t1_413));
OF := AND_1((bool2bv((t1_413[64:63]) == (t2_414[64:63]))), (XOR_1((t1_413[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_413)), t2_414)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16ec:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x16ef:
t_419 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))))), (XOR_32((RAX[32:0]), t_419)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_419, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)), 2bv32)), (XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)), 2bv32)), (XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)))))[1:0]));
SF := t_419[32:31];
ZF := bool2bv(0bv32 == t_419);

label_0x16f6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x180e;
}

label_0x16fc:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));

label_0x1704:
t_423 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_423[64:0];
OF := bool2bv(t_423 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_423 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_120;
SF := unconstrained_121;
ZF := unconstrained_122;
AF := unconstrained_123;

label_0x1708:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x1710:
RCX := LOAD_LE_64(mem, RCX);

label_0x1713:
t1_425 := RCX;
t2_426 := RAX;
RCX := PLUS_64(RCX, t2_426);
CF := bool2bv(LT_64(RCX, t1_425));
OF := AND_1((bool2bv((t1_425[64:63]) == (t2_426[64:63]))), (XOR_1((t1_425[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_425)), t2_426)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1716:
RAX := RCX;

label_0x1719:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0x1721:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x1729:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_124;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x172f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1734:
t_433 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_433, 4bv64)), t_433)), 2bv64)), (XOR_64((RSHIFT_64(t_433, 4bv64)), t_433)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_433, 4bv64)), t_433)), 2bv64)), (XOR_64((RSHIFT_64(t_433, 4bv64)), t_433)))))[1:0]));
SF := t_433[64:63];
ZF := bool2bv(0bv64 == t_433);

label_0x1737:
if (bv2bool(ZF)) {
  goto label_0x173a;
}

label_0x1739:
assume false;

label_0x173a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x1742:
origDEST_437 := RAX;
origCOUNT_438 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), CF, LSHIFT_64(origDEST_437, (MINUS_64(64bv64, origCOUNT_438)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_438 == 1bv64)), origDEST_437[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_438 == 0bv64)), AF, unconstrained_127);

label_0x1746:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 5965bv64)), 0bv64));

label_0x174d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1751:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x1759:
origDEST_443 := RCX;
origCOUNT_444 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), CF, LSHIFT_64(origDEST_443, (MINUS_64(64bv64, origCOUNT_444)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_444 == 1bv64)), origDEST_443[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_444 == 0bv64)), AF, unconstrained_129);

label_0x175d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_130;
SF := unconstrained_131;
AF := unconstrained_132;
PF := unconstrained_133;

label_0x1761:
if (bv2bool(CF)) {
  goto label_0x1764;
}

label_0x1763:
assume false;

label_0x1764:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x176c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 168bv64))));

label_0x1774:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1777:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)))));

label_0x177f:
t_449 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_449[64:0];
OF := bool2bv(t_449 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_449 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_134;
SF := unconstrained_135;
ZF := unconstrained_136;
AF := unconstrained_137;

label_0x1783:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x178b:
RCX := LOAD_LE_64(mem, RCX);

label_0x178e:
t1_451 := RCX;
t2_452 := RAX;
RCX := PLUS_64(RCX, t2_452);
CF := bool2bv(LT_64(RCX, t1_451));
OF := AND_1((bool2bv((t1_451[64:63]) == (t2_452[64:63]))), (XOR_1((t1_451[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_451)), t2_452)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1791:
RAX := RCX;

label_0x1794:
t1_457 := RAX;
t2_458 := 2bv64;
RAX := PLUS_64(RAX, t2_458);
CF := bool2bv(LT_64(RAX, t1_457));
OF := AND_1((bool2bv((t1_457[64:63]) == (t2_458[64:63]))), (XOR_1((t1_457[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_457)), t2_458)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1798:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0x17a0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x17a8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_138;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17ae:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17b3:
t_465 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_139;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)), 2bv64)), (XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)), 2bv64)), (XOR_64((RSHIFT_64(t_465, 4bv64)), t_465)))))[1:0]));
SF := t_465[64:63];
ZF := bool2bv(0bv64 == t_465);

label_0x17b6:
if (bv2bool(ZF)) {
  goto label_0x17b9;
}

label_0x17b8:
assume false;

label_0x17b9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x17c1:
origDEST_469 := RAX;
origCOUNT_470 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), CF, LSHIFT_64(origDEST_469, (MINUS_64(64bv64, origCOUNT_470)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_470 == 1bv64)), origDEST_469[64:63], unconstrained_140));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), AF, unconstrained_141);

label_0x17c5:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6092bv64)), 0bv64));

label_0x17cc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17d0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x17d8:
origDEST_475 := RCX;
origCOUNT_476 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), CF, LSHIFT_64(origDEST_475, (MINUS_64(64bv64, origCOUNT_476)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_476 == 1bv64)), origDEST_475[64:63], unconstrained_142));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), AF, unconstrained_143);

label_0x17dc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_144;
SF := unconstrained_145;
AF := unconstrained_146;
PF := unconstrained_147;

label_0x17e0:
if (bv2bool(CF)) {
  goto label_0x17e3;
}

label_0x17e2:
assume false;

label_0x17e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x17eb:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 172bv64))));

label_0x17f3:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x17f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)));

label_0x17fd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x1804:
goto label_0x18d2;

label_0x1809:
goto label_0x18d2;

label_0x180e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 212bv64)));

label_0x1815:
t_481 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_481, 1bv32)), (XOR_32(t_481, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_481)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1817:
mem := STORE_LE_32(mem, PLUS_64(RSP, 212bv64), RAX[32:0]);

label_0x181e:
t_485 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))), t_485)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_485, (LOAD_LE_32(mem, PLUS_64(RSP, 212bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)), 2bv32)), (XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)), 2bv32)), (XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)))))[1:0]));
SF := t_485[32:31];
ZF := bool2bv(0bv32 == t_485);

label_0x1826:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1833;
}

label_0x1828:
mem := STORE_LE_32(mem, PLUS_64(RSP, 212bv64), 7bv32);

label_0x1833:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)));

label_0x183a:
t_489 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_489[32:31]) == (1bv32[32:31]))), (XOR_1((t_489[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_489)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x183c:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_148;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x183f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 216bv64), RAX[32:0]);

label_0x1846:
goto label_0x1404;

label_0x184b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x1853:
RCX := LOAD_LE_64(mem, RAX);

label_0x1856:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6235bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x185b"} true;
call arbitrary_func();

label_0x185b:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6242bv64)), 0bv64));

label_0x1862:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0x186a:
RAX := PLUS_64(RSP, 112bv64)[64:0];

label_0x186f:
origDEST_495 := RAX;
origCOUNT_496 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), CF, LSHIFT_64(origDEST_495, (MINUS_64(64bv64, origCOUNT_496)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_496 == 1bv64)), origDEST_495[64:63], unconstrained_149));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), AF, unconstrained_150);

label_0x1873:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x187b:
t1_501 := RCX;
t2_502 := RAX;
RCX := PLUS_64(RCX, t2_502);
CF := bool2bv(LT_64(RCX, t1_501));
OF := AND_1((bool2bv((t1_501[64:63]) == (t2_502[64:63]))), (XOR_1((t1_501[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_501)), t2_502)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x187e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RCX);

label_0x1886:
RAX := PLUS_64(RSP, 112bv64)[64:0];

label_0x188b:
origDEST_507 := RAX;
origCOUNT_508 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), CF, LSHIFT_64(origDEST_507, (MINUS_64(64bv64, origCOUNT_508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_508 == 1bv64)), origDEST_507[64:63], unconstrained_151));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), AF, unconstrained_152);

label_0x188f:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_153;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1893:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x1895:
mem := STORE_LE_8(mem, PLUS_64(RSP, 320bv64), RCX[32:0][8:0]);

label_0x189c:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x189f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 320bv64))));

label_0x18a7:
origDEST_515 := RAX[32:0][8:0];
origCOUNT_516 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), CF, RSHIFT_8(origDEST_515, (MINUS_8(8bv8, origCOUNT_516)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_516 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_154));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv8)), AF, unconstrained_155);

label_0x18a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x18b1:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x18b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x18bb:
t_523 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_523, 2bv64));
OF := AND_64((XOR_64(t_523, 2bv64)), (XOR_64(t_523, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_523)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18bf:
RDI := RAX;

label_0x18c2:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_157;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x18c4:
RCX := (0bv32 ++ 2bv32);

label_0x18c9:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x18cb:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_158;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x18cd:
goto label_0x1b2e;

label_0x18d2:
goto label_0x1023;

label_0x18d7:
goto label_0x1023;

label_0x18dc:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 408bv64)));

label_0x18e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x18eb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6384bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x18f0"} true;
call arbitrary_func();

label_0x18f0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 324bv64), RAX[32:0]);

label_0x18f7:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 408bv64)));

label_0x18fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x1906:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6411bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x190b"} true;
call arbitrary_func();

label_0x190b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 324bv64)));

label_0x1912:
R8 := (0bv32 ++ (0bv16 ++ RCX[32:0][16:0]));

label_0x1916:
RDX := (0bv32 ++ (0bv16 ++ RAX[32:0][16:0]));

label_0x1919:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x191e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6435bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1923"} true;
call arbitrary_func();

label_0x1923:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1925:
mem := STORE_LE_32(mem, PLUS_64(RSP, 328bv64), RAX[32:0]);

label_0x192c:
RAX := (0bv32 ++ 4bv32);

label_0x1931:
t_527 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_527[64:0];
OF := bool2bv(t_527 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_527 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_159;
SF := unconstrained_160;
ZF := unconstrained_161;
AF := unconstrained_162;

label_0x1935:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x193d:
RCX := LOAD_LE_64(mem, RCX);

label_0x1940:
t1_529 := RCX;
t2_530 := RAX;
RCX := PLUS_64(RCX, t2_530);
CF := bool2bv(LT_64(RCX, t1_529));
OF := AND_1((bool2bv((t1_529[64:63]) == (t2_530[64:63]))), (XOR_1((t1_529[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_529)), t2_530)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1943:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RCX);

label_0x194b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x1953:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_163;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1959:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x195e:
t_537 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_164;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)), 2bv64)), (XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)), 2bv64)), (XOR_64((RSHIFT_64(t_537, 4bv64)), t_537)))))[1:0]));
SF := t_537[64:63];
ZF := bool2bv(0bv64 == t_537);

label_0x1961:
if (bv2bool(ZF)) {
  goto label_0x1964;
}

label_0x1963:
assume false;

label_0x1964:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x196c:
origDEST_541 := RAX;
origCOUNT_542 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), CF, LSHIFT_64(origDEST_541, (MINUS_64(64bv64, origCOUNT_542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_542 == 1bv64)), origDEST_541[64:63], unconstrained_165));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), AF, unconstrained_166);

label_0x1970:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6519bv64)), 0bv64));

label_0x1977:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x197b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x1983:
origDEST_547 := RCX;
origCOUNT_548 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), CF, LSHIFT_64(origDEST_547, (MINUS_64(64bv64, origCOUNT_548)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_548 == 1bv64)), origDEST_547[64:63], unconstrained_167));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_548 == 0bv64)), AF, unconstrained_168);

label_0x1987:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_169;
SF := unconstrained_170;
AF := unconstrained_171;
PF := unconstrained_172;

label_0x198b:
if (bv2bool(CF)) {
  goto label_0x198e;
}

label_0x198d:
assume false;

label_0x198e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x1996:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 328bv64)));

label_0x199d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x199f:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 416bv64)));

label_0x19a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x19ae:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6579bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x19b3"} true;
call arbitrary_func();

label_0x19b3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 344bv64), RAX[32:0]);

label_0x19ba:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 416bv64)));

label_0x19c1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x19c9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6606bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x19ce"} true;
call arbitrary_func();

label_0x19ce:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 344bv64)));

label_0x19d5:
R8 := (0bv32 ++ (0bv16 ++ RCX[32:0][16:0]));

label_0x19d9:
RDX := (0bv32 ++ (0bv16 ++ RAX[32:0][16:0]));

label_0x19dc:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x19e1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6630bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x19e6"} true;
call arbitrary_func();

label_0x19e6:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x19e8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 348bv64), RAX[32:0]);

label_0x19ef:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x19f6:
t_553 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_553, 1bv32)), (XOR_32(t_553, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_553)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x19f8:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x19fa:
t_557 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_557[64:0];
OF := bool2bv(t_557 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_557 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_173;
SF := unconstrained_174;
ZF := unconstrained_175;
AF := unconstrained_176;

label_0x19fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x1a06:
RCX := LOAD_LE_64(mem, RCX);

label_0x1a09:
t1_559 := RCX;
t2_560 := RAX;
RCX := PLUS_64(RCX, t2_560);
CF := bool2bv(LT_64(RCX, t1_559));
OF := AND_1((bool2bv((t1_559[64:63]) == (t2_560[64:63]))), (XOR_1((t1_559[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_559)), t2_560)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1a0c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RCX);

label_0x1a14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x1a1c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a22:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a27:
t_567 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_178;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)), 2bv64)), (XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)), 2bv64)), (XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)))))[1:0]));
SF := t_567[64:63];
ZF := bool2bv(0bv64 == t_567);

label_0x1a2a:
if (bv2bool(ZF)) {
  goto label_0x1a2d;
}

label_0x1a2c:
assume false;

label_0x1a2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x1a35:
origDEST_571 := RAX;
origCOUNT_572 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), CF, LSHIFT_64(origDEST_571, (MINUS_64(64bv64, origCOUNT_572)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_572 == 1bv64)), origDEST_571[64:63], unconstrained_179));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), AF, unconstrained_180);

label_0x1a39:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6720bv64)), 0bv64));

label_0x1a40:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a44:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x1a4c:
origDEST_577 := RCX;
origCOUNT_578 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), CF, LSHIFT_64(origDEST_577, (MINUS_64(64bv64, origCOUNT_578)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_578 == 1bv64)), origDEST_577[64:63], unconstrained_181));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_578 == 0bv64)), AF, unconstrained_182);

label_0x1a50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_183;
SF := unconstrained_184;
AF := unconstrained_185;
PF := unconstrained_186;

label_0x1a54:
if (bv2bool(CF)) {
  goto label_0x1a57;
}

label_0x1a56:
assume false;

label_0x1a57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x1a5f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 348bv64)));

label_0x1a66:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1a68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1a70:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a76:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a7b:
t_585 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_188;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))))[1:0]));
SF := t_585[64:63];
ZF := bool2bv(0bv64 == t_585);

label_0x1a7e:
if (bv2bool(ZF)) {
  goto label_0x1a81;
}

label_0x1a80:
assume false;

label_0x1a81:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1a89:
origDEST_589 := RAX;
origCOUNT_590 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, LSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), origDEST_589[64:63], unconstrained_189));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_190);

label_0x1a8d:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6804bv64)), 0bv64));

label_0x1a94:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a98:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1aa0:
origDEST_595 := RCX;
origCOUNT_596 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), CF, LSHIFT_64(origDEST_595, (MINUS_64(64bv64, origCOUNT_596)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_596 == 1bv64)), origDEST_595[64:63], unconstrained_191));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), AF, unconstrained_192);

label_0x1aa4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_193;
SF := unconstrained_194;
AF := unconstrained_195;
PF := unconstrained_196;

label_0x1aa8:
if (bv2bool(CF)) {
  goto label_0x1aab;
}

label_0x1aaa:
assume false;

label_0x1aab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1ab3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x1aba:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1abc:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 6851bv64)), 0bv64));

label_0x1ac3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0x1acb:
RAX := PLUS_64(RSP, 112bv64)[64:0];

label_0x1ad0:
origDEST_601 := RAX;
origCOUNT_602 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), CF, LSHIFT_64(origDEST_601, (MINUS_64(64bv64, origCOUNT_602)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_602 == 1bv64)), origDEST_601[64:63], unconstrained_197));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), AF, unconstrained_198);

label_0x1ad4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x1adc:
t1_607 := RCX;
t2_608 := RAX;
RCX := PLUS_64(RCX, t2_608);
CF := bool2bv(LT_64(RCX, t1_607));
OF := AND_1((bool2bv((t1_607[64:63]) == (t2_608[64:63]))), (XOR_1((t1_607[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_607)), t2_608)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1adf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RCX);

label_0x1ae7:
RAX := PLUS_64(RSP, 112bv64)[64:0];

label_0x1aec:
origDEST_613 := RAX;
origCOUNT_614 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), CF, LSHIFT_64(origDEST_613, (MINUS_64(64bv64, origCOUNT_614)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_614 == 1bv64)), origDEST_613[64:63], unconstrained_199));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), AF, unconstrained_200);

label_0x1af0:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_201;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1af4:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x1af6:
mem := STORE_LE_8(mem, PLUS_64(RSP, 376bv64), RCX[32:0][8:0]);

label_0x1afd:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1b00:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 376bv64))));

label_0x1b08:
origDEST_621 := RAX[32:0][8:0];
origCOUNT_622 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), CF, RSHIFT_8(origDEST_621, (MINUS_8(8bv8, origCOUNT_622)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_622 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_202));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv8)), AF, unconstrained_203);

label_0x1b0a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x1b12:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_204;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x1b14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x1b1c:
t_629 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_629, 2bv64));
OF := AND_64((XOR_64(t_629, 2bv64)), (XOR_64(t_629, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_629)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b20:
RDI := RAX;

label_0x1b23:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_205;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1b25:
RCX := (0bv32 ++ 2bv32);

label_0x1b2a:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x1b2c:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x1b2e:
t1_633 := RSP;
t2_634 := 384bv64;
RSP := PLUS_64(RSP, t2_634);
CF := bool2bv(LT_64(RSP, t1_633));
OF := AND_1((bool2bv((t1_633[64:63]) == (t2_634[64:63]))), (XOR_1((t1_633[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_633)), t2_634)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1b35:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x1b36:

ra_639 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_14,origCOUNT_22,origCOUNT_310,origCOUNT_316,origCOUNT_342,origCOUNT_348,origCOUNT_438,origCOUNT_44,origCOUNT_444,origCOUNT_470,origCOUNT_476,origCOUNT_496,origCOUNT_50,origCOUNT_508,origCOUNT_516,origCOUNT_542,origCOUNT_548,origCOUNT_572,origCOUNT_578,origCOUNT_590,origCOUNT_596,origCOUNT_602,origCOUNT_614,origCOUNT_622,origCOUNT_8,origDEST_13,origDEST_21,origDEST_309,origDEST_315,origDEST_341,origDEST_347,origDEST_43,origDEST_437,origDEST_443,origDEST_469,origDEST_475,origDEST_49,origDEST_495,origDEST_507,origDEST_515,origDEST_541,origDEST_547,origDEST_571,origDEST_577,origDEST_589,origDEST_595,origDEST_601,origDEST_613,origDEST_621,origDEST_7,ra_639,t1_199,t1_205,t1_227,t1_233,t1_241,t1_247,t1_253,t1_261,t1_267,t1_279,t1_285,t1_29,t1_297,t1_323,t1_329,t1_355,t1_361,t1_369,t1_375,t1_381,t1_389,t1_395,t1_407,t1_413,t1_425,t1_451,t1_457,t1_501,t1_529,t1_55,t1_559,t1_607,t1_61,t1_633,t2_200,t2_206,t2_228,t2_234,t2_242,t2_248,t2_254,t2_262,t2_268,t2_280,t2_286,t2_298,t2_30,t2_324,t2_330,t2_356,t2_362,t2_370,t2_376,t2_382,t2_390,t2_396,t2_408,t2_414,t2_426,t2_452,t2_458,t2_502,t2_530,t2_56,t2_560,t2_608,t2_62,t2_634,t_1,t_103,t_105,t_107,t_111,t_113,t_115,t_119,t_121,t_123,t_127,t_129,t_131,t_135,t_139,t_143,t_147,t_151,t_155,t_159,t_163,t_167,t_171,t_175,t_179,t_183,t_187,t_191,t_195,t_211,t_217,t_221,t_225,t_239,t_259,t_273,t_277,t_291,t_295,t_3,t_305,t_321,t_337,t_35,t_353,t_367,t_387,t_39,t_401,t_405,t_419,t_423,t_433,t_449,t_465,t_481,t_485,t_489,t_523,t_527,t_537,t_553,t_557,t_567,t_585,t_629,t_67,t_71,t_75,t_79,t_83,t_87,t_91,t_95,t_99;

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
var origCOUNT_14: bv64;
var origCOUNT_22: bv64;
var origCOUNT_310: bv64;
var origCOUNT_316: bv64;
var origCOUNT_342: bv64;
var origCOUNT_348: bv64;
var origCOUNT_438: bv64;
var origCOUNT_44: bv64;
var origCOUNT_444: bv64;
var origCOUNT_470: bv64;
var origCOUNT_476: bv64;
var origCOUNT_496: bv64;
var origCOUNT_50: bv64;
var origCOUNT_508: bv64;
var origCOUNT_516: bv8;
var origCOUNT_542: bv64;
var origCOUNT_548: bv64;
var origCOUNT_572: bv64;
var origCOUNT_578: bv64;
var origCOUNT_590: bv64;
var origCOUNT_596: bv64;
var origCOUNT_602: bv64;
var origCOUNT_614: bv64;
var origCOUNT_622: bv8;
var origCOUNT_8: bv64;
var origDEST_13: bv64;
var origDEST_21: bv64;
var origDEST_309: bv64;
var origDEST_315: bv64;
var origDEST_341: bv64;
var origDEST_347: bv64;
var origDEST_43: bv64;
var origDEST_437: bv64;
var origDEST_443: bv64;
var origDEST_469: bv64;
var origDEST_475: bv64;
var origDEST_49: bv64;
var origDEST_495: bv64;
var origDEST_507: bv64;
var origDEST_515: bv8;
var origDEST_541: bv64;
var origDEST_547: bv64;
var origDEST_571: bv64;
var origDEST_577: bv64;
var origDEST_589: bv64;
var origDEST_595: bv64;
var origDEST_601: bv64;
var origDEST_613: bv64;
var origDEST_621: bv8;
var origDEST_7: bv64;
var ra_639: bv64;
var t1_199: bv8;
var t1_205: bv8;
var t1_227: bv64;
var t1_233: bv32;
var t1_241: bv64;
var t1_247: bv64;
var t1_253: bv32;
var t1_261: bv64;
var t1_267: bv64;
var t1_279: bv64;
var t1_285: bv64;
var t1_29: bv64;
var t1_297: bv64;
var t1_323: bv64;
var t1_329: bv64;
var t1_355: bv64;
var t1_361: bv32;
var t1_369: bv64;
var t1_375: bv64;
var t1_381: bv32;
var t1_389: bv64;
var t1_395: bv64;
var t1_407: bv64;
var t1_413: bv64;
var t1_425: bv64;
var t1_451: bv64;
var t1_457: bv64;
var t1_501: bv64;
var t1_529: bv64;
var t1_55: bv64;
var t1_559: bv64;
var t1_607: bv64;
var t1_61: bv64;
var t1_633: bv64;
var t2_200: bv8;
var t2_206: bv8;
var t2_228: bv64;
var t2_234: bv32;
var t2_242: bv64;
var t2_248: bv64;
var t2_254: bv32;
var t2_262: bv64;
var t2_268: bv64;
var t2_280: bv64;
var t2_286: bv64;
var t2_298: bv64;
var t2_30: bv64;
var t2_324: bv64;
var t2_330: bv64;
var t2_356: bv64;
var t2_362: bv32;
var t2_370: bv64;
var t2_376: bv64;
var t2_382: bv32;
var t2_390: bv64;
var t2_396: bv64;
var t2_408: bv64;
var t2_414: bv64;
var t2_426: bv64;
var t2_452: bv64;
var t2_458: bv64;
var t2_502: bv64;
var t2_530: bv64;
var t2_56: bv64;
var t2_560: bv64;
var t2_608: bv64;
var t2_62: bv64;
var t2_634: bv64;
var t_1: bv64;
var t_103: bv64;
var t_105: bv64;
var t_107: bv32;
var t_111: bv64;
var t_113: bv64;
var t_115: bv32;
var t_119: bv64;
var t_121: bv64;
var t_123: bv32;
var t_127: bv64;
var t_129: bv64;
var t_131: bv32;
var t_135: bv32;
var t_139: bv32;
var t_143: bv32;
var t_147: bv32;
var t_151: bv32;
var t_155: bv32;
var t_159: bv32;
var t_163: bv32;
var t_167: bv32;
var t_171: bv32;
var t_175: bv32;
var t_179: bv32;
var t_183: bv32;
var t_187: bv32;
var t_191: bv32;
var t_195: bv32;
var t_211: bv32;
var t_217: bv32;
var t_221: bv32;
var t_225: bv128;
var t_239: bv128;
var t_259: bv128;
var t_273: bv32;
var t_277: bv128;
var t_291: bv32;
var t_295: bv128;
var t_3: bv64;
var t_305: bv64;
var t_321: bv128;
var t_337: bv64;
var t_35: bv128;
var t_353: bv128;
var t_367: bv128;
var t_387: bv128;
var t_39: bv64;
var t_401: bv32;
var t_405: bv128;
var t_419: bv32;
var t_423: bv128;
var t_433: bv64;
var t_449: bv128;
var t_465: bv64;
var t_481: bv32;
var t_485: bv32;
var t_489: bv32;
var t_523: bv64;
var t_527: bv128;
var t_537: bv64;
var t_553: bv32;
var t_557: bv128;
var t_567: bv64;
var t_585: bv64;
var t_629: bv64;
var t_67: bv32;
var t_71: bv32;
var t_75: bv32;
var t_79: bv32;
var t_83: bv32;
var t_87: bv32;
var t_91: bv32;
var t_95: bv32;
var t_99: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3584bv64);
axiom policy(6992bv64);
axiom policy(12288bv64);
axiom policy(12464bv64);
axiom policy(13536bv64);
axiom policy(18656bv64);
