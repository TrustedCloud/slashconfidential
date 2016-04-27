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
axiom _function_addr_low == 3744bv64;
axiom _function_addr_high == 6080bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xea0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0xea5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0xeaa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xeaf:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0xeb0:
t_3 := RSP;
RSP := MINUS_64(RSP, 288bv64);
CF := bool2bv(LT_64(t_3, 288bv64));
OF := AND_64((XOR_64(t_3, 288bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 288bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xeb7:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0xebc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0xec4:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xecb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0xed3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xedb:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0xedf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0xee7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xeef:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0xef3:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xef7:
RCX := (0bv32 ++ 53bv32);

label_0xefc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RCX);

label_0xf04:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xf07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xf0f:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0xf12:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xf1a:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xf22:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0xf26:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), 0bv32);

label_0xf31:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), 0bv32);

label_0xf3c:
mem := STORE_LE_8(mem, PLUS_64(RSP, 152bv64), 0bv8);

label_0xf44:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xf4c:
t1_29 := RAX;
t2_30 := 4424bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf52:
RDX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xf54:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xf59:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3934bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf5e"} true;
call arbitrary_func();

label_0xf5e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xf66:
t1_35 := RAX;
t2_36 := 4392bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf6c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xf74:
t1_41 := RCX;
t2_42 := 4388bv64;
RCX := PLUS_64(RCX, t2_42);
CF := bool2bv(LT_64(RCX, t1_41));
OF := AND_1((bool2bv((t1_41[64:63]) == (t2_42[64:63]))), (XOR_1((t1_41[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_41)), t2_42)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xf7b:
R8 := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xf7e:
RDX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xf80:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xf85:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3978bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf8a"} true;
call arbitrary_func();

label_0xf8a:
RDX := RAX;

label_0xf8d:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xf92:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3991bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf97"} true;
call arbitrary_func();

label_0xf97:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xf9f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfa5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xfaa:
t_49 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_49, 4bv64)), t_49)), 2bv64)), (XOR_64((RSHIFT_64(t_49, 4bv64)), t_49)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_49, 4bv64)), t_49)), 2bv64)), (XOR_64((RSHIFT_64(t_49, 4bv64)), t_49)))))[1:0]));
SF := t_49[64:63];
ZF := bool2bv(0bv64 == t_49);

label_0xfad:
if (bv2bool(ZF)) {
  goto label_0xfb0;
}

label_0xfaf:
assume false;

label_0xfb0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xfb8:
origDEST_53 := RAX;
origCOUNT_54 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_12);

label_0xfbc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xfc3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xfc7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xfcf:
origDEST_59 := RCX;
origCOUNT_60 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_14);

label_0xfd3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_15;
SF := unconstrained_16;
AF := unconstrained_17;
PF := unconstrained_18;

label_0xfd7:
if (bv2bool(CF)) {
  goto label_0xfda;
}

label_0xfd9:
assume false;

label_0xfda:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xfe2:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0xfe8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 164bv64), 0bv32);

label_0xff3:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 152bv64))));

label_0xffb:
t_65 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))))[1:0]));
SF := t_65[32:31];
ZF := bool2bv(0bv32 == t_65);

label_0xffd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14be;
}

label_0x1003:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x100b:
t1_69 := RAX;
t2_70 := 4424bv64;
RAX := PLUS_64(RAX, t2_70);
CF := bool2bv(LT_64(RAX, t1_69));
OF := AND_1((bool2bv((t1_69[64:63]) == (t2_70[64:63]))), (XOR_1((t1_69[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_69)), t2_70)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1011:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1019:
t1_75 := RCX;
t2_76 := 4428bv64;
RCX := PLUS_64(RCX, t2_76);
CF := bool2bv(LT_64(RCX, t1_75));
OF := AND_1((bool2bv((t1_75[64:63]) == (t2_76[64:63]))), (XOR_1((t1_75[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_75)), t2_76)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1020:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1022:
t_81 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RAX := (0bv32 ++ t_81[32:0]);
OF := bool2bv(t_81 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_81 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_20;
SF := unconstrained_21;
ZF := unconstrained_22;
AF := unconstrained_23;

label_0x1025:
t_83 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 164bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 164bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 164bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 164bv64))), t_83)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_83, (LOAD_LE_32(mem, PLUS_64(RSP, 164bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))))[1:0]));
SF := t_83[32:31];
ZF := bool2bv(0bv32 == t_83);

label_0x102c:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x14be;
}

label_0x1032:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x103a:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x103c:
t_87 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_87, 1bv32)), (XOR_32(t_87, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_87)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x103e:
RDX := (0bv32 ++ RAX[32:0]);

label_0x1040:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1045:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4170bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x104a"} true;
call arbitrary_func();

label_0x104a:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x104c:
t_91 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_91, 1bv32)), (XOR_32(t_91, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_91)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x104e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), RAX[32:0]);

label_0x1052:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x105a:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x105c:
t_95 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_95, 1bv32)), (XOR_32(t_95, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_95)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x105e:
RDX := (0bv32 ++ RAX[32:0]);

label_0x1060:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1065:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4202bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x106a"} true;
call arbitrary_func();

label_0x106a:
t1_99 := RAX;
t2_100 := 4bv64;
RAX := PLUS_64(RAX, t2_100);
CF := bool2bv(LT_64(RAX, t1_99));
OF := AND_1((bool2bv((t1_99[64:63]) == (t2_100[64:63]))), (XOR_1((t1_99[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_99)), t2_100)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x106e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1070:
t_105 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_105, 1bv32)), (XOR_32(t_105, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_105)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1072:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), RAX[32:0]);

label_0x1076:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x107e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1080:
t_109 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_109, 1bv32)), (XOR_32(t_109, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_109)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1082:
RDX := (0bv32 ++ RAX[32:0]);

label_0x1084:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1089:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4238bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x108e"} true;
call arbitrary_func();

label_0x108e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1090:
t_113 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_113[32:31]) == (1bv32[32:31]))), (XOR_1((t_113[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_113)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1092:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x1096:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x109e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x10a0:
t_117 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_117, 1bv32)), (XOR_32(t_117, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_117)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x10a2:
RDX := (0bv32 ++ RAX[32:0]);

label_0x10a4:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x10a9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4270bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x10ae"} true;
call arbitrary_func();

label_0x10ae:
t1_121 := RAX;
t2_122 := 4bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x10b2:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x10b4:
t_127 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_127[32:31]) == (1bv32[32:31]))), (XOR_1((t_127[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_127)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x10b6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x10ba:
t_131 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))), t_131)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_131, (LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))))[1:0]));
SF := t_131[32:31];
ZF := bool2bv(0bv32 == t_131);

label_0x10bf:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x10c9;
}

label_0x10c1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), 0bv32);

label_0x10c9:
t_135 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))), t_135)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_135, (LOAD_LE_32(mem, PLUS_64(RSP, 116bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))))[1:0]));
SF := t_135[32:31];
ZF := bool2bv(0bv32 == t_135);

label_0x10ce:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x10d8;
}

label_0x10d0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), 0bv32);

label_0x10d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x10e0:
t1_139 := RAX;
t2_140 := 4408bv64;
RAX := PLUS_64(RAX, t2_140);
CF := bool2bv(LT_64(RAX, t1_139));
OF := AND_1((bool2bv((t1_139[64:63]) == (t2_140[64:63]))), (XOR_1((t1_139[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_139)), t2_140)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x10e6:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x10e8:
t_145 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), t_145)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_145, (LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0x10ec:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1102;
}

label_0x10ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x10f6:
t1_149 := RAX;
t2_150 := 4408bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x10fc:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x10fe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x1102:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x110a:
t1_155 := RAX;
t2_156 := 4412bv64;
RAX := PLUS_64(RAX, t2_156);
CF := bool2bv(LT_64(RAX, t1_155));
OF := AND_1((bool2bv((t1_155[64:63]) == (t2_156[64:63]))), (XOR_1((t1_155[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_155)), t2_156)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1110:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1112:
t_161 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 124bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 124bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 124bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 124bv64))), t_161)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_161, (LOAD_LE_32(mem, PLUS_64(RSP, 124bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)), 2bv32)), (XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)), 2bv32)), (XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)))))[1:0]));
SF := t_161[32:31];
ZF := bool2bv(0bv32 == t_161);

label_0x1116:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x112c;
}

label_0x1118:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1120:
t1_165 := RAX;
t2_166 := 4412bv64;
RAX := PLUS_64(RAX, t2_166);
CF := bool2bv(LT_64(RAX, t1_165));
OF := AND_1((bool2bv((t1_165[64:63]) == (t2_166[64:63]))), (XOR_1((t1_165[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_165)), t2_166)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1126:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1128:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x112c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), 100000000bv32);

label_0x1137:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0x113b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 140bv64), RAX[32:0]);

label_0x1142:
goto label_0x1154;

label_0x1144:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x114b:
t_171 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_171[32:31]) == (1bv32[32:31]))), (XOR_1((t_171[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_171)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x114d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 140bv64), RAX[32:0]);

label_0x1154:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 124bv64)));

label_0x1158:
t_175 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))), t_175)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_175, (LOAD_LE_32(mem, PLUS_64(RSP, 140bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)), 2bv32)), (XOR_32((RSHIFT_32(t_175, 4bv32)), t_175)))))[1:0]));
SF := t_175[32:31];
ZF := bool2bv(0bv32 == t_175);

label_0x115f:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x13e2;
}

label_0x1165:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x1169:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0x1170:
goto label_0x1182;

label_0x1172:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x1179:
t_179 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_179[32:31]) == (1bv32[32:31]))), (XOR_1((t_179[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_179)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x117b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0x1182:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x1186:
t_183 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))), t_183)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_183, (LOAD_LE_32(mem, PLUS_64(RSP, 136bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)), 2bv32)), (XOR_32((RSHIFT_32(t_183, 4bv32)), t_183)))))[1:0]));
SF := t_183[32:31];
ZF := bool2bv(0bv32 == t_183);

label_0x118d:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x13dd;
}

label_0x1193:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x119b:
t1_187 := RAX;
t2_188 := 8bv64;
RAX := PLUS_64(RAX, t2_188);
CF := bool2bv(LT_64(RAX, t1_187));
OF := AND_1((bool2bv((t1_187[64:63]) == (t2_188[64:63]))), (XOR_1((t1_187[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_187)), t2_188)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x119f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x11a7:
t1_193 := RCX;
t2_194 := 4424bv64;
RCX := PLUS_64(RCX, t2_194);
CF := bool2bv(LT_64(RCX, t1_193));
OF := AND_1((bool2bv((t1_193[64:63]) == (t2_194[64:63]))), (XOR_1((t1_193[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_193)), t2_194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x11ae:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x11b5:
t_199 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_199[32:0]);
OF := bool2bv(t_199 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_199 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_24;
SF := unconstrained_25;
ZF := unconstrained_26;
AF := unconstrained_27;

label_0x11b8:
RCX := (0bv32 ++ RDX[32:0]);

label_0x11ba:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x11c1:
t1_201 := RDX[32:0];
t2_202 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_202));
CF := bool2bv(LT_32((RDX[32:0]), t1_201));
OF := AND_1((bool2bv((t1_201[32:31]) == (t2_202[32:31]))), (XOR_1((t1_201[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_201)), t2_202)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x11c3:
RCX := (0bv32 ++ RDX[32:0]);

label_0x11c5:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x11c8:
t_207 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_207[64:0];
OF := bool2bv(t_207 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_207 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_28;
SF := unconstrained_29;
ZF := unconstrained_30;
AF := unconstrained_31;

label_0x11cc:
RAX := LOAD_LE_64(mem, RAX);

label_0x11cf:
t1_209 := RAX;
t2_210 := RCX;
RAX := PLUS_64(RAX, t2_210);
CF := bool2bv(LT_64(RAX, t1_209));
OF := AND_1((bool2bv((t1_209[64:63]) == (t2_210[64:63]))), (XOR_1((t1_209[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_209)), t2_210)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11d2:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x11d5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x11dd:
t1_215 := RCX;
t2_216 := 16bv64;
RCX := PLUS_64(RCX, t2_216);
CF := bool2bv(LT_64(RCX, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x11e1:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x11e4:
t_221 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_221)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_221, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))))[1:0]));
SF := t_221[32:31];
ZF := bool2bv(0bv32 == t_221);

label_0x11e6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13d8;
}

label_0x11ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x11f4:
t1_225 := RAX;
t2_226 := 8bv64;
RAX := PLUS_64(RAX, t2_226);
CF := bool2bv(LT_64(RAX, t1_225));
OF := AND_1((bool2bv((t1_225[64:63]) == (t2_226[64:63]))), (XOR_1((t1_225[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_225)), t2_226)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11f8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1200:
t1_231 := RCX;
t2_232 := 4424bv64;
RCX := PLUS_64(RCX, t2_232);
CF := bool2bv(LT_64(RCX, t1_231));
OF := AND_1((bool2bv((t1_231[64:63]) == (t2_232[64:63]))), (XOR_1((t1_231[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_231)), t2_232)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1207:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x120e:
t_237 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_237[32:0]);
OF := bool2bv(t_237 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_237 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_32;
SF := unconstrained_33;
ZF := unconstrained_34;
AF := unconstrained_35;

label_0x1211:
RCX := (0bv32 ++ RDX[32:0]);

label_0x1213:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x121a:
t1_239 := RDX[32:0];
t2_240 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_240));
CF := bool2bv(LT_32((RDX[32:0]), t1_239));
OF := AND_1((bool2bv((t1_239[32:31]) == (t2_240[32:31]))), (XOR_1((t1_239[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_239)), t2_240)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x121c:
RCX := (0bv32 ++ RDX[32:0]);

label_0x121e:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x1221:
t_245 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_245[64:0];
OF := bool2bv(t_245 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_245 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_36;
SF := unconstrained_37;
ZF := unconstrained_38;
AF := unconstrained_39;

label_0x1225:
RAX := LOAD_LE_64(mem, RAX);

label_0x1228:
t1_247 := RAX;
t2_248 := RCX;
RAX := PLUS_64(RAX, t2_248);
CF := bool2bv(LT_64(RAX, t1_247));
OF := AND_1((bool2bv((t1_247[64:63]) == (t2_248[64:63]))), (XOR_1((t1_247[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_247)), t2_248)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x122b:
t1_253 := RAX;
t2_254 := 2bv64;
RAX := PLUS_64(RAX, t2_254);
CF := bool2bv(LT_64(RAX, t1_253));
OF := AND_1((bool2bv((t1_253[64:63]) == (t2_254[64:63]))), (XOR_1((t1_253[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_253)), t2_254)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x122f:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x1232:
t_259 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))), (XOR_32((RAX[32:0]), t_259)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_259, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))))[1:0]));
SF := t_259[32:31];
ZF := bool2bv(0bv32 == t_259);

label_0x1239:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x12a9;
}

label_0x123b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x1242:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), RAX[32:0]);

label_0x1249:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x1250:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), RAX[32:0]);

label_0x1257:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x125f:
t1_263 := RAX;
t2_264 := 8bv64;
RAX := PLUS_64(RAX, t2_264);
CF := bool2bv(LT_64(RAX, t1_263));
OF := AND_1((bool2bv((t1_263[64:63]) == (t2_264[64:63]))), (XOR_1((t1_263[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_263)), t2_264)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1263:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x126b:
t1_269 := RCX;
t2_270 := 4424bv64;
RCX := PLUS_64(RCX, t2_270);
CF := bool2bv(LT_64(RCX, t1_269));
OF := AND_1((bool2bv((t1_269[64:63]) == (t2_270[64:63]))), (XOR_1((t1_269[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_269)), t2_270)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1272:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x1279:
t_275 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_275[32:0]);
OF := bool2bv(t_275 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_275 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_40;
SF := unconstrained_41;
ZF := unconstrained_42;
AF := unconstrained_43;

label_0x127c:
RCX := (0bv32 ++ RDX[32:0]);

label_0x127e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x1285:
t1_277 := RDX[32:0];
t2_278 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_278));
CF := bool2bv(LT_32((RDX[32:0]), t1_277));
OF := AND_1((bool2bv((t1_277[32:31]) == (t2_278[32:31]))), (XOR_1((t1_277[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_277)), t2_278)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x1287:
RCX := (0bv32 ++ RDX[32:0]);

label_0x1289:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x128c:
t_283 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_283[64:0];
OF := bool2bv(t_283 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_283 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_44;
SF := unconstrained_45;
ZF := unconstrained_46;
AF := unconstrained_47;

label_0x1290:
RAX := LOAD_LE_64(mem, RAX);

label_0x1293:
t1_285 := RAX;
t2_286 := RCX;
RAX := PLUS_64(RAX, t2_286);
CF := bool2bv(LT_64(RAX, t1_285));
OF := AND_1((bool2bv((t1_285[64:63]) == (t2_286[64:63]))), (XOR_1((t1_285[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_285)), t2_286)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1296:
t1_291 := RAX;
t2_292 := 2bv64;
RAX := PLUS_64(RAX, t2_292);
CF := bool2bv(LT_64(RAX, t1_291));
OF := AND_1((bool2bv((t1_291[64:63]) == (t2_292[64:63]))), (XOR_1((t1_291[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_291)), t2_292)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x129a:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x129d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), RAX[32:0]);

label_0x12a4:
goto label_0x13d8;

label_0x12a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x12b1:
t1_297 := RAX;
t2_298 := 8bv64;
RAX := PLUS_64(RAX, t2_298);
CF := bool2bv(LT_64(RAX, t1_297));
OF := AND_1((bool2bv((t1_297[64:63]) == (t2_298[64:63]))), (XOR_1((t1_297[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_297)), t2_298)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12b5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x12bd:
t1_303 := RCX;
t2_304 := 4424bv64;
RCX := PLUS_64(RCX, t2_304);
CF := bool2bv(LT_64(RCX, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x12c4:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x12cb:
t_309 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, RCX)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RCX)) ,(0bv32 ++ LOAD_LE_32(mem, RCX))))));
RDX := (0bv32 ++ t_309[32:0]);
OF := bool2bv(t_309 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_309 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_48;
SF := unconstrained_49;
ZF := unconstrained_50;
AF := unconstrained_51;

label_0x12ce:
RCX := (0bv32 ++ RDX[32:0]);

label_0x12d0:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x12d7:
t1_311 := RDX[32:0];
t2_312 := RCX[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_312));
CF := bool2bv(LT_32((RDX[32:0]), t1_311));
OF := AND_1((bool2bv((t1_311[32:31]) == (t2_312[32:31]))), (XOR_1((t1_311[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_311)), t2_312)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x12d9:
RCX := (0bv32 ++ RDX[32:0]);

label_0x12db:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x12de:
t_317 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_317[64:0];
OF := bool2bv(t_317 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_317 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_52;
SF := unconstrained_53;
ZF := unconstrained_54;
AF := unconstrained_55;

label_0x12e2:
RAX := LOAD_LE_64(mem, RAX);

label_0x12e5:
t1_319 := RAX;
t2_320 := RCX;
RAX := PLUS_64(RAX, t2_320);
CF := bool2bv(LT_64(RAX, t1_319));
OF := AND_1((bool2bv((t1_319[64:63]) == (t2_320[64:63]))), (XOR_1((t1_319[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_319)), t2_320)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12e8:
t1_325 := RAX;
t2_326 := 2bv64;
RAX := PLUS_64(RAX, t2_326);
CF := bool2bv(LT_64(RAX, t1_325));
OF := AND_1((bool2bv((t1_325[64:63]) == (t2_326[64:63]))), (XOR_1((t1_325[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_325)), t2_326)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12ec:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RAX)));

label_0x12ef:
t_331 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))), (XOR_32((RAX[32:0]), t_331)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_331, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))))[1:0]));
SF := t_331[32:31];
ZF := bool2bv(0bv32 == t_331);

label_0x12f6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13d8;
}

label_0x12fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1304:
t1_335 := RAX;
t2_336 := 4396bv64;
RAX := PLUS_64(RAX, t2_336);
CF := bool2bv(LT_64(RAX, t1_335));
OF := AND_1((bool2bv((t1_335[64:63]) == (t2_336[64:63]))), (XOR_1((t1_335[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_335)), t2_336)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x130a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x1311:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x1313:
t_341 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_341, (RCX[32:0])));
OF := AND_32((XOR_32(t_341, (RCX[32:0]))), (XOR_32(t_341, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_341)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1315:
RCX := (0bv32 ++ RAX[32:0]);

label_0x1317:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4892bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x131c"} true;
call arbitrary_func();

label_0x131c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 200bv64), RAX[32:0]);

label_0x1323:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x132b:
t1_345 := RCX;
t2_346 := 4400bv64;
RCX := PLUS_64(RCX, t2_346);
CF := bool2bv(LT_64(RCX, t1_345));
OF := AND_1((bool2bv((t1_345[64:63]) == (t2_346[64:63]))), (XOR_1((t1_345[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_345)), t2_346)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1332:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 132bv64)));

label_0x1339:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x133b:
t_351 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_351, (RDX[32:0])));
OF := AND_32((XOR_32(t_351, (RDX[32:0]))), (XOR_32(t_351, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_351)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x133d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4930bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1342"} true;
call arbitrary_func();

label_0x1342:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x1349:
t1_355 := RCX[32:0];
t2_356 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_356));
CF := bool2bv(LT_32((RCX[32:0]), t1_355));
OF := AND_1((bool2bv((t1_355[32:31]) == (t2_356[32:31]))), (XOR_1((t1_355[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_355)), t2_356)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x134b:
RAX := (0bv32 ++ RCX[32:0]);

label_0x134d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 156bv64), RAX[32:0]);

label_0x1354:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x135c:
t1_361 := RAX;
t2_362 := 4396bv64;
RAX := PLUS_64(RAX, t2_362);
CF := bool2bv(LT_64(RAX, t1_361));
OF := AND_1((bool2bv((t1_361[64:63]) == (t2_362[64:63]))), (XOR_1((t1_361[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_361)), t2_362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1362:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x1369:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x136b:
t_367 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_367, (RCX[32:0])));
OF := AND_32((XOR_32(t_367, (RCX[32:0]))), (XOR_32(t_367, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_367)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x136d:
RCX := (0bv32 ++ RAX[32:0]);

label_0x136f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4980bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1374"} true;
call arbitrary_func();

label_0x1374:
mem := STORE_LE_32(mem, PLUS_64(RSP, 204bv64), RAX[32:0]);

label_0x137b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1383:
t1_371 := RCX;
t2_372 := 4400bv64;
RCX := PLUS_64(RCX, t2_372);
CF := bool2bv(LT_64(RCX, t1_371));
OF := AND_1((bool2bv((t1_371[64:63]) == (t2_372[64:63]))), (XOR_1((t1_371[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_371)), t2_372)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x138a:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x1391:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1393:
t_377 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_377, (RDX[32:0])));
OF := AND_32((XOR_32(t_377, (RDX[32:0]))), (XOR_32(t_377, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_377)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1395:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5018bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x139a"} true;
call arbitrary_func();

label_0x139a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 204bv64)));

label_0x13a1:
t1_381 := RCX[32:0];
t2_382 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_382));
CF := bool2bv(LT_32((RCX[32:0]), t1_381));
OF := AND_1((bool2bv((t1_381[32:31]) == (t2_382[32:31]))), (XOR_1((t1_381[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_381)), t2_382)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x13a3:
RAX := (0bv32 ++ RCX[32:0]);

label_0x13a5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 160bv64), RAX[32:0]);

label_0x13ac:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 156bv64)));

label_0x13b3:
t_387 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), t_387)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_387, (LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_387, 4bv32)), t_387)), 2bv32)), (XOR_32((RSHIFT_32(t_387, 4bv32)), t_387)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_387, 4bv32)), t_387)), 2bv32)), (XOR_32((RSHIFT_32(t_387, 4bv32)), t_387)))))[1:0]));
SF := t_387[32:31];
ZF := bool2bv(0bv32 == t_387);

label_0x13ba:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x13d8;
}

label_0x13bc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x13c3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), RAX[32:0]);

label_0x13ca:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 140bv64)));

label_0x13d1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), RAX[32:0]);

label_0x13d8:
goto label_0x1172;

label_0x13dd:
goto label_0x1144;

label_0x13e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x13ea:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x13ec:
t_391 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_391[32:31]) == (1bv32[32:31]))), (XOR_1((t_391[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_391)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x13ee:
mem := STORE_LE_32(mem, PLUS_64(RSP, 208bv64), RAX[32:0]);

label_0x13f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x13fd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1403:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1408:
t_397 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_397, 4bv64)), t_397)), 2bv64)), (XOR_64((RSHIFT_64(t_397, 4bv64)), t_397)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_397, 4bv64)), t_397)), 2bv64)), (XOR_64((RSHIFT_64(t_397, 4bv64)), t_397)))))[1:0]));
SF := t_397[64:63];
ZF := bool2bv(0bv64 == t_397);

label_0x140b:
if (bv2bool(ZF)) {
  goto label_0x140e;
}

label_0x140d:
assume false;

label_0x140e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x1416:
origDEST_401 := RAX;
origCOUNT_402 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), CF, LSHIFT_64(origDEST_401, (MINUS_64(64bv64, origCOUNT_402)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_402 == 1bv64)), origDEST_401[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), AF, unconstrained_59);

label_0x141a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1421:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1425:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x142d:
origDEST_407 := RCX;
origCOUNT_408 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), CF, LSHIFT_64(origDEST_407, (MINUS_64(64bv64, origCOUNT_408)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_408 == 1bv64)), origDEST_407[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_408 == 0bv64)), AF, unconstrained_61);

label_0x1431:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_62;
SF := unconstrained_63;
AF := unconstrained_64;
PF := unconstrained_65;

label_0x1435:
if (bv2bool(CF)) {
  goto label_0x1438;
}

label_0x1437:
assume false;

label_0x1438:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x1440:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x1447:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1449:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 164bv64)));

label_0x1450:
t_413 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_413[32:31]) == (1bv32[32:31]))), (XOR_1((t_413[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_413)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1452:
mem := STORE_LE_32(mem, PLUS_64(RSP, 164bv64), RAX[32:0]);

label_0x1459:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 132bv64)));

label_0x1461:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x1468:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x146d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5234bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1472"} true;
call arbitrary_func();

label_0x1472:
RDX := RAX;

label_0x1475:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x147a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5247bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x147f"} true;
call arbitrary_func();

label_0x147f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x1487:
t1_417 := RAX;
t2_418 := 4396bv64;
RAX := PLUS_64(RAX, t2_418);
CF := bool2bv(LT_64(RAX, t1_417));
OF := AND_1((bool2bv((t1_417[64:63]) == (t2_418[64:63]))), (XOR_1((t1_417[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_417)), t2_418)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x148d:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x148f:
t_423 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), t_423)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_423, (LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)), 2bv32)), (XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)), 2bv32)), (XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)))))[1:0]));
SF := t_423[32:31];
ZF := bool2bv(0bv32 == t_423);

label_0x1496:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14b9;
}

label_0x1498:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x14a0:
t1_427 := RAX;
t2_428 := 4400bv64;
RAX := PLUS_64(RAX, t2_428);
CF := bool2bv(LT_64(RAX, t1_427));
OF := AND_1((bool2bv((t1_427[64:63]) == (t2_428[64:63]))), (XOR_1((t1_427[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_427)), t2_428)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14a6:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x14a8:
t_433 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))), t_433)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_433, (LOAD_LE_32(mem, PLUS_64(RSP, 132bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)), 2bv32)), (XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)), 2bv32)), (XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)))))[1:0]));
SF := t_433[32:31];
ZF := bool2bv(0bv32 == t_433);

label_0x14af:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14b9;
}

label_0x14b1:
mem := STORE_LE_8(mem, PLUS_64(RSP, 152bv64), 1bv8);

label_0x14b9:
goto label_0xff3;

label_0x14be:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 152bv64))));

label_0x14c6:
t_437 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))))[1:0]));
SF := t_437[32:31];
ZF := bool2bv(0bv32 == t_437);

label_0x14c8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15f2;
}

label_0x14ce:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x14d3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5336bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14d8"} true;
call arbitrary_func();

label_0x14d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x14e0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_67;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14e6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x14eb:
t_443 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))))[1:0]));
SF := t_443[64:63];
ZF := bool2bv(0bv64 == t_443);

label_0x14ee:
if (bv2bool(ZF)) {
  goto label_0x14f1;
}

label_0x14f0:
assume false;

label_0x14f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x14f9:
origDEST_447 := RAX;
origCOUNT_448 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), CF, LSHIFT_64(origDEST_447, (MINUS_64(64bv64, origCOUNT_448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_448 == 1bv64)), origDEST_447[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), AF, unconstrained_70);

label_0x14fd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1504:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1508:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x1510:
origDEST_453 := RCX;
origCOUNT_454 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), CF, LSHIFT_64(origDEST_453, (MINUS_64(64bv64, origCOUNT_454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_454 == 1bv64)), origDEST_453[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), AF, unconstrained_72);

label_0x1514:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_73;
SF := unconstrained_74;
AF := unconstrained_75;
PF := unconstrained_76;

label_0x1518:
if (bv2bool(CF)) {
  goto label_0x151b;
}

label_0x151a:
assume false;

label_0x151b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x1523:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x152a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x1532:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1538:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x153d:
t_461 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)), 2bv64)), (XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)), 2bv64)), (XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)))))[1:0]));
SF := t_461[64:63];
ZF := bool2bv(0bv64 == t_461);

label_0x1540:
if (bv2bool(ZF)) {
  goto label_0x1543;
}

label_0x1542:
assume false;

label_0x1543:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x154b:
origDEST_465 := RAX;
origCOUNT_466 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), CF, LSHIFT_64(origDEST_465, (MINUS_64(64bv64, origCOUNT_466)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_466 == 1bv64)), origDEST_465[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), AF, unconstrained_80);

label_0x154f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1556:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x155a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x1562:
origDEST_471 := RCX;
origCOUNT_472 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), CF, LSHIFT_64(origDEST_471, (MINUS_64(64bv64, origCOUNT_472)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_472 == 1bv64)), origDEST_471[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), AF, unconstrained_82);

label_0x1566:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x156a:
if (bv2bool(CF)) {
  goto label_0x156d;
}

label_0x156c:
assume false;

label_0x156d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x1575:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x157b:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x1582:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x158a:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x158f:
origDEST_477 := RAX;
origCOUNT_478 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), CF, LSHIFT_64(origDEST_477, (MINUS_64(64bv64, origCOUNT_478)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_478 == 1bv64)), origDEST_477[64:63], unconstrained_87));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), AF, unconstrained_88);

label_0x1593:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x159b:
t1_483 := RCX;
t2_484 := RAX;
RCX := PLUS_64(RCX, t2_484);
CF := bool2bv(LT_64(RCX, t1_483));
OF := AND_1((bool2bv((t1_483[64:63]) == (t2_484[64:63]))), (XOR_1((t1_483[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_483)), t2_484)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x159e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RCX);

label_0x15a6:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x15ab:
origDEST_489 := RAX;
origCOUNT_490 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), CF, LSHIFT_64(origDEST_489, (MINUS_64(64bv64, origCOUNT_490)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_490 == 1bv64)), origDEST_489[64:63], unconstrained_89));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), AF, unconstrained_90);

label_0x15af:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15b3:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x15b5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 232bv64), RCX[32:0][8:0]);

label_0x15bc:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x15bf:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 232bv64))));

label_0x15c7:
origDEST_497 := RAX[32:0][8:0];
origCOUNT_498 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), CF, RSHIFT_8(origDEST_497, (MINUS_8(8bv8, origCOUNT_498)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_498 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_498 == 0bv8)), AF, unconstrained_93);

label_0x15c9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x15d1:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x15d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x15db:
t_505 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_505, 2bv64));
OF := AND_64((XOR_64(t_505, 2bv64)), (XOR_64(t_505, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_505)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15df:
RDI := RAX;

label_0x15e2:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_95;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x15e4:
RCX := (0bv32 ++ 2bv32);

label_0x15e9:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x15eb:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_96;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x15ed:
goto label_0x17aa;

label_0x15f2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x15f7:
t_509 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(8bv64[64:63]) ,(1bv64 ++ 8bv64) ,(0bv64 ++ 8bv64)))));
RAX := t_509[64:0];
OF := bool2bv(t_509 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_509 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_97;
SF := unconstrained_98;
ZF := unconstrained_99;
AF := unconstrained_100;

label_0x15fb:
RCX := RAX;

label_0x15fe:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5635bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1603"} true;
call arbitrary_func();

label_0x1603:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0x160b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x1613:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1619:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x161e:
t_513 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)), 2bv64)), (XOR_64((RSHIFT_64(t_513, 4bv64)), t_513)))))[1:0]));
SF := t_513[64:63];
ZF := bool2bv(0bv64 == t_513);

label_0x1621:
if (bv2bool(ZF)) {
  goto label_0x1624;
}

label_0x1623:
assume false;

label_0x1624:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x162c:
origDEST_517 := RAX;
origCOUNT_518 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), CF, LSHIFT_64(origDEST_517, (MINUS_64(64bv64, origCOUNT_518)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_518 == 1bv64)), origDEST_517[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), AF, unconstrained_104);

label_0x1630:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1637:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x163b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x1643:
origDEST_523 := RCX;
origCOUNT_524 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), CF, LSHIFT_64(origDEST_523, (MINUS_64(64bv64, origCOUNT_524)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_524 == 1bv64)), origDEST_523[64:63], unconstrained_105));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_524 == 0bv64)), AF, unconstrained_106);

label_0x1647:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_107;
SF := unconstrained_108;
AF := unconstrained_109;
PF := unconstrained_110;

label_0x164b:
if (bv2bool(CF)) {
  goto label_0x164e;
}

label_0x164d:
assume false;

label_0x164e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x1656:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x165e:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1661:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x1665:
t_529 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_529, 1bv32)), (XOR_32(t_529, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_529)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1667:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x166e:
goto label_0x1680;

label_0x1670:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x1677:
t_533 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_533, 1bv32)), (XOR_32(t_533, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_533)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1679:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x1680:
t_537 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_537)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_537, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))))[1:0]));
SF := t_537[32:31];
ZF := bool2bv(0bv32 == t_537);

label_0x1688:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x172e;
}

label_0x168e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x1695:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x169a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5791bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x169f"} true;
call arbitrary_func();

label_0x169f:
RAX := LOAD_LE_64(mem, RAX);

label_0x16a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x16aa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x16ae:
t_541 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_541, 1bv32)), (XOR_32(t_541, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_541)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x16b0:
t_545 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)))));
CF := bool2bv(LT_32(t_545, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)))));
OF := AND_32((XOR_32(t_545, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), (XOR_32(t_545, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_545)), (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x16b7:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x16b9:
t_549 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(8bv64[64:63]) ,(1bv64 ++ 8bv64) ,(0bv64 ++ 8bv64)))));
RAX := t_549[64:0];
OF := bool2bv(t_549 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_549 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_111;
SF := unconstrained_112;
ZF := unconstrained_113;
AF := unconstrained_114;

label_0x16bd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x16c5:
RCX := LOAD_LE_64(mem, RCX);

label_0x16c8:
t1_551 := RCX;
t2_552 := RAX;
RCX := PLUS_64(RCX, t2_552);
CF := bool2bv(LT_64(RCX, t1_551));
OF := AND_1((bool2bv((t1_551[64:63]) == (t2_552[64:63]))), (XOR_1((t1_551[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_551)), t2_552)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x16cb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RCX);

label_0x16d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x16db:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_115;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16e1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x16e6:
t_559 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)), 2bv64)), (XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)), 2bv64)), (XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)))))[1:0]));
SF := t_559[64:63];
ZF := bool2bv(0bv64 == t_559);

label_0x16e9:
if (bv2bool(ZF)) {
  goto label_0x16ec;
}

label_0x16eb:
assume false;

label_0x16ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x16f4:
origDEST_563 := RAX;
origCOUNT_564 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), CF, LSHIFT_64(origDEST_563, (MINUS_64(64bv64, origCOUNT_564)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_564 == 1bv64)), origDEST_563[64:63], unconstrained_117));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), AF, unconstrained_118);

label_0x16f8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x16ff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1703:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x170b:
origDEST_569 := RCX;
origCOUNT_570 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), CF, LSHIFT_64(origDEST_569, (MINUS_64(64bv64, origCOUNT_570)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_570 == 1bv64)), origDEST_569[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), AF, unconstrained_120);

label_0x170f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_121;
SF := unconstrained_122;
AF := unconstrained_123;
PF := unconstrained_124;

label_0x1713:
if (bv2bool(CF)) {
  goto label_0x1716;
}

label_0x1715:
assume false;

label_0x1716:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x171e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x1726:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1729:
goto label_0x1670;

label_0x172e:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1733:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5944bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1738"} true;
call arbitrary_func();

label_0x1738:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x173f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0x1747:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x174c:
origDEST_575 := RAX;
origCOUNT_576 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), CF, LSHIFT_64(origDEST_575, (MINUS_64(64bv64, origCOUNT_576)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_576 == 1bv64)), origDEST_575[64:63], unconstrained_125));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), AF, unconstrained_126);

label_0x1750:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x1758:
t1_581 := RCX;
t2_582 := RAX;
RCX := PLUS_64(RCX, t2_582);
CF := bool2bv(LT_64(RCX, t1_581));
OF := AND_1((bool2bv((t1_581[64:63]) == (t2_582[64:63]))), (XOR_1((t1_581[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_581)), t2_582)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x175b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RCX);

label_0x1763:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x1768:
origDEST_587 := RAX;
origCOUNT_588 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), CF, LSHIFT_64(origDEST_587, (MINUS_64(64bv64, origCOUNT_588)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_588 == 1bv64)), origDEST_587[64:63], unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv64)), AF, unconstrained_128);

label_0x176c:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_129;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1770:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x1772:
mem := STORE_LE_8(mem, PLUS_64(RSP, 280bv64), RCX[32:0][8:0]);

label_0x1779:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x177c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 280bv64))));

label_0x1784:
origDEST_595 := RAX[32:0][8:0];
origCOUNT_596 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), CF, RSHIFT_8(origDEST_595, (MINUS_8(8bv8, origCOUNT_596)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_596 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_130));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv8)), AF, unconstrained_131);

label_0x1786:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x178e:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x1790:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1798:
t_603 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_603, 2bv64));
OF := AND_64((XOR_64(t_603, 2bv64)), (XOR_64(t_603, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_603)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x179c:
RDI := RAX;

label_0x179f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_133;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x17a1:
RCX := (0bv32 ++ 2bv32);

label_0x17a6:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x17a8:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x17aa:
t1_607 := RSP;
t2_608 := 288bv64;
RSP := PLUS_64(RSP, t2_608);
CF := bool2bv(LT_64(RSP, t1_607));
OF := AND_1((bool2bv((t1_607[64:63]) == (t2_608[64:63]))), (XOR_1((t1_607[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_607)), t2_608)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x17b1:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x17b2:

ra_613 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_14,origCOUNT_22,origCOUNT_402,origCOUNT_408,origCOUNT_448,origCOUNT_454,origCOUNT_466,origCOUNT_472,origCOUNT_478,origCOUNT_490,origCOUNT_498,origCOUNT_518,origCOUNT_524,origCOUNT_54,origCOUNT_564,origCOUNT_570,origCOUNT_576,origCOUNT_588,origCOUNT_596,origCOUNT_60,origCOUNT_8,origDEST_13,origDEST_21,origDEST_401,origDEST_407,origDEST_447,origDEST_453,origDEST_465,origDEST_471,origDEST_477,origDEST_489,origDEST_497,origDEST_517,origDEST_523,origDEST_53,origDEST_563,origDEST_569,origDEST_575,origDEST_587,origDEST_59,origDEST_595,origDEST_7,ra_613,t1_121,t1_139,t1_149,t1_155,t1_165,t1_187,t1_193,t1_201,t1_209,t1_215,t1_225,t1_231,t1_239,t1_247,t1_253,t1_263,t1_269,t1_277,t1_285,t1_29,t1_291,t1_297,t1_303,t1_311,t1_319,t1_325,t1_335,t1_345,t1_35,t1_355,t1_361,t1_371,t1_381,t1_41,t1_417,t1_427,t1_483,t1_551,t1_581,t1_607,t1_69,t1_75,t1_99,t2_100,t2_122,t2_140,t2_150,t2_156,t2_166,t2_188,t2_194,t2_202,t2_210,t2_216,t2_226,t2_232,t2_240,t2_248,t2_254,t2_264,t2_270,t2_278,t2_286,t2_292,t2_298,t2_30,t2_304,t2_312,t2_320,t2_326,t2_336,t2_346,t2_356,t2_36,t2_362,t2_372,t2_382,t2_418,t2_42,t2_428,t2_484,t2_552,t2_582,t2_608,t2_70,t2_76,t_1,t_105,t_109,t_113,t_117,t_127,t_131,t_135,t_145,t_161,t_171,t_175,t_179,t_183,t_199,t_207,t_221,t_237,t_245,t_259,t_275,t_283,t_3,t_309,t_317,t_331,t_341,t_351,t_367,t_377,t_387,t_391,t_397,t_413,t_423,t_433,t_437,t_443,t_461,t_49,t_505,t_509,t_513,t_529,t_533,t_537,t_541,t_545,t_549,t_559,t_603,t_65,t_81,t_83,t_87,t_91,t_95;

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
var origCOUNT_402: bv64;
var origCOUNT_408: bv64;
var origCOUNT_448: bv64;
var origCOUNT_454: bv64;
var origCOUNT_466: bv64;
var origCOUNT_472: bv64;
var origCOUNT_478: bv64;
var origCOUNT_490: bv64;
var origCOUNT_498: bv8;
var origCOUNT_518: bv64;
var origCOUNT_524: bv64;
var origCOUNT_54: bv64;
var origCOUNT_564: bv64;
var origCOUNT_570: bv64;
var origCOUNT_576: bv64;
var origCOUNT_588: bv64;
var origCOUNT_596: bv8;
var origCOUNT_60: bv64;
var origCOUNT_8: bv64;
var origDEST_13: bv64;
var origDEST_21: bv64;
var origDEST_401: bv64;
var origDEST_407: bv64;
var origDEST_447: bv64;
var origDEST_453: bv64;
var origDEST_465: bv64;
var origDEST_471: bv64;
var origDEST_477: bv64;
var origDEST_489: bv64;
var origDEST_497: bv8;
var origDEST_517: bv64;
var origDEST_523: bv64;
var origDEST_53: bv64;
var origDEST_563: bv64;
var origDEST_569: bv64;
var origDEST_575: bv64;
var origDEST_587: bv64;
var origDEST_59: bv64;
var origDEST_595: bv8;
var origDEST_7: bv64;
var ra_613: bv64;
var t1_121: bv64;
var t1_139: bv64;
var t1_149: bv64;
var t1_155: bv64;
var t1_165: bv64;
var t1_187: bv64;
var t1_193: bv64;
var t1_201: bv32;
var t1_209: bv64;
var t1_215: bv64;
var t1_225: bv64;
var t1_231: bv64;
var t1_239: bv32;
var t1_247: bv64;
var t1_253: bv64;
var t1_263: bv64;
var t1_269: bv64;
var t1_277: bv32;
var t1_285: bv64;
var t1_29: bv64;
var t1_291: bv64;
var t1_297: bv64;
var t1_303: bv64;
var t1_311: bv32;
var t1_319: bv64;
var t1_325: bv64;
var t1_335: bv64;
var t1_345: bv64;
var t1_35: bv64;
var t1_355: bv32;
var t1_361: bv64;
var t1_371: bv64;
var t1_381: bv32;
var t1_41: bv64;
var t1_417: bv64;
var t1_427: bv64;
var t1_483: bv64;
var t1_551: bv64;
var t1_581: bv64;
var t1_607: bv64;
var t1_69: bv64;
var t1_75: bv64;
var t1_99: bv64;
var t2_100: bv64;
var t2_122: bv64;
var t2_140: bv64;
var t2_150: bv64;
var t2_156: bv64;
var t2_166: bv64;
var t2_188: bv64;
var t2_194: bv64;
var t2_202: bv32;
var t2_210: bv64;
var t2_216: bv64;
var t2_226: bv64;
var t2_232: bv64;
var t2_240: bv32;
var t2_248: bv64;
var t2_254: bv64;
var t2_264: bv64;
var t2_270: bv64;
var t2_278: bv32;
var t2_286: bv64;
var t2_292: bv64;
var t2_298: bv64;
var t2_30: bv64;
var t2_304: bv64;
var t2_312: bv32;
var t2_320: bv64;
var t2_326: bv64;
var t2_336: bv64;
var t2_346: bv64;
var t2_356: bv32;
var t2_36: bv64;
var t2_362: bv64;
var t2_372: bv64;
var t2_382: bv32;
var t2_418: bv64;
var t2_42: bv64;
var t2_428: bv64;
var t2_484: bv64;
var t2_552: bv64;
var t2_582: bv64;
var t2_608: bv64;
var t2_70: bv64;
var t2_76: bv64;
var t_1: bv64;
var t_105: bv32;
var t_109: bv32;
var t_113: bv32;
var t_117: bv32;
var t_127: bv32;
var t_131: bv32;
var t_135: bv32;
var t_145: bv32;
var t_161: bv32;
var t_171: bv32;
var t_175: bv32;
var t_179: bv32;
var t_183: bv32;
var t_199: bv64;
var t_207: bv128;
var t_221: bv32;
var t_237: bv64;
var t_245: bv128;
var t_259: bv32;
var t_275: bv64;
var t_283: bv128;
var t_3: bv64;
var t_309: bv64;
var t_317: bv128;
var t_331: bv32;
var t_341: bv32;
var t_351: bv32;
var t_367: bv32;
var t_377: bv32;
var t_387: bv32;
var t_391: bv32;
var t_397: bv64;
var t_413: bv32;
var t_423: bv32;
var t_433: bv32;
var t_437: bv32;
var t_443: bv64;
var t_461: bv64;
var t_49: bv64;
var t_505: bv64;
var t_509: bv128;
var t_513: bv64;
var t_529: bv32;
var t_533: bv32;
var t_537: bv32;
var t_541: bv32;
var t_545: bv32;
var t_549: bv128;
var t_559: bv64;
var t_603: bv64;
var t_65: bv32;
var t_81: bv64;
var t_83: bv32;
var t_87: bv32;
var t_91: bv32;
var t_95: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(64bv64);
axiom policy(448bv64);
axiom policy(1680bv64);
axiom policy(2128bv64);
axiom policy(3744bv64);
axiom policy(6080bv64);
axiom policy(7248bv64);
axiom policy(8560bv64);
axiom policy(9472bv64);
axiom policy(9664bv64);
