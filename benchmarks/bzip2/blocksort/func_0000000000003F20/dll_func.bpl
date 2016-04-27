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
axiom _function_addr_low == 16160bv64;
axiom _function_addr_high == 25760bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x3f20:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x3f25:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x3f2a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x3f2f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x3f34:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x3f35:
t_3 := RSP;
RSP := MINUS_64(RSP, 2304bv64);
CF := bool2bv(LT_64(t_3, 2304bv64));
OF := AND_64((XOR_64(t_3, 2304bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 2304bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3f3c:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x3f43:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1528bv64), RAX);

label_0x3f4b:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0x3f50:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0x3f54:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1536bv64), RAX);

label_0x3f5c:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0x3f61:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x3f65:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3f69:
RCX := (0bv32 ++ 819bv32);

label_0x3f6e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1544bv64), RCX);

label_0x3f76:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3f79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1544bv64));

label_0x3f81:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x3f84:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1528bv64));

label_0x3f8c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 1536bv64));

label_0x3f94:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x3f98:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x3f9f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1552bv64), RAX);

label_0x3fa7:
RAX := PLUS_64(RSP, 176bv64)[64:0];

label_0x3faf:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_10);

label_0x3fb3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1560bv64), RAX);

label_0x3fbb:
RAX := PLUS_64(RSP, 176bv64)[64:0];

label_0x3fc3:
origDEST_35 := RAX;
origCOUNT_36 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_12);

label_0x3fc7:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3fcb:
RCX := 1125899906842623bv64;

label_0x3fd5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1568bv64), RCX);

label_0x3fdd:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3fe0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1568bv64));

label_0x3fe8:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, RSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_15);

label_0x3feb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1552bv64));

label_0x3ff3:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 1560bv64));

label_0x3ffb:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x3fff:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x4006:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1576bv64), RAX);

label_0x400e:
RAX := PLUS_64(RSP, 592bv64)[64:0];

label_0x4016:
origDEST_51 := RAX;
origCOUNT_52 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), CF, LSHIFT_64(origDEST_51, (MINUS_64(64bv64, origCOUNT_52)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_52 == 1bv64)), origDEST_51[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), AF, unconstrained_18);

label_0x401a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1584bv64), RAX);

label_0x4022:
RAX := PLUS_64(RSP, 592bv64)[64:0];

label_0x402a:
origDEST_57 := RAX;
origCOUNT_58 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_20);

label_0x402e:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4032:
RCX := 1125899906842623bv64;

label_0x403c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1592bv64), RCX);

label_0x4044:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x4047:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1592bv64));

label_0x404f:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, RSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_23);

label_0x4052:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1576bv64));

label_0x405a:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 1584bv64));

label_0x4062:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x4066:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x406d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1600bv64), RAX);

label_0x4075:
RAX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x407d:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_26);

label_0x4081:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1608bv64), RAX);

label_0x4089:
RAX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x4091:
origDEST_79 := RAX;
origCOUNT_80 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_28);

label_0x4095:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4099:
RCX := 1125899906842623bv64;

label_0x40a3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1616bv64), RCX);

label_0x40ab:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x40ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1616bv64));

label_0x40b6:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, RSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_31);

label_0x40b9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1600bv64));

label_0x40c1:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 1608bv64));

label_0x40c9:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x40cd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), 0bv32);

label_0x40d8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x40e0:
t_95 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_95[64:0];
OF := bool2bv(t_95 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_95 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_33;
SF := unconstrained_34;
ZF := unconstrained_35;
AF := unconstrained_36;

label_0x40e4:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x40ec:
t1_97 := RCX;
t2_98 := RAX;
RCX := PLUS_64(RCX, t2_98);
CF := bool2bv(LT_64(RCX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x40ef:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1624bv64), RCX);

label_0x40f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1624bv64));

label_0x40ff:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4105:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x410a:
t_105 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))))[1:0]));
SF := t_105[64:63];
ZF := bool2bv(0bv64 == t_105);

label_0x410d:
if (bv2bool(ZF)) {
  goto label_0x4110;
}

label_0x410f:
assume false;

label_0x4110:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1624bv64));

label_0x4118:
origDEST_109 := RAX;
origCOUNT_110 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_40);

label_0x411c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4123:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4127:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1624bv64));

label_0x412f:
origDEST_115 := RCX;
origCOUNT_116 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), CF, LSHIFT_64(origDEST_115, (MINUS_64(64bv64, origCOUNT_116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_116 == 1bv64)), origDEST_115[64:63], unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), AF, unconstrained_42);

label_0x4133:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_43;
SF := unconstrained_44;
AF := unconstrained_45;
PF := unconstrained_46;

label_0x4137:
if (bv2bool(CF)) {
  goto label_0x413a;
}

label_0x4139:
assume false;

label_0x413a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1624bv64));

label_0x4142:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 2352bv64)));

label_0x4149:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x414b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x4153:
t_121 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_121[64:0];
OF := bool2bv(t_121 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_121 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_47;
SF := unconstrained_48;
ZF := unconstrained_49;
AF := unconstrained_50;

label_0x4157:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x415f:
t1_123 := RCX;
t2_124 := RAX;
RCX := PLUS_64(RCX, t2_124);
CF := bool2bv(LT_64(RCX, t1_123));
OF := AND_1((bool2bv((t1_123[64:63]) == (t2_124[64:63]))), (XOR_1((t1_123[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_123)), t2_124)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4162:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1632bv64), RCX);

label_0x416a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1632bv64));

label_0x4172:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4178:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x417d:
t_131 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))))[1:0]));
SF := t_131[64:63];
ZF := bool2bv(0bv64 == t_131);

label_0x4180:
if (bv2bool(ZF)) {
  goto label_0x4183;
}

label_0x4182:
assume false;

label_0x4183:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1632bv64));

label_0x418b:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_54);

label_0x418f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4196:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x419a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1632bv64));

label_0x41a2:
origDEST_141 := RCX;
origCOUNT_142 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), CF, LSHIFT_64(origDEST_141, (MINUS_64(64bv64, origCOUNT_142)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_142 == 1bv64)), origDEST_141[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), AF, unconstrained_56);

label_0x41a6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x41aa:
if (bv2bool(CF)) {
  goto label_0x41ad;
}

label_0x41ac:
assume false;

label_0x41ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1632bv64));

label_0x41b5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 2360bv64)));

label_0x41bc:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x41be:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x41c6:
t_147 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_147[64:0];
OF := bool2bv(t_147 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_147 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_61;
SF := unconstrained_62;
ZF := unconstrained_63;
AF := unconstrained_64;

label_0x41ca:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x41d2:
t1_149 := RCX;
t2_150 := RAX;
RCX := PLUS_64(RCX, t2_150);
CF := bool2bv(LT_64(RCX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x41d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1640bv64), RCX);

label_0x41dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1640bv64));

label_0x41e5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41eb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x41f0:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x41f3:
if (bv2bool(ZF)) {
  goto label_0x41f6;
}

label_0x41f5:
assume false;

label_0x41f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1640bv64));

label_0x41fe:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_68);

label_0x4202:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4209:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x420d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1640bv64));

label_0x4215:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_70);

label_0x4219:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_71;
SF := unconstrained_72;
AF := unconstrained_73;
PF := unconstrained_74;

label_0x421d:
if (bv2bool(CF)) {
  goto label_0x4220;
}

label_0x421f:
assume false;

label_0x4220:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1640bv64));

label_0x4228:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 2368bv64)));

label_0x422f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4231:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x4238:
t_173 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_173[32:31]) == (1bv32[32:31]))), (XOR_1((t_173[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_173)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x423a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x4241:
t_177 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), t_177)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_177, (LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))))[1:0]));
SF := t_177[32:31];
ZF := bool2bv(0bv32 == t_177);

label_0x4249:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x641b;
}

label_0x424f:
t_181 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 100bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 100bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), 100bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))), t_181)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_181, (LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))))), 100bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))))[1:0]));
SF := t_181[32:31];
ZF := bool2bv(0bv32 == t_181);

label_0x4257:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x4263;
}

label_0x4259:
RCX := (0bv32 ++ 1001bv32);

label_0x425e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 16995bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4263"} true;
call arbitrary_func();

label_0x4263:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x426a:
t_185 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_185, 1bv32)), (XOR_32(t_185, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_185)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x426c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x4273:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x427b:
t_189 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_189[64:0];
OF := bool2bv(t_189 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_189 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_75;
SF := unconstrained_76;
ZF := unconstrained_77;
AF := unconstrained_78;

label_0x427f:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x4287:
t1_191 := RCX;
t2_192 := RAX;
RCX := PLUS_64(RCX, t2_192);
CF := bool2bv(LT_64(RCX, t1_191));
OF := AND_1((bool2bv((t1_191[64:63]) == (t2_192[64:63]))), (XOR_1((t1_191[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_191)), t2_192)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x428a:
RAX := RCX;

label_0x428d:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x428f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1456bv64), RAX[32:0]);

label_0x4296:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x429e:
t_197 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_197[64:0];
OF := bool2bv(t_197 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_197 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_79;
SF := unconstrained_80;
ZF := unconstrained_81;
AF := unconstrained_82;

label_0x42a2:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x42aa:
t1_199 := RCX;
t2_200 := RAX;
RCX := PLUS_64(RCX, t2_200);
CF := bool2bv(LT_64(RCX, t1_199));
OF := AND_1((bool2bv((t1_199[64:63]) == (t2_200[64:63]))), (XOR_1((t1_199[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_199)), t2_200)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x42ad:
RAX := RCX;

label_0x42b0:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x42b2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1460bv64), RAX[32:0]);

label_0x42b9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x42c1:
t_205 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_205[64:0];
OF := bool2bv(t_205 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_205 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_83;
SF := unconstrained_84;
ZF := unconstrained_85;
AF := unconstrained_86;

label_0x42c5:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x42cd:
t1_207 := RCX;
t2_208 := RAX;
RCX := PLUS_64(RCX, t2_208);
CF := bool2bv(LT_64(RCX, t1_207));
OF := AND_1((bool2bv((t1_207[64:63]) == (t2_208[64:63]))), (XOR_1((t1_207[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_207)), t2_208)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x42d0:
RAX := RCX;

label_0x42d3:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x42d5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1464bv64), RAX[32:0]);

label_0x42dc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x42e3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x42ea:
t_213 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_213, (RAX[32:0])));
OF := AND_32((XOR_32(t_213, (RAX[32:0]))), (XOR_32(t_213, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_213)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x42ec:
RAX := (0bv32 ++ RCX[32:0]);

label_0x42ee:
t_217 := MINUS_32((RAX[32:0]), 20bv32);
CF := bool2bv(LT_32((RAX[32:0]), 20bv32));
OF := AND_32((XOR_32((RAX[32:0]), 20bv32)), (XOR_32((RAX[32:0]), t_217)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_217, (RAX[32:0]))), 20bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)), 2bv32)), (XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)), 2bv32)), (XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)))))[1:0]));
SF := t_217[32:31];
ZF := bool2bv(0bv32 == t_217);

label_0x42f1:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x42fd;
}

label_0x42f3:
t_221 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64))), 14bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64))), 14bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64))), 14bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64))), t_221)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_221, (LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64))))), 14bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))))[1:0]));
SF := t_221[32:31];
ZF := bool2bv(0bv32 == t_221);

label_0x42fb:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4367;
}

label_0x42fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2376bv64));

label_0x4305:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x430a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x4311:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x4315:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x431c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x4320:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4327:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x432b:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 2344bv64)));

label_0x4333:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 2336bv64));

label_0x433b:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x4343:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x434b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 17232bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4350"} true;
call arbitrary_func();

label_0x4350:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2376bv64));

label_0x4358:
t_225 := MINUS_32((LOAD_LE_32(mem, RAX)), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 0bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_225)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_225, (LOAD_LE_32(mem, RAX)))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))))[1:0]));
SF := t_225[32:31];
ZF := bool2bv(0bv32 == t_225);

label_0x435b:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x4362;
}

label_0x435d:
goto label_0x641b;

label_0x4362:
goto label_0x4241;

label_0x4367:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x436e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4375:
t1_229 := RCX[32:0];
t2_230 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_230));
CF := bool2bv(LT_32((RCX[32:0]), t1_229));
OF := AND_1((bool2bv((t1_229[32:31]) == (t2_230[32:31]))), (XOR_1((t1_229[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_229)), t2_230)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4377:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4379:
origDEST_235 := RAX[32:0];
origCOUNT_236 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ ARSHIFT_32((RAX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), CF, LSHIFT_32(origDEST_235, (MINUS_32(32bv32, origCOUNT_236)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv32)), 0bv1, unconstrained_87));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv32)), AF, unconstrained_88);

label_0x437b:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x437d:
t_241 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_241[64:0];
OF := bool2bv(t_241 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_241 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_89;
SF := unconstrained_90;
ZF := unconstrained_91;
AF := unconstrained_92;

label_0x4381:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4389:
t1_243 := RCX;
t2_244 := RAX;
RCX := PLUS_64(RCX, t2_244);
CF := bool2bv(LT_64(RCX, t1_243));
OF := AND_1((bool2bv((t1_243[64:63]) == (t2_244[64:63]))), (XOR_1((t1_243[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_243)), t2_244)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x438c:
RAX := RCX;

label_0x438f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x4396:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x4398:
t1_249 := RAX[32:0];
t2_250 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_250));
CF := bool2bv(LT_32((RAX[32:0]), t1_249));
OF := AND_1((bool2bv((t1_249[32:31]) == (t2_250[32:31]))), (XOR_1((t1_249[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_249)), t2_250)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x439a:
RAX := (0bv32 ++ RAX[32:0]);

label_0x439c:
t_255 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_255[64:0];
OF := bool2bv(t_255 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_255 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_93;
SF := unconstrained_94;
ZF := unconstrained_95;
AF := unconstrained_96;

label_0x43a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x43a8:
t1_257 := RCX;
t2_258 := RAX;
RCX := PLUS_64(RCX, t2_258);
CF := bool2bv(LT_64(RCX, t1_257));
OF := AND_1((bool2bv((t1_257[64:63]) == (t2_258[64:63]))), (XOR_1((t1_257[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_257)), t2_258)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x43ab:
RAX := RCX;

label_0x43ae:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)))));

label_0x43b6:
t_263 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_263[64:0];
OF := bool2bv(t_263 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_263 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_97;
SF := unconstrained_98;
ZF := unconstrained_99;
AF := unconstrained_100;

label_0x43ba:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x43c2:
t1_265 := RDX;
t2_266 := RCX;
RDX := PLUS_64(RDX, t2_266);
CF := bool2bv(LT_64(RDX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x43c5:
RCX := RDX;

label_0x43c8:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x43cf:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x43d1:
t1_271 := RCX[32:0];
t2_272 := RDX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_272));
CF := bool2bv(LT_32((RCX[32:0]), t1_271));
OF := AND_1((bool2bv((t1_271[32:31]) == (t2_272[32:31]))), (XOR_1((t1_271[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_271)), t2_272)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x43d3:
RCX := (0bv32 ++ RCX[32:0]);

label_0x43d5:
t_277 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RCX := t_277[64:0];
OF := bool2bv(t_277 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_277 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_101;
SF := unconstrained_102;
ZF := unconstrained_103;
AF := unconstrained_104;

label_0x43d9:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x43e1:
t1_279 := RDX;
t2_280 := RCX;
RDX := PLUS_64(RDX, t2_280);
CF := bool2bv(LT_64(RDX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x43e4:
RCX := RDX;

label_0x43e7:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)))));

label_0x43ef:
t_285 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RDX := t_285[64:0];
OF := bool2bv(t_285 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_285 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_105;
SF := unconstrained_106;
ZF := unconstrained_107;
AF := unconstrained_108;

label_0x43f3:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x43fb:
t1_287 := R8;
t2_288 := RDX;
R8 := PLUS_64(R8, t2_288);
CF := bool2bv(LT_64(R8, t1_287));
OF := AND_1((bool2bv((t1_287[64:63]) == (t2_288[64:63]))), (XOR_1((t1_287[64:63]), (R8[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R8, t1_287)), t2_288)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))))[1:0]));
SF := R8[64:63];
ZF := bool2bv(0bv64 == R8);

label_0x43fe:
RDX := R8;

label_0x4401:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x4409:
RDX := (0bv32 ++ LOAD_LE_32(mem, RDX));

label_0x440b:
t1_293 := RDX[32:0];
t2_294 := R8[32:0];
RDX := (0bv32 ++ PLUS_32((RDX[32:0]), t2_294));
CF := bool2bv(LT_32((RDX[32:0]), t1_293));
OF := AND_1((bool2bv((t1_293[32:31]) == (t2_294[32:31]))), (XOR_1((t1_293[32:31]), (RDX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t1_293)), t2_294)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x440e:
RDX := (0bv32 ++ RDX[32:0]);

label_0x4410:
t_299 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RDX := t_299[64:0];
OF := bool2bv(t_299 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_299 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_109;
SF := unconstrained_110;
ZF := unconstrained_111;
AF := unconstrained_112;

label_0x4414:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x441c:
t1_301 := R8;
t2_302 := RDX;
R8 := PLUS_64(R8, t2_302);
CF := bool2bv(LT_64(R8, t1_301));
OF := AND_1((bool2bv((t1_301[64:63]) == (t2_302[64:63]))), (XOR_1((t1_301[64:63]), (R8[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R8, t1_301)), t2_302)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))))[1:0]));
SF := R8[64:63];
ZF := bool2bv(0bv64 == R8);

label_0x441f:
RDX := R8;

label_0x4422:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1648bv64), RDX);

label_0x442a:
R8 := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x442e:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x4431:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1648bv64));

label_0x4439:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x443c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 17473bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4441"} true;
call arbitrary_func();

label_0x4441:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x4444:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1448bv64), RAX[32:0]);

label_0x444b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4452:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1432bv64), RAX[32:0]);

label_0x4459:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4460:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1424bv64), RAX[32:0]);

label_0x4467:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x446e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1436bv64), RAX[32:0]);

label_0x4475:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x447c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1428bv64), RAX[32:0]);

label_0x4483:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_113;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4485:
t_307 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_307)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_307, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)), 2bv32)), (XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)), 2bv32)), (XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)))))[1:0]));
SF := t_307[32:31];
ZF := bool2bv(0bv32 == t_307);

label_0x4488:
if (bv2bool(ZF)) {
  goto label_0x49c5;
}

label_0x448e:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_114;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4490:
t_311 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_311)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_311, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))))[1:0]));
SF := t_311[32:31];
ZF := bool2bv(0bv32 == t_311);

label_0x4493:
if (bv2bool(ZF)) {
  goto label_0x4677;
}

label_0x4499:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x44a0:
t_315 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), t_315)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_315, (LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_315, 4bv32)), t_315)), 2bv32)), (XOR_32((RSHIFT_32(t_315, 4bv32)), t_315)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_315, 4bv32)), t_315)), 2bv32)), (XOR_32((RSHIFT_32(t_315, 4bv32)), t_315)))))[1:0]));
SF := t_315[32:31];
ZF := bool2bv(0bv32 == t_315);

label_0x44a7:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x44ae;
}

label_0x44a9:
goto label_0x4677;

label_0x44ae:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)))));

label_0x44b6:
t_319 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_319[64:0];
OF := bool2bv(t_319 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_319 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_115;
SF := unconstrained_116;
ZF := unconstrained_117;
AF := unconstrained_118;

label_0x44ba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x44c2:
t1_321 := RCX;
t2_322 := RAX;
RCX := PLUS_64(RCX, t2_322);
CF := bool2bv(LT_64(RCX, t1_321));
OF := AND_1((bool2bv((t1_321[64:63]) == (t2_322[64:63]))), (XOR_1((t1_321[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_321)), t2_322)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x44c5:
RAX := RCX;

label_0x44c8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x44cf:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x44d1:
t1_327 := RAX[32:0];
t2_328 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_328));
CF := bool2bv(LT_32((RAX[32:0]), t1_327));
OF := AND_1((bool2bv((t1_327[32:31]) == (t2_328[32:31]))), (XOR_1((t1_327[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_327)), t2_328)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x44d3:
RAX := (0bv32 ++ RAX[32:0]);

label_0x44d5:
t_333 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_333[64:0];
OF := bool2bv(t_333 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_333 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_119;
SF := unconstrained_120;
ZF := unconstrained_121;
AF := unconstrained_122;

label_0x44d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x44e1:
t1_335 := RCX;
t2_336 := RAX;
RCX := PLUS_64(RCX, t2_336);
CF := bool2bv(LT_64(RCX, t1_335));
OF := AND_1((bool2bv((t1_335[64:63]) == (t2_336[64:63]))), (XOR_1((t1_335[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_335)), t2_336)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x44e4:
RAX := RCX;

label_0x44e7:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x44ea:
t_341 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64)))));
CF := bool2bv(LT_32(t_341, (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64)))));
OF := AND_32((XOR_32(t_341, (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64))))), (XOR_32(t_341, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_341)), (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x44f1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1440bv64), RAX[32:0]);

label_0x44f8:
t_345 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), t_345)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_345, (LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))))[1:0]));
SF := t_345[32:31];
ZF := bool2bv(0bv32 == t_345);

label_0x4500:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4656;
}

label_0x4506:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)))));

label_0x450e:
t_349 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_349[64:0];
OF := bool2bv(t_349 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_349 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_123;
SF := unconstrained_124;
ZF := unconstrained_125;
AF := unconstrained_126;

label_0x4512:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x451a:
t1_351 := RCX;
t2_352 := RAX;
RCX := PLUS_64(RCX, t2_352);
CF := bool2bv(LT_64(RCX, t1_351));
OF := AND_1((bool2bv((t1_351[64:63]) == (t2_352[64:63]))), (XOR_1((t1_351[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_351)), t2_352)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x451d:
RAX := RCX;

label_0x4520:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x4522:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1468bv64), RAX[32:0]);

label_0x4529:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)))));

label_0x4531:
t_357 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_357[64:0];
OF := bool2bv(t_357 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_357 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_127;
SF := unconstrained_128;
ZF := unconstrained_129;
AF := unconstrained_130;

label_0x4535:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x453d:
t1_359 := RCX;
t2_360 := RAX;
RCX := PLUS_64(RCX, t2_360);
CF := bool2bv(LT_64(RCX, t1_359));
OF := AND_1((bool2bv((t1_359[64:63]) == (t2_360[64:63]))), (XOR_1((t1_359[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_359)), t2_360)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4540:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1656bv64), RCX);

label_0x4548:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)))));

label_0x4550:
t_365 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_365[64:0];
OF := bool2bv(t_365 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_365 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_131;
SF := unconstrained_132;
ZF := unconstrained_133;
AF := unconstrained_134;

label_0x4554:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x455c:
t1_367 := RCX;
t2_368 := RAX;
RCX := PLUS_64(RCX, t2_368);
CF := bool2bv(LT_64(RCX, t1_367));
OF := AND_1((bool2bv((t1_367[64:63]) == (t2_368[64:63]))), (XOR_1((t1_367[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_367)), t2_368)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x455f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1664bv64), RCX);

label_0x4567:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1664bv64));

label_0x456f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4575:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x457a:
t_375 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)), 2bv64)), (XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)), 2bv64)), (XOR_64((RSHIFT_64(t_375, 4bv64)), t_375)))))[1:0]));
SF := t_375[64:63];
ZF := bool2bv(0bv64 == t_375);

label_0x457d:
if (bv2bool(ZF)) {
  goto label_0x4580;
}

label_0x457f:
assume false;

label_0x4580:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1664bv64));

label_0x4588:
origDEST_379 := RAX;
origCOUNT_380 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), CF, LSHIFT_64(origDEST_379, (MINUS_64(64bv64, origCOUNT_380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_380 == 1bv64)), origDEST_379[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), AF, unconstrained_138);

label_0x458c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4593:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4597:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1664bv64));

label_0x459f:
origDEST_385 := RCX;
origCOUNT_386 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), CF, LSHIFT_64(origDEST_385, (MINUS_64(64bv64, origCOUNT_386)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_386 == 1bv64)), origDEST_385[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv64)), AF, unconstrained_140);

label_0x45a3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_141;
SF := unconstrained_142;
AF := unconstrained_143;
PF := unconstrained_144;

label_0x45a7:
if (bv2bool(CF)) {
  goto label_0x45aa;
}

label_0x45a9:
assume false;

label_0x45aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1664bv64));

label_0x45b2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1656bv64));

label_0x45ba:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x45bc:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x45be:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)))));

label_0x45c6:
t_391 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_391[64:0];
OF := bool2bv(t_391 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_391 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_145;
SF := unconstrained_146;
ZF := unconstrained_147;
AF := unconstrained_148;

label_0x45ca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x45d2:
t1_393 := RCX;
t2_394 := RAX;
RCX := PLUS_64(RCX, t2_394);
CF := bool2bv(LT_64(RCX, t1_393));
OF := AND_1((bool2bv((t1_393[64:63]) == (t2_394[64:63]))), (XOR_1((t1_393[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_393)), t2_394)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x45d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1672bv64), RCX);

label_0x45dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1672bv64));

label_0x45e5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_149;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x45eb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x45f0:
t_401 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_150;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))))[1:0]));
SF := t_401[64:63];
ZF := bool2bv(0bv64 == t_401);

label_0x45f3:
if (bv2bool(ZF)) {
  goto label_0x45f6;
}

label_0x45f5:
assume false;

label_0x45f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1672bv64));

label_0x45fe:
origDEST_405 := RAX;
origCOUNT_406 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), CF, LSHIFT_64(origDEST_405, (MINUS_64(64bv64, origCOUNT_406)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_406 == 1bv64)), origDEST_405[64:63], unconstrained_151));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), AF, unconstrained_152);

label_0x4602:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4609:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x460d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1672bv64));

label_0x4615:
origDEST_411 := RCX;
origCOUNT_412 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), CF, LSHIFT_64(origDEST_411, (MINUS_64(64bv64, origCOUNT_412)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_412 == 1bv64)), origDEST_411[64:63], unconstrained_153));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), AF, unconstrained_154);

label_0x4619:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_155;
SF := unconstrained_156;
AF := unconstrained_157;
PF := unconstrained_158;

label_0x461d:
if (bv2bool(CF)) {
  goto label_0x4620;
}

label_0x461f:
assume false;

label_0x4620:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1672bv64));

label_0x4628:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1468bv64)));

label_0x462f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4631:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4638:
t_417 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_417[32:31]) == (1bv32[32:31]))), (XOR_1((t_417[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_417)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x463a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1432bv64), RAX[32:0]);

label_0x4641:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4648:
t_421 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_421[32:31]) == (1bv32[32:31]))), (XOR_1((t_421[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_421)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x464a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1424bv64), RAX[32:0]);

label_0x4651:
goto label_0x448e;

label_0x4656:
t_425 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), t_425)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_425, (LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)), 2bv32)), (XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)), 2bv32)), (XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)))))[1:0]));
SF := t_425[32:31];
ZF := bool2bv(0bv32 == t_425);

label_0x465e:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4662;
}

label_0x4660:
goto label_0x4677;

label_0x4662:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4669:
t_429 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_429[32:31]) == (1bv32[32:31]))), (XOR_1((t_429[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_429)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x466b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1424bv64), RAX[32:0]);

label_0x4672:
goto label_0x448e;

label_0x4677:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_159;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4679:
t_433 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_433)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_433, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)), 2bv32)), (XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)), 2bv32)), (XOR_32((RSHIFT_32(t_433, 4bv32)), t_433)))))[1:0]));
SF := t_433[32:31];
ZF := bool2bv(0bv32 == t_433);

label_0x467c:
if (bv2bool(ZF)) {
  goto label_0x4860;
}

label_0x4682:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4689:
t_437 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), t_437)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_437, (LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))))[1:0]));
SF := t_437[32:31];
ZF := bool2bv(0bv32 == t_437);

label_0x4690:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4697;
}

label_0x4692:
goto label_0x4860;

label_0x4697:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)))));

label_0x469f:
t_441 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_441[64:0];
OF := bool2bv(t_441 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_441 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_160;
SF := unconstrained_161;
ZF := unconstrained_162;
AF := unconstrained_163;

label_0x46a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x46ab:
t1_443 := RCX;
t2_444 := RAX;
RCX := PLUS_64(RCX, t2_444);
CF := bool2bv(LT_64(RCX, t1_443));
OF := AND_1((bool2bv((t1_443[64:63]) == (t2_444[64:63]))), (XOR_1((t1_443[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_443)), t2_444)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x46ae:
RAX := RCX;

label_0x46b1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x46b8:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x46ba:
t1_449 := RAX[32:0];
t2_450 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_450));
CF := bool2bv(LT_32((RAX[32:0]), t1_449));
OF := AND_1((bool2bv((t1_449[32:31]) == (t2_450[32:31]))), (XOR_1((t1_449[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_449)), t2_450)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x46bc:
RAX := (0bv32 ++ RAX[32:0]);

label_0x46be:
t_455 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_455[64:0];
OF := bool2bv(t_455 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_455 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_164;
SF := unconstrained_165;
ZF := unconstrained_166;
AF := unconstrained_167;

label_0x46c2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2328bv64));

label_0x46ca:
t1_457 := RCX;
t2_458 := RAX;
RCX := PLUS_64(RCX, t2_458);
CF := bool2bv(LT_64(RCX, t1_457));
OF := AND_1((bool2bv((t1_457[64:63]) == (t2_458[64:63]))), (XOR_1((t1_457[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_457)), t2_458)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x46cd:
RAX := RCX;

label_0x46d0:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x46d3:
t_463 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64)))));
CF := bool2bv(LT_32(t_463, (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64)))));
OF := AND_32((XOR_32(t_463, (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64))))), (XOR_32(t_463, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_463)), (LOAD_LE_32(mem, PLUS_64(RSP, 1448bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x46da:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1440bv64), RAX[32:0]);

label_0x46e1:
t_467 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), t_467)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_467, (LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_467, 4bv32)), t_467)), 2bv32)), (XOR_32((RSHIFT_32(t_467, 4bv32)), t_467)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_467, 4bv32)), t_467)), 2bv32)), (XOR_32((RSHIFT_32(t_467, 4bv32)), t_467)))))[1:0]));
SF := t_467[32:31];
ZF := bool2bv(0bv32 == t_467);

label_0x46e9:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x483f;
}

label_0x46ef:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)))));

label_0x46f7:
t_471 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_471[64:0];
OF := bool2bv(t_471 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_471 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_168;
SF := unconstrained_169;
ZF := unconstrained_170;
AF := unconstrained_171;

label_0x46fb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4703:
t1_473 := RCX;
t2_474 := RAX;
RCX := PLUS_64(RCX, t2_474);
CF := bool2bv(LT_64(RCX, t1_473));
OF := AND_1((bool2bv((t1_473[64:63]) == (t2_474[64:63]))), (XOR_1((t1_473[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_473)), t2_474)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4706:
RAX := RCX;

label_0x4709:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x470b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1472bv64), RAX[32:0]);

label_0x4712:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)))));

label_0x471a:
t_479 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_479[64:0];
OF := bool2bv(t_479 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_479 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_172;
SF := unconstrained_173;
ZF := unconstrained_174;
AF := unconstrained_175;

label_0x471e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4726:
t1_481 := RCX;
t2_482 := RAX;
RCX := PLUS_64(RCX, t2_482);
CF := bool2bv(LT_64(RCX, t1_481));
OF := AND_1((bool2bv((t1_481[64:63]) == (t2_482[64:63]))), (XOR_1((t1_481[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_481)), t2_482)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4729:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1680bv64), RCX);

label_0x4731:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)))));

label_0x4739:
t_487 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_487[64:0];
OF := bool2bv(t_487 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_487 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_176;
SF := unconstrained_177;
ZF := unconstrained_178;
AF := unconstrained_179;

label_0x473d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4745:
t1_489 := RCX;
t2_490 := RAX;
RCX := PLUS_64(RCX, t2_490);
CF := bool2bv(LT_64(RCX, t1_489));
OF := AND_1((bool2bv((t1_489[64:63]) == (t2_490[64:63]))), (XOR_1((t1_489[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_489)), t2_490)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4748:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1688bv64), RCX);

label_0x4750:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1688bv64));

label_0x4758:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_180;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x475e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4763:
t_497 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_181;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)), 2bv64)), (XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)), 2bv64)), (XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)))))[1:0]));
SF := t_497[64:63];
ZF := bool2bv(0bv64 == t_497);

label_0x4766:
if (bv2bool(ZF)) {
  goto label_0x4769;
}

label_0x4768:
assume false;

label_0x4769:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1688bv64));

label_0x4771:
origDEST_501 := RAX;
origCOUNT_502 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), CF, LSHIFT_64(origDEST_501, (MINUS_64(64bv64, origCOUNT_502)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_502 == 1bv64)), origDEST_501[64:63], unconstrained_182));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_502 == 0bv64)), AF, unconstrained_183);

label_0x4775:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x477c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4780:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1688bv64));

label_0x4788:
origDEST_507 := RCX;
origCOUNT_508 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), CF, LSHIFT_64(origDEST_507, (MINUS_64(64bv64, origCOUNT_508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_508 == 1bv64)), origDEST_507[64:63], unconstrained_184));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), AF, unconstrained_185);

label_0x478c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_186;
SF := unconstrained_187;
AF := unconstrained_188;
PF := unconstrained_189;

label_0x4790:
if (bv2bool(CF)) {
  goto label_0x4793;
}

label_0x4792:
assume false;

label_0x4793:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1688bv64));

label_0x479b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1680bv64));

label_0x47a3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x47a5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x47a7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)))));

label_0x47af:
t_513 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_513[64:0];
OF := bool2bv(t_513 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_513 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_190;
SF := unconstrained_191;
ZF := unconstrained_192;
AF := unconstrained_193;

label_0x47b3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x47bb:
t1_515 := RCX;
t2_516 := RAX;
RCX := PLUS_64(RCX, t2_516);
CF := bool2bv(LT_64(RCX, t1_515));
OF := AND_1((bool2bv((t1_515[64:63]) == (t2_516[64:63]))), (XOR_1((t1_515[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_515)), t2_516)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x47be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1696bv64), RCX);

label_0x47c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1696bv64));

label_0x47ce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_194;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x47d4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x47d9:
t_523 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_195;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)), 2bv64)), (XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)), 2bv64)), (XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)))))[1:0]));
SF := t_523[64:63];
ZF := bool2bv(0bv64 == t_523);

label_0x47dc:
if (bv2bool(ZF)) {
  goto label_0x47df;
}

label_0x47de:
assume false;

label_0x47df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1696bv64));

label_0x47e7:
origDEST_527 := RAX;
origCOUNT_528 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), CF, LSHIFT_64(origDEST_527, (MINUS_64(64bv64, origCOUNT_528)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_528 == 1bv64)), origDEST_527[64:63], unconstrained_196));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), AF, unconstrained_197);

label_0x47eb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x47f2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x47f6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1696bv64));

label_0x47fe:
origDEST_533 := RCX;
origCOUNT_534 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), CF, LSHIFT_64(origDEST_533, (MINUS_64(64bv64, origCOUNT_534)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_534 == 1bv64)), origDEST_533[64:63], unconstrained_198));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), AF, unconstrained_199);

label_0x4802:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_200;
SF := unconstrained_201;
AF := unconstrained_202;
PF := unconstrained_203;

label_0x4806:
if (bv2bool(CF)) {
  goto label_0x4809;
}

label_0x4808:
assume false;

label_0x4809:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1696bv64));

label_0x4811:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1472bv64)));

label_0x4818:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x481a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4821:
t_539 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_539, 1bv32)), (XOR_32(t_539, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_539)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4823:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1436bv64), RAX[32:0]);

label_0x482a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4831:
t_543 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_543, 1bv32)), (XOR_32(t_543, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_543)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4833:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1428bv64), RAX[32:0]);

label_0x483a:
goto label_0x4677;

label_0x483f:
t_547 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))), t_547)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_547, (LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))))[1:0]));
SF := t_547[32:31];
ZF := bool2bv(0bv32 == t_547);

label_0x4847:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x484b;
}

label_0x4849:
goto label_0x4860;

label_0x484b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4852:
t_551 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_551, 1bv32)), (XOR_32(t_551, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_551)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4854:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1428bv64), RAX[32:0]);

label_0x485b:
goto label_0x4677;

label_0x4860:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4867:
t_555 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))), t_555)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_555, (LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)), 2bv32)), (XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)), 2bv32)), (XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)))))[1:0]));
SF := t_555[32:31];
ZF := bool2bv(0bv32 == t_555);

label_0x486e:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4875;
}

label_0x4870:
goto label_0x49c5;

label_0x4875:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)))));

label_0x487d:
t_559 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_559[64:0];
OF := bool2bv(t_559 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_559 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_204;
SF := unconstrained_205;
ZF := unconstrained_206;
AF := unconstrained_207;

label_0x4881:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4889:
t1_561 := RCX;
t2_562 := RAX;
RCX := PLUS_64(RCX, t2_562);
CF := bool2bv(LT_64(RCX, t1_561));
OF := AND_1((bool2bv((t1_561[64:63]) == (t2_562[64:63]))), (XOR_1((t1_561[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_561)), t2_562)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x488c:
RAX := RCX;

label_0x488f:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x4891:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1476bv64), RAX[32:0]);

label_0x4898:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)))));

label_0x48a0:
t_567 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_567[64:0];
OF := bool2bv(t_567 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_567 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_208;
SF := unconstrained_209;
ZF := unconstrained_210;
AF := unconstrained_211;

label_0x48a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x48ac:
t1_569 := RCX;
t2_570 := RAX;
RCX := PLUS_64(RCX, t2_570);
CF := bool2bv(LT_64(RCX, t1_569));
OF := AND_1((bool2bv((t1_569[64:63]) == (t2_570[64:63]))), (XOR_1((t1_569[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_569)), t2_570)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x48af:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1704bv64), RCX);

label_0x48b7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)))));

label_0x48bf:
t_575 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_575[64:0];
OF := bool2bv(t_575 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_575 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_212;
SF := unconstrained_213;
ZF := unconstrained_214;
AF := unconstrained_215;

label_0x48c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x48cb:
t1_577 := RCX;
t2_578 := RAX;
RCX := PLUS_64(RCX, t2_578);
CF := bool2bv(LT_64(RCX, t1_577));
OF := AND_1((bool2bv((t1_577[64:63]) == (t2_578[64:63]))), (XOR_1((t1_577[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_577)), t2_578)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x48ce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1712bv64), RCX);

label_0x48d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1712bv64));

label_0x48de:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_216;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x48e4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x48e9:
t_585 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_217;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))))[1:0]));
SF := t_585[64:63];
ZF := bool2bv(0bv64 == t_585);

label_0x48ec:
if (bv2bool(ZF)) {
  goto label_0x48ef;
}

label_0x48ee:
assume false;

label_0x48ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1712bv64));

label_0x48f7:
origDEST_589 := RAX;
origCOUNT_590 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, LSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), origDEST_589[64:63], unconstrained_218));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_219);

label_0x48fb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4902:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4906:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1712bv64));

label_0x490e:
origDEST_595 := RCX;
origCOUNT_596 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), CF, LSHIFT_64(origDEST_595, (MINUS_64(64bv64, origCOUNT_596)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_596 == 1bv64)), origDEST_595[64:63], unconstrained_220));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), AF, unconstrained_221);

label_0x4912:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_222;
SF := unconstrained_223;
AF := unconstrained_224;
PF := unconstrained_225;

label_0x4916:
if (bv2bool(CF)) {
  goto label_0x4919;
}

label_0x4918:
assume false;

label_0x4919:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1712bv64));

label_0x4921:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1704bv64));

label_0x4929:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x492b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x492d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)))));

label_0x4935:
t_601 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_601[64:0];
OF := bool2bv(t_601 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_601 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_226;
SF := unconstrained_227;
ZF := unconstrained_228;
AF := unconstrained_229;

label_0x4939:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4941:
t1_603 := RCX;
t2_604 := RAX;
RCX := PLUS_64(RCX, t2_604);
CF := bool2bv(LT_64(RCX, t1_603));
OF := AND_1((bool2bv((t1_603[64:63]) == (t2_604[64:63]))), (XOR_1((t1_603[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_603)), t2_604)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4944:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1720bv64), RCX);

label_0x494c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1720bv64));

label_0x4954:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_230;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x495a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x495f:
t_611 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_231;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_611, 4bv64)), t_611)), 2bv64)), (XOR_64((RSHIFT_64(t_611, 4bv64)), t_611)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_611, 4bv64)), t_611)), 2bv64)), (XOR_64((RSHIFT_64(t_611, 4bv64)), t_611)))))[1:0]));
SF := t_611[64:63];
ZF := bool2bv(0bv64 == t_611);

label_0x4962:
if (bv2bool(ZF)) {
  goto label_0x4965;
}

label_0x4964:
assume false;

label_0x4965:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1720bv64));

label_0x496d:
origDEST_615 := RAX;
origCOUNT_616 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), CF, LSHIFT_64(origDEST_615, (MINUS_64(64bv64, origCOUNT_616)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_616 == 1bv64)), origDEST_615[64:63], unconstrained_232));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), AF, unconstrained_233);

label_0x4971:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4978:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x497c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1720bv64));

label_0x4984:
origDEST_621 := RCX;
origCOUNT_622 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), CF, LSHIFT_64(origDEST_621, (MINUS_64(64bv64, origCOUNT_622)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_622 == 1bv64)), origDEST_621[64:63], unconstrained_234));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), AF, unconstrained_235);

label_0x4988:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_236;
SF := unconstrained_237;
AF := unconstrained_238;
PF := unconstrained_239;

label_0x498c:
if (bv2bool(CF)) {
  goto label_0x498f;
}

label_0x498e:
assume false;

label_0x498f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1720bv64));

label_0x4997:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1476bv64)));

label_0x499e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x49a0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x49a7:
t_627 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_627[32:31]) == (1bv32[32:31]))), (XOR_1((t_627[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_627)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x49a9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1424bv64), RAX[32:0]);

label_0x49b0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x49b7:
t_631 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_631, 1bv32)), (XOR_32(t_631, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_631)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x49b9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1428bv64), RAX[32:0]);

label_0x49c0:
goto label_0x4483;

label_0x49c5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x49cc:
t_635 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))), t_635)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_635, (LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_635, 4bv32)), t_635)), 2bv32)), (XOR_32((RSHIFT_32(t_635, 4bv32)), t_635)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_635, 4bv32)), t_635)), 2bv32)), (XOR_32((RSHIFT_32(t_635, 4bv32)), t_635)))))[1:0]));
SF := t_635[32:31];
ZF := bool2bv(0bv32 == t_635);

label_0x49d3:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x4b57;
}

label_0x49d9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x49e1:
t_639 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_639[64:0];
OF := bool2bv(t_639 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_639 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_240;
SF := unconstrained_241;
ZF := unconstrained_242;
AF := unconstrained_243;

label_0x49e5:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x49ed:
t1_641 := RCX;
t2_642 := RAX;
RCX := PLUS_64(RCX, t2_642);
CF := bool2bv(LT_64(RCX, t1_641));
OF := AND_1((bool2bv((t1_641[64:63]) == (t2_642[64:63]))), (XOR_1((t1_641[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_641)), t2_642)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x49f0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1728bv64), RCX);

label_0x49f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1728bv64));

label_0x4a00:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_244;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a06:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4a0b:
t_649 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_245;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_649, 4bv64)), t_649)), 2bv64)), (XOR_64((RSHIFT_64(t_649, 4bv64)), t_649)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_649, 4bv64)), t_649)), 2bv64)), (XOR_64((RSHIFT_64(t_649, 4bv64)), t_649)))))[1:0]));
SF := t_649[64:63];
ZF := bool2bv(0bv64 == t_649);

label_0x4a0e:
if (bv2bool(ZF)) {
  goto label_0x4a11;
}

label_0x4a10:
assume false;

label_0x4a11:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1728bv64));

label_0x4a19:
origDEST_653 := RAX;
origCOUNT_654 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), CF, LSHIFT_64(origDEST_653, (MINUS_64(64bv64, origCOUNT_654)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_654 == 1bv64)), origDEST_653[64:63], unconstrained_246));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_654 == 0bv64)), AF, unconstrained_247);

label_0x4a1d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4a24:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4a28:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1728bv64));

label_0x4a30:
origDEST_659 := RCX;
origCOUNT_660 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), CF, LSHIFT_64(origDEST_659, (MINUS_64(64bv64, origCOUNT_660)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_660 == 1bv64)), origDEST_659[64:63], unconstrained_248));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), AF, unconstrained_249);

label_0x4a34:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_250;
SF := unconstrained_251;
AF := unconstrained_252;
PF := unconstrained_253;

label_0x4a38:
if (bv2bool(CF)) {
  goto label_0x4a3b;
}

label_0x4a3a:
assume false;

label_0x4a3b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1728bv64));

label_0x4a43:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4a4a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4a4c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x4a54:
t_665 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_665[64:0];
OF := bool2bv(t_665 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_665 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_254;
SF := unconstrained_255;
ZF := unconstrained_256;
AF := unconstrained_257;

label_0x4a58:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x4a60:
t1_667 := RCX;
t2_668 := RAX;
RCX := PLUS_64(RCX, t2_668);
CF := bool2bv(LT_64(RCX, t1_667));
OF := AND_1((bool2bv((t1_667[64:63]) == (t2_668[64:63]))), (XOR_1((t1_667[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_667)), t2_668)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4a63:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1736bv64), RCX);

label_0x4a6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1736bv64));

label_0x4a73:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_258;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a79:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4a7e:
t_675 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_259;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)), 2bv64)), (XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)), 2bv64)), (XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)))))[1:0]));
SF := t_675[64:63];
ZF := bool2bv(0bv64 == t_675);

label_0x4a81:
if (bv2bool(ZF)) {
  goto label_0x4a84;
}

label_0x4a83:
assume false;

label_0x4a84:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1736bv64));

label_0x4a8c:
origDEST_679 := RAX;
origCOUNT_680 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), CF, LSHIFT_64(origDEST_679, (MINUS_64(64bv64, origCOUNT_680)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_680 == 1bv64)), origDEST_679[64:63], unconstrained_260));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), AF, unconstrained_261);

label_0x4a90:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4a97:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4a9b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1736bv64));

label_0x4aa3:
origDEST_685 := RCX;
origCOUNT_686 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), CF, LSHIFT_64(origDEST_685, (MINUS_64(64bv64, origCOUNT_686)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_686 == 1bv64)), origDEST_685[64:63], unconstrained_262));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), AF, unconstrained_263);

label_0x4aa7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_264;
SF := unconstrained_265;
AF := unconstrained_266;
PF := unconstrained_267;

label_0x4aab:
if (bv2bool(CF)) {
  goto label_0x4aae;
}

label_0x4aad:
assume false;

label_0x4aae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1736bv64));

label_0x4ab6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x4abd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4abf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x4ac6:
t_691 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_691[32:31]) == (1bv32[32:31]))), (XOR_1((t_691[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_691)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4ac8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1744bv64), RAX[32:0]);

label_0x4acf:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x4ad7:
t_695 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_695[64:0];
OF := bool2bv(t_695 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_695 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_268;
SF := unconstrained_269;
ZF := unconstrained_270;
AF := unconstrained_271;

label_0x4adb:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x4ae3:
t1_697 := RCX;
t2_698 := RAX;
RCX := PLUS_64(RCX, t2_698);
CF := bool2bv(LT_64(RCX, t1_697));
OF := AND_1((bool2bv((t1_697[64:63]) == (t2_698[64:63]))), (XOR_1((t1_697[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_697)), t2_698)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4ae6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1752bv64), RCX);

label_0x4aee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1752bv64));

label_0x4af6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_272;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4afc:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4b01:
t_705 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_273;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_705, 4bv64)), t_705)), 2bv64)), (XOR_64((RSHIFT_64(t_705, 4bv64)), t_705)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_705, 4bv64)), t_705)), 2bv64)), (XOR_64((RSHIFT_64(t_705, 4bv64)), t_705)))))[1:0]));
SF := t_705[64:63];
ZF := bool2bv(0bv64 == t_705);

label_0x4b04:
if (bv2bool(ZF)) {
  goto label_0x4b07;
}

label_0x4b06:
assume false;

label_0x4b07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1752bv64));

label_0x4b0f:
origDEST_709 := RAX;
origCOUNT_710 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), CF, LSHIFT_64(origDEST_709, (MINUS_64(64bv64, origCOUNT_710)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_710 == 1bv64)), origDEST_709[64:63], unconstrained_274));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_710 == 0bv64)), AF, unconstrained_275);

label_0x4b13:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4b1a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4b1e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1752bv64));

label_0x4b26:
origDEST_715 := RCX;
origCOUNT_716 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), CF, LSHIFT_64(origDEST_715, (MINUS_64(64bv64, origCOUNT_716)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_716 == 1bv64)), origDEST_715[64:63], unconstrained_276));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), AF, unconstrained_277);

label_0x4b2a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_278;
SF := unconstrained_279;
AF := unconstrained_280;
PF := unconstrained_281;

label_0x4b2e:
if (bv2bool(CF)) {
  goto label_0x4b31;
}

label_0x4b30:
assume false;

label_0x4b31:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1752bv64));

label_0x4b39:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1744bv64)));

label_0x4b40:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4b42:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x4b49:
t_721 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_721[32:31]) == (1bv32[32:31]))), (XOR_1((t_721[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_721)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4b4b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x4b52:
goto label_0x4241;

label_0x4b57:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4b5e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4b65:
t_725 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_725, (RAX[32:0])));
OF := AND_32((XOR_32(t_725, (RAX[32:0]))), (XOR_32(t_725, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_725)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4b67:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4b69:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4b70:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4b77:
t_729 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_729, (RCX[32:0])));
OF := AND_32((XOR_32(t_729, (RCX[32:0]))), (XOR_32(t_729, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_729)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x4b79:
RCX := (0bv32 ++ RDX[32:0]);

label_0x4b7b:
t_733 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_733)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_733, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_733, 4bv32)), t_733)), 2bv32)), (XOR_32((RSHIFT_32(t_733, 4bv32)), t_733)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_733, 4bv32)), t_733)), 2bv32)), (XOR_32((RSHIFT_32(t_733, 4bv32)), t_733)))))[1:0]));
SF := t_733[32:31];
ZF := bool2bv(0bv32 == t_733);

label_0x4b7d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x4b9a;
}

label_0x4b7f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4b86:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4b8d:
t_737 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_737, (RAX[32:0])));
OF := AND_32((XOR_32(t_737, (RAX[32:0]))), (XOR_32(t_737, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_737)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4b8f:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4b91:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1760bv64), RAX[32:0]);

label_0x4b98:
goto label_0x4bb3;

label_0x4b9a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)));

label_0x4ba1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4ba8:
t_741 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_741, (RAX[32:0])));
OF := AND_32((XOR_32(t_741, (RAX[32:0]))), (XOR_32(t_741, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_741)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4baa:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4bac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1760bv64), RAX[32:0]);

label_0x4bb3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1760bv64)));

label_0x4bba:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1440bv64), RAX[32:0]);

label_0x4bc1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4bc8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1480bv64), RAX[32:0]);

label_0x4bcf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64)));

label_0x4bd6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4bdd:
t_745 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_745, (RAX[32:0])));
OF := AND_32((XOR_32(t_745, (RAX[32:0]))), (XOR_32(t_745, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_745)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4bdf:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4be1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1484bv64), RAX[32:0]);

label_0x4be8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64)));

label_0x4bef:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1488bv64), RAX[32:0]);

label_0x4bf6:
t_749 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64))), t_749)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_749, (LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_749, 4bv32)), t_749)), 2bv32)), (XOR_32((RSHIFT_32(t_749, 4bv32)), t_749)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_749, 4bv32)), t_749)), 2bv32)), (XOR_32((RSHIFT_32(t_749, 4bv32)), t_749)))))[1:0]));
SF := t_749[32:31];
ZF := bool2bv(0bv32 == t_749);

label_0x4bfe:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4d64;
}

label_0x4c04:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64)))));

label_0x4c0c:
t_753 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_753[64:0];
OF := bool2bv(t_753 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_753 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_282;
SF := unconstrained_283;
ZF := unconstrained_284;
AF := unconstrained_285;

label_0x4c10:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4c18:
t1_755 := RCX;
t2_756 := RAX;
RCX := PLUS_64(RCX, t2_756);
CF := bool2bv(LT_64(RCX, t1_755));
OF := AND_1((bool2bv((t1_755[64:63]) == (t2_756[64:63]))), (XOR_1((t1_755[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_755)), t2_756)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4c1b:
RAX := RCX;

label_0x4c1e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x4c20:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1492bv64), RAX[32:0]);

label_0x4c27:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64)))));

label_0x4c2f:
t_761 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_761[64:0];
OF := bool2bv(t_761 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_761 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_286;
SF := unconstrained_287;
ZF := unconstrained_288;
AF := unconstrained_289;

label_0x4c33:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4c3b:
t1_763 := RCX;
t2_764 := RAX;
RCX := PLUS_64(RCX, t2_764);
CF := bool2bv(LT_64(RCX, t1_763));
OF := AND_1((bool2bv((t1_763[64:63]) == (t2_764[64:63]))), (XOR_1((t1_763[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_763)), t2_764)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4c3e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1768bv64), RCX);

label_0x4c46:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64)))));

label_0x4c4e:
t_769 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_769[64:0];
OF := bool2bv(t_769 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_769 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_290;
SF := unconstrained_291;
ZF := unconstrained_292;
AF := unconstrained_293;

label_0x4c52:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4c5a:
t1_771 := RCX;
t2_772 := RAX;
RCX := PLUS_64(RCX, t2_772);
CF := bool2bv(LT_64(RCX, t1_771));
OF := AND_1((bool2bv((t1_771[64:63]) == (t2_772[64:63]))), (XOR_1((t1_771[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_771)), t2_772)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4c5d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1776bv64), RCX);

label_0x4c65:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1776bv64));

label_0x4c6d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_294;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c73:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4c78:
t_779 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_295;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_779, 4bv64)), t_779)), 2bv64)), (XOR_64((RSHIFT_64(t_779, 4bv64)), t_779)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_779, 4bv64)), t_779)), 2bv64)), (XOR_64((RSHIFT_64(t_779, 4bv64)), t_779)))))[1:0]));
SF := t_779[64:63];
ZF := bool2bv(0bv64 == t_779);

label_0x4c7b:
if (bv2bool(ZF)) {
  goto label_0x4c7e;
}

label_0x4c7d:
assume false;

label_0x4c7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1776bv64));

label_0x4c86:
origDEST_783 := RAX;
origCOUNT_784 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), CF, LSHIFT_64(origDEST_783, (MINUS_64(64bv64, origCOUNT_784)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_784 == 1bv64)), origDEST_783[64:63], unconstrained_296));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_784 == 0bv64)), AF, unconstrained_297);

label_0x4c8a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4c91:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4c95:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1776bv64));

label_0x4c9d:
origDEST_789 := RCX;
origCOUNT_790 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), CF, LSHIFT_64(origDEST_789, (MINUS_64(64bv64, origCOUNT_790)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_790 == 1bv64)), origDEST_789[64:63], unconstrained_298));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), AF, unconstrained_299);

label_0x4ca1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_300;
SF := unconstrained_301;
AF := unconstrained_302;
PF := unconstrained_303;

label_0x4ca5:
if (bv2bool(CF)) {
  goto label_0x4ca8;
}

label_0x4ca7:
assume false;

label_0x4ca8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1776bv64));

label_0x4cb0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1768bv64));

label_0x4cb8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x4cba:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4cbc:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64)))));

label_0x4cc4:
t_795 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_795[64:0];
OF := bool2bv(t_795 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_795 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_304;
SF := unconstrained_305;
ZF := unconstrained_306;
AF := unconstrained_307;

label_0x4cc8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4cd0:
t1_797 := RCX;
t2_798 := RAX;
RCX := PLUS_64(RCX, t2_798);
CF := bool2bv(LT_64(RCX, t1_797));
OF := AND_1((bool2bv((t1_797[64:63]) == (t2_798[64:63]))), (XOR_1((t1_797[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_797)), t2_798)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4cd3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1784bv64), RCX);

label_0x4cdb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1784bv64));

label_0x4ce3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_308;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ce9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4cee:
t_805 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_309;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_805, 4bv64)), t_805)), 2bv64)), (XOR_64((RSHIFT_64(t_805, 4bv64)), t_805)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_805, 4bv64)), t_805)), 2bv64)), (XOR_64((RSHIFT_64(t_805, 4bv64)), t_805)))))[1:0]));
SF := t_805[64:63];
ZF := bool2bv(0bv64 == t_805);

label_0x4cf1:
if (bv2bool(ZF)) {
  goto label_0x4cf4;
}

label_0x4cf3:
assume false;

label_0x4cf4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1784bv64));

label_0x4cfc:
origDEST_809 := RAX;
origCOUNT_810 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), CF, LSHIFT_64(origDEST_809, (MINUS_64(64bv64, origCOUNT_810)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_810 == 1bv64)), origDEST_809[64:63], unconstrained_310));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_810 == 0bv64)), AF, unconstrained_311);

label_0x4d00:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4d07:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4d0b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1784bv64));

label_0x4d13:
origDEST_815 := RCX;
origCOUNT_816 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), CF, LSHIFT_64(origDEST_815, (MINUS_64(64bv64, origCOUNT_816)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_816 == 1bv64)), origDEST_815[64:63], unconstrained_312));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_816 == 0bv64)), AF, unconstrained_313);

label_0x4d17:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_314;
SF := unconstrained_315;
AF := unconstrained_316;
PF := unconstrained_317;

label_0x4d1b:
if (bv2bool(CF)) {
  goto label_0x4d1e;
}

label_0x4d1d:
assume false;

label_0x4d1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1784bv64));

label_0x4d26:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1492bv64)));

label_0x4d2d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4d2f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1480bv64)));

label_0x4d36:
t_821 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_821[32:31]) == (1bv32[32:31]))), (XOR_1((t_821[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_821)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4d38:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1480bv64), RAX[32:0]);

label_0x4d3f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1484bv64)));

label_0x4d46:
t_825 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_825[32:31]) == (1bv32[32:31]))), (XOR_1((t_825[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_825)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4d48:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1484bv64), RAX[32:0]);

label_0x4d4f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1488bv64)));

label_0x4d56:
t_829 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_829, 1bv32)), (XOR_32(t_829, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_829)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4d58:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1488bv64), RAX[32:0]);

label_0x4d5f:
goto label_0x4bf6;

label_0x4d64:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4d6b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x4d72:
t_833 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_833, (RAX[32:0])));
OF := AND_32((XOR_32(t_833, (RAX[32:0]))), (XOR_32(t_833, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_833)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4d74:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4d76:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4d7d:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4d84:
t_837 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_837, (RCX[32:0])));
OF := AND_32((XOR_32(t_837, (RCX[32:0]))), (XOR_32(t_837, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_837)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x4d86:
RCX := (0bv32 ++ RDX[32:0]);

label_0x4d88:
t_841 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_841)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_841, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_841, 4bv32)), t_841)), 2bv32)), (XOR_32((RSHIFT_32(t_841, 4bv32)), t_841)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_841, 4bv32)), t_841)), 2bv32)), (XOR_32((RSHIFT_32(t_841, 4bv32)), t_841)))))[1:0]));
SF := t_841[32:31];
ZF := bool2bv(0bv32 == t_841);

label_0x4d8a:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x4da7;
}

label_0x4d8c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4d93:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x4d9a:
t_845 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_845, (RAX[32:0])));
OF := AND_32((XOR_32(t_845, (RAX[32:0]))), (XOR_32(t_845, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_845)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4d9c:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4d9e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1792bv64), RAX[32:0]);

label_0x4da5:
goto label_0x4dc0;

label_0x4da7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4dae:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4db5:
t_849 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_849, (RAX[32:0])));
OF := AND_32((XOR_32(t_849, (RAX[32:0]))), (XOR_32(t_849, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_849)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4db7:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4db9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1792bv64), RAX[32:0]);

label_0x4dc0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1792bv64)));

label_0x4dc7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1444bv64), RAX[32:0]);

label_0x4dce:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4dd5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1496bv64), RAX[32:0]);

label_0x4ddc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1444bv64)));

label_0x4de3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x4dea:
t_853 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_853, (RAX[32:0])));
OF := AND_32((XOR_32(t_853, (RAX[32:0]))), (XOR_32(t_853, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_853)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4dec:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4dee:
t_857 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_857[32:31]) == (1bv32[32:31]))), (XOR_1((t_857[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_857)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4df0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1500bv64), RAX[32:0]);

label_0x4df7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1444bv64)));

label_0x4dfe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1504bv64), RAX[32:0]);

label_0x4e05:
t_861 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64))), t_861)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_861, (LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_861, 4bv32)), t_861)), 2bv32)), (XOR_32((RSHIFT_32(t_861, 4bv32)), t_861)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_861, 4bv32)), t_861)), 2bv32)), (XOR_32((RSHIFT_32(t_861, 4bv32)), t_861)))))[1:0]));
SF := t_861[32:31];
ZF := bool2bv(0bv32 == t_861);

label_0x4e0d:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4f73;
}

label_0x4e13:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64)))));

label_0x4e1b:
t_865 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_865[64:0];
OF := bool2bv(t_865 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_865 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_318;
SF := unconstrained_319;
ZF := unconstrained_320;
AF := unconstrained_321;

label_0x4e1f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4e27:
t1_867 := RCX;
t2_868 := RAX;
RCX := PLUS_64(RCX, t2_868);
CF := bool2bv(LT_64(RCX, t1_867));
OF := AND_1((bool2bv((t1_867[64:63]) == (t2_868[64:63]))), (XOR_1((t1_867[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_867)), t2_868)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4e2a:
RAX := RCX;

label_0x4e2d:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x4e2f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1508bv64), RAX[32:0]);

label_0x4e36:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64)))));

label_0x4e3e:
t_873 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_873[64:0];
OF := bool2bv(t_873 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_873 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_322;
SF := unconstrained_323;
ZF := unconstrained_324;
AF := unconstrained_325;

label_0x4e42:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4e4a:
t1_875 := RCX;
t2_876 := RAX;
RCX := PLUS_64(RCX, t2_876);
CF := bool2bv(LT_64(RCX, t1_875));
OF := AND_1((bool2bv((t1_875[64:63]) == (t2_876[64:63]))), (XOR_1((t1_875[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_875)), t2_876)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4e4d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1800bv64), RCX);

label_0x4e55:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64)))));

label_0x4e5d:
t_881 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_881[64:0];
OF := bool2bv(t_881 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_881 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_326;
SF := unconstrained_327;
ZF := unconstrained_328;
AF := unconstrained_329;

label_0x4e61:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4e69:
t1_883 := RCX;
t2_884 := RAX;
RCX := PLUS_64(RCX, t2_884);
CF := bool2bv(LT_64(RCX, t1_883));
OF := AND_1((bool2bv((t1_883[64:63]) == (t2_884[64:63]))), (XOR_1((t1_883[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_883)), t2_884)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4e6c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1808bv64), RCX);

label_0x4e74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1808bv64));

label_0x4e7c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_330;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e82:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4e87:
t_891 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_331;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_891, 4bv64)), t_891)), 2bv64)), (XOR_64((RSHIFT_64(t_891, 4bv64)), t_891)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_891, 4bv64)), t_891)), 2bv64)), (XOR_64((RSHIFT_64(t_891, 4bv64)), t_891)))))[1:0]));
SF := t_891[64:63];
ZF := bool2bv(0bv64 == t_891);

label_0x4e8a:
if (bv2bool(ZF)) {
  goto label_0x4e8d;
}

label_0x4e8c:
assume false;

label_0x4e8d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1808bv64));

label_0x4e95:
origDEST_895 := RAX;
origCOUNT_896 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), CF, LSHIFT_64(origDEST_895, (MINUS_64(64bv64, origCOUNT_896)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_896 == 1bv64)), origDEST_895[64:63], unconstrained_332));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_896 == 0bv64)), AF, unconstrained_333);

label_0x4e99:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4ea0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ea4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1808bv64));

label_0x4eac:
origDEST_901 := RCX;
origCOUNT_902 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), CF, LSHIFT_64(origDEST_901, (MINUS_64(64bv64, origCOUNT_902)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_902 == 1bv64)), origDEST_901[64:63], unconstrained_334));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_902 == 0bv64)), AF, unconstrained_335);

label_0x4eb0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_336;
SF := unconstrained_337;
AF := unconstrained_338;
PF := unconstrained_339;

label_0x4eb4:
if (bv2bool(CF)) {
  goto label_0x4eb7;
}

label_0x4eb6:
assume false;

label_0x4eb7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1808bv64));

label_0x4ebf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1800bv64));

label_0x4ec7:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x4ec9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4ecb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64)))));

label_0x4ed3:
t_907 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_907[64:0];
OF := bool2bv(t_907 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_907 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_340;
SF := unconstrained_341;
ZF := unconstrained_342;
AF := unconstrained_343;

label_0x4ed7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2320bv64));

label_0x4edf:
t1_909 := RCX;
t2_910 := RAX;
RCX := PLUS_64(RCX, t2_910);
CF := bool2bv(LT_64(RCX, t1_909));
OF := AND_1((bool2bv((t1_909[64:63]) == (t2_910[64:63]))), (XOR_1((t1_909[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_909)), t2_910)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4ee2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1816bv64), RCX);

label_0x4eea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1816bv64));

label_0x4ef2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_344;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ef8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4efd:
t_917 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_345;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_917, 4bv64)), t_917)), 2bv64)), (XOR_64((RSHIFT_64(t_917, 4bv64)), t_917)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_917, 4bv64)), t_917)), 2bv64)), (XOR_64((RSHIFT_64(t_917, 4bv64)), t_917)))))[1:0]));
SF := t_917[64:63];
ZF := bool2bv(0bv64 == t_917);

label_0x4f00:
if (bv2bool(ZF)) {
  goto label_0x4f03;
}

label_0x4f02:
assume false;

label_0x4f03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1816bv64));

label_0x4f0b:
origDEST_921 := RAX;
origCOUNT_922 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), CF, LSHIFT_64(origDEST_921, (MINUS_64(64bv64, origCOUNT_922)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_922 == 1bv64)), origDEST_921[64:63], unconstrained_346));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_922 == 0bv64)), AF, unconstrained_347);

label_0x4f0f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4f16:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4f1a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1816bv64));

label_0x4f22:
origDEST_927 := RCX;
origCOUNT_928 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), CF, LSHIFT_64(origDEST_927, (MINUS_64(64bv64, origCOUNT_928)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_928 == 1bv64)), origDEST_927[64:63], unconstrained_348));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_928 == 0bv64)), AF, unconstrained_349);

label_0x4f26:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_350;
SF := unconstrained_351;
AF := unconstrained_352;
PF := unconstrained_353;

label_0x4f2a:
if (bv2bool(CF)) {
  goto label_0x4f2d;
}

label_0x4f2c:
assume false;

label_0x4f2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1816bv64));

label_0x4f35:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1508bv64)));

label_0x4f3c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4f3e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1496bv64)));

label_0x4f45:
t_933 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_933[32:31]) == (1bv32[32:31]))), (XOR_1((t_933[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_933)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4f47:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1496bv64), RAX[32:0]);

label_0x4f4e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1500bv64)));

label_0x4f55:
t_937 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_937[32:31]) == (1bv32[32:31]))), (XOR_1((t_937[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_937)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4f57:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1500bv64), RAX[32:0]);

label_0x4f5e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1504bv64)));

label_0x4f65:
t_941 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_941, 1bv32)), (XOR_32(t_941, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_941)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4f67:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1504bv64), RAX[32:0]);

label_0x4f6e:
goto label_0x4e05;

label_0x4f73:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1424bv64)));

label_0x4f7a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x4f81:
t1_945 := RCX[32:0];
t2_946 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_946));
CF := bool2bv(LT_32((RCX[32:0]), t1_945));
OF := AND_1((bool2bv((t1_945[32:31]) == (t2_946[32:31]))), (XOR_1((t1_945[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_945)), t2_946)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4f83:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4f85:
t_951 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)))));
CF := bool2bv(LT_32(t_951, (LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64)))));
OF := AND_32((XOR_32(t_951, (LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))))), (XOR_32(t_951, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_951)), (LOAD_LE_32(mem, PLUS_64(RSP, 1432bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4f8c:
t_955 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_955, 1bv32)), (XOR_32(t_955, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_955)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4f8e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1440bv64), RAX[32:0]);

label_0x4f95:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1428bv64)));

label_0x4f9c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1436bv64)));

label_0x4fa3:
t_959 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_959, (RAX[32:0])));
OF := AND_32((XOR_32(t_959, (RAX[32:0]))), (XOR_32(t_959, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_959)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4fa5:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4fa7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x4fae:
t_963 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_963, (RAX[32:0])));
OF := AND_32((XOR_32(t_963, (RAX[32:0]))), (XOR_32(t_963, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_963)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4fb0:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4fb2:
t_967 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_967[32:31]) == (1bv32[32:31]))), (XOR_1((t_967[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_967)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4fb4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1444bv64), RAX[32:0]);

label_0x4fbb:
RAX := (0bv32 ++ 4bv32);

label_0x4fc0:
t_971 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_971[64:0];
OF := bool2bv(t_971 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_971 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_354;
SF := unconstrained_355;
ZF := unconstrained_356;
AF := unconstrained_357;

label_0x4fc4:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x4fcc:
t1_973 := RCX;
t2_974 := RAX;
RCX := PLUS_64(RCX, t2_974);
CF := bool2bv(LT_64(RCX, t1_973));
OF := AND_1((bool2bv((t1_973[64:63]) == (t2_974[64:63]))), (XOR_1((t1_973[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_973)), t2_974)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4fcf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1824bv64), RCX);

label_0x4fd7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1824bv64));

label_0x4fdf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_358;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4fe5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4fea:
t_981 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_359;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_981, 4bv64)), t_981)), 2bv64)), (XOR_64((RSHIFT_64(t_981, 4bv64)), t_981)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_981, 4bv64)), t_981)), 2bv64)), (XOR_64((RSHIFT_64(t_981, 4bv64)), t_981)))))[1:0]));
SF := t_981[64:63];
ZF := bool2bv(0bv64 == t_981);

label_0x4fed:
if (bv2bool(ZF)) {
  goto label_0x4ff0;
}

label_0x4fef:
assume false;

label_0x4ff0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1824bv64));

label_0x4ff8:
origDEST_985 := RAX;
origCOUNT_986 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), CF, LSHIFT_64(origDEST_985, (MINUS_64(64bv64, origCOUNT_986)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_986 == 1bv64)), origDEST_985[64:63], unconstrained_360));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_986 == 0bv64)), AF, unconstrained_361);

label_0x4ffc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5003:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5007:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1824bv64));

label_0x500f:
origDEST_991 := RCX;
origCOUNT_992 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), CF, LSHIFT_64(origDEST_991, (MINUS_64(64bv64, origCOUNT_992)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_992 == 1bv64)), origDEST_991[64:63], unconstrained_362));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_992 == 0bv64)), AF, unconstrained_363);

label_0x5013:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_364;
SF := unconstrained_365;
AF := unconstrained_366;
PF := unconstrained_367;

label_0x5017:
if (bv2bool(CF)) {
  goto label_0x501a;
}

label_0x5019:
assume false;

label_0x501a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1824bv64));

label_0x5022:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1456bv64)));

label_0x5029:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x502b:
RAX := (0bv32 ++ 4bv32);

label_0x5030:
t_997 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_997[64:0];
OF := bool2bv(t_997 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_997 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_368;
SF := unconstrained_369;
ZF := unconstrained_370;
AF := unconstrained_371;

label_0x5034:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5039:
t1_999 := RCX;
t2_1000 := RAX;
RCX := PLUS_64(RCX, t2_1000);
CF := bool2bv(LT_64(RCX, t1_999));
OF := AND_1((bool2bv((t1_999[64:63]) == (t2_1000[64:63]))), (XOR_1((t1_999[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_999)), t2_1000)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x503c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1832bv64), RCX);

label_0x5044:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1832bv64));

label_0x504c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_372;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5052:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5057:
t_1007 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_373;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1007, 4bv64)), t_1007)), 2bv64)), (XOR_64((RSHIFT_64(t_1007, 4bv64)), t_1007)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1007, 4bv64)), t_1007)), 2bv64)), (XOR_64((RSHIFT_64(t_1007, 4bv64)), t_1007)))))[1:0]));
SF := t_1007[64:63];
ZF := bool2bv(0bv64 == t_1007);

label_0x505a:
if (bv2bool(ZF)) {
  goto label_0x505d;
}

label_0x505c:
assume false;

label_0x505d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1832bv64));

label_0x5065:
origDEST_1011 := RAX;
origCOUNT_1012 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), CF, LSHIFT_64(origDEST_1011, (MINUS_64(64bv64, origCOUNT_1012)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 1bv64)), origDEST_1011[64:63], unconstrained_374));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1012 == 0bv64)), AF, unconstrained_375);

label_0x5069:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5070:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5074:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1832bv64));

label_0x507c:
origDEST_1017 := RCX;
origCOUNT_1018 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), CF, LSHIFT_64(origDEST_1017, (MINUS_64(64bv64, origCOUNT_1018)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 1bv64)), origDEST_1017[64:63], unconstrained_376));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1018 == 0bv64)), AF, unconstrained_377);

label_0x5080:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_378;
SF := unconstrained_379;
AF := unconstrained_380;
PF := unconstrained_381;

label_0x5084:
if (bv2bool(CF)) {
  goto label_0x5087;
}

label_0x5086:
assume false;

label_0x5087:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1832bv64));

label_0x508f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64)));

label_0x5096:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5098:
RAX := (0bv32 ++ 4bv32);

label_0x509d:
t_1023 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1023[64:0];
OF := bool2bv(t_1023 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1023 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_382;
SF := unconstrained_383;
ZF := unconstrained_384;
AF := unconstrained_385;

label_0x50a1:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x50a6:
t1_1025 := RCX;
t2_1026 := RAX;
RCX := PLUS_64(RCX, t2_1026);
CF := bool2bv(LT_64(RCX, t1_1025));
OF := AND_1((bool2bv((t1_1025[64:63]) == (t2_1026[64:63]))), (XOR_1((t1_1025[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1025)), t2_1026)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x50a9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1840bv64), RCX);

label_0x50b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1840bv64));

label_0x50b9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_386;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x50bf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x50c4:
t_1033 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_387;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1033, 4bv64)), t_1033)), 2bv64)), (XOR_64((RSHIFT_64(t_1033, 4bv64)), t_1033)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1033, 4bv64)), t_1033)), 2bv64)), (XOR_64((RSHIFT_64(t_1033, 4bv64)), t_1033)))))[1:0]));
SF := t_1033[64:63];
ZF := bool2bv(0bv64 == t_1033);

label_0x50c7:
if (bv2bool(ZF)) {
  goto label_0x50ca;
}

label_0x50c9:
assume false;

label_0x50ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1840bv64));

label_0x50d2:
origDEST_1037 := RAX;
origCOUNT_1038 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), CF, LSHIFT_64(origDEST_1037, (MINUS_64(64bv64, origCOUNT_1038)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 1bv64)), origDEST_1037[64:63], unconstrained_388));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), AF, unconstrained_389);

label_0x50d6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x50dd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x50e1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1840bv64));

label_0x50e9:
origDEST_1043 := RCX;
origCOUNT_1044 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), CF, LSHIFT_64(origDEST_1043, (MINUS_64(64bv64, origCOUNT_1044)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 1bv64)), origDEST_1043[64:63], unconstrained_390));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1044 == 0bv64)), AF, unconstrained_391);

label_0x50ed:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_392;
SF := unconstrained_393;
AF := unconstrained_394;
PF := unconstrained_395;

label_0x50f1:
if (bv2bool(CF)) {
  goto label_0x50f4;
}

label_0x50f3:
assume false;

label_0x50f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1840bv64));

label_0x50fc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x5103:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5105:
RAX := (0bv32 ++ 4bv32);

label_0x510a:
t_1049 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1049[64:0];
OF := bool2bv(t_1049 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1049 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_396;
SF := unconstrained_397;
ZF := unconstrained_398;
AF := unconstrained_399;

label_0x510e:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5116:
t1_1051 := RCX;
t2_1052 := RAX;
RCX := PLUS_64(RCX, t2_1052);
CF := bool2bv(LT_64(RCX, t1_1051));
OF := AND_1((bool2bv((t1_1051[64:63]) == (t2_1052[64:63]))), (XOR_1((t1_1051[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1051)), t2_1052)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5119:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1848bv64), RCX);

label_0x5121:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1848bv64));

label_0x5129:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_400;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x512f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5134:
t_1059 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_401;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1059, 4bv64)), t_1059)), 2bv64)), (XOR_64((RSHIFT_64(t_1059, 4bv64)), t_1059)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1059, 4bv64)), t_1059)), 2bv64)), (XOR_64((RSHIFT_64(t_1059, 4bv64)), t_1059)))))[1:0]));
SF := t_1059[64:63];
ZF := bool2bv(0bv64 == t_1059);

label_0x5137:
if (bv2bool(ZF)) {
  goto label_0x513a;
}

label_0x5139:
assume false;

label_0x513a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1848bv64));

label_0x5142:
origDEST_1063 := RAX;
origCOUNT_1064 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), CF, LSHIFT_64(origDEST_1063, (MINUS_64(64bv64, origCOUNT_1064)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 1bv64)), origDEST_1063[64:63], unconstrained_402));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1064 == 0bv64)), AF, unconstrained_403);

label_0x5146:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x514d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5151:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1848bv64));

label_0x5159:
origDEST_1069 := RCX;
origCOUNT_1070 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), CF, LSHIFT_64(origDEST_1069, (MINUS_64(64bv64, origCOUNT_1070)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 1bv64)), origDEST_1069[64:63], unconstrained_404));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1070 == 0bv64)), AF, unconstrained_405);

label_0x515d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_406;
SF := unconstrained_407;
AF := unconstrained_408;
PF := unconstrained_409;

label_0x5161:
if (bv2bool(CF)) {
  goto label_0x5164;
}

label_0x5163:
assume false;

label_0x5164:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1848bv64));

label_0x516c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1444bv64)));

label_0x5173:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5175:
RAX := (0bv32 ++ 4bv32);

label_0x517a:
t_1075 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1075[64:0];
OF := bool2bv(t_1075 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1075 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_410;
SF := unconstrained_411;
ZF := unconstrained_412;
AF := unconstrained_413;

label_0x517e:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5183:
t1_1077 := RCX;
t2_1078 := RAX;
RCX := PLUS_64(RCX, t2_1078);
CF := bool2bv(LT_64(RCX, t1_1077));
OF := AND_1((bool2bv((t1_1077[64:63]) == (t2_1078[64:63]))), (XOR_1((t1_1077[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1077)), t2_1078)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5186:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1856bv64), RCX);

label_0x518e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1856bv64));

label_0x5196:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_414;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x519c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x51a1:
t_1085 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_415;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)), 2bv64)), (XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)), 2bv64)), (XOR_64((RSHIFT_64(t_1085, 4bv64)), t_1085)))))[1:0]));
SF := t_1085[64:63];
ZF := bool2bv(0bv64 == t_1085);

label_0x51a4:
if (bv2bool(ZF)) {
  goto label_0x51a7;
}

label_0x51a6:
assume false;

label_0x51a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1856bv64));

label_0x51af:
origDEST_1089 := RAX;
origCOUNT_1090 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), CF, LSHIFT_64(origDEST_1089, (MINUS_64(64bv64, origCOUNT_1090)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 1bv64)), origDEST_1089[64:63], unconstrained_416));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1090 == 0bv64)), AF, unconstrained_417);

label_0x51b3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x51ba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x51be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1856bv64));

label_0x51c6:
origDEST_1095 := RCX;
origCOUNT_1096 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), CF, LSHIFT_64(origDEST_1095, (MINUS_64(64bv64, origCOUNT_1096)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 1bv64)), origDEST_1095[64:63], unconstrained_418));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1096 == 0bv64)), AF, unconstrained_419);

label_0x51ca:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_420;
SF := unconstrained_421;
AF := unconstrained_422;
PF := unconstrained_423;

label_0x51ce:
if (bv2bool(CF)) {
  goto label_0x51d1;
}

label_0x51d0:
assume false;

label_0x51d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1856bv64));

label_0x51d9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1460bv64)));

label_0x51e0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x51e2:
RAX := (0bv32 ++ 4bv32);

label_0x51e7:
t_1101 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1101[64:0];
OF := bool2bv(t_1101 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1101 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_424;
SF := unconstrained_425;
ZF := unconstrained_426;
AF := unconstrained_427;

label_0x51eb:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x51f0:
t1_1103 := RCX;
t2_1104 := RAX;
RCX := PLUS_64(RCX, t2_1104);
CF := bool2bv(LT_64(RCX, t1_1103));
OF := AND_1((bool2bv((t1_1103[64:63]) == (t2_1104[64:63]))), (XOR_1((t1_1103[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1103)), t2_1104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x51f3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1864bv64), RCX);

label_0x51fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1864bv64));

label_0x5203:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_428;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5209:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x520e:
t_1111 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_429;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1111, 4bv64)), t_1111)), 2bv64)), (XOR_64((RSHIFT_64(t_1111, 4bv64)), t_1111)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1111, 4bv64)), t_1111)), 2bv64)), (XOR_64((RSHIFT_64(t_1111, 4bv64)), t_1111)))))[1:0]));
SF := t_1111[64:63];
ZF := bool2bv(0bv64 == t_1111);

label_0x5211:
if (bv2bool(ZF)) {
  goto label_0x5214;
}

label_0x5213:
assume false;

label_0x5214:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1864bv64));

label_0x521c:
origDEST_1115 := RAX;
origCOUNT_1116 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), CF, LSHIFT_64(origDEST_1115, (MINUS_64(64bv64, origCOUNT_1116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 1bv64)), origDEST_1115[64:63], unconstrained_430));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), AF, unconstrained_431);

label_0x5220:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5227:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x522b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1864bv64));

label_0x5233:
origDEST_1121 := RCX;
origCOUNT_1122 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), CF, LSHIFT_64(origDEST_1121, (MINUS_64(64bv64, origCOUNT_1122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 1bv64)), origDEST_1121[64:63], unconstrained_432));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1122 == 0bv64)), AF, unconstrained_433);

label_0x5237:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_434;
SF := unconstrained_435;
AF := unconstrained_436;
PF := unconstrained_437;

label_0x523b:
if (bv2bool(CF)) {
  goto label_0x523e;
}

label_0x523d:
assume false;

label_0x523e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1864bv64));

label_0x5246:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x524d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x524f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1440bv64)));

label_0x5256:
t_1127 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1127[32:31]) == (1bv32[32:31]))), (XOR_1((t_1127[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1127)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5258:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1872bv64), RAX[32:0]);

label_0x525f:
RAX := (0bv32 ++ 4bv32);

label_0x5264:
t_1131 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1131[64:0];
OF := bool2bv(t_1131 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1131 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_438;
SF := unconstrained_439;
ZF := unconstrained_440;
AF := unconstrained_441;

label_0x5268:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5270:
t1_1133 := RCX;
t2_1134 := RAX;
RCX := PLUS_64(RCX, t2_1134);
CF := bool2bv(LT_64(RCX, t1_1133));
OF := AND_1((bool2bv((t1_1133[64:63]) == (t2_1134[64:63]))), (XOR_1((t1_1133[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1133)), t2_1134)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5273:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1880bv64), RCX);

label_0x527b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1880bv64));

label_0x5283:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_442;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5289:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x528e:
t_1141 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_443;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1141, 4bv64)), t_1141)), 2bv64)), (XOR_64((RSHIFT_64(t_1141, 4bv64)), t_1141)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1141, 4bv64)), t_1141)), 2bv64)), (XOR_64((RSHIFT_64(t_1141, 4bv64)), t_1141)))))[1:0]));
SF := t_1141[64:63];
ZF := bool2bv(0bv64 == t_1141);

label_0x5291:
if (bv2bool(ZF)) {
  goto label_0x5294;
}

label_0x5293:
assume false;

label_0x5294:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1880bv64));

label_0x529c:
origDEST_1145 := RAX;
origCOUNT_1146 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), CF, LSHIFT_64(origDEST_1145, (MINUS_64(64bv64, origCOUNT_1146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 1bv64)), origDEST_1145[64:63], unconstrained_444));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1146 == 0bv64)), AF, unconstrained_445);

label_0x52a0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x52a7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x52ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1880bv64));

label_0x52b3:
origDEST_1151 := RCX;
origCOUNT_1152 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), CF, LSHIFT_64(origDEST_1151, (MINUS_64(64bv64, origCOUNT_1152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 1bv64)), origDEST_1151[64:63], unconstrained_446));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1152 == 0bv64)), AF, unconstrained_447);

label_0x52b7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_448;
SF := unconstrained_449;
AF := unconstrained_450;
PF := unconstrained_451;

label_0x52bb:
if (bv2bool(CF)) {
  goto label_0x52be;
}

label_0x52bd:
assume false;

label_0x52be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1880bv64));

label_0x52c6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1872bv64)));

label_0x52cd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x52cf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1444bv64)));

label_0x52d6:
t_1157 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1157, 1bv32)), (XOR_32(t_1157, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1157)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x52d8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1888bv64), RAX[32:0]);

label_0x52df:
RAX := (0bv32 ++ 4bv32);

label_0x52e4:
t_1161 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1161[64:0];
OF := bool2bv(t_1161 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1161 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_452;
SF := unconstrained_453;
ZF := unconstrained_454;
AF := unconstrained_455;

label_0x52e8:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x52ed:
t1_1163 := RCX;
t2_1164 := RAX;
RCX := PLUS_64(RCX, t2_1164);
CF := bool2bv(LT_64(RCX, t1_1163));
OF := AND_1((bool2bv((t1_1163[64:63]) == (t2_1164[64:63]))), (XOR_1((t1_1163[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1163)), t2_1164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x52f0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1896bv64), RCX);

label_0x52f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1896bv64));

label_0x5300:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_456;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5306:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x530b:
t_1171 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_457;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1171, 4bv64)), t_1171)), 2bv64)), (XOR_64((RSHIFT_64(t_1171, 4bv64)), t_1171)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1171, 4bv64)), t_1171)), 2bv64)), (XOR_64((RSHIFT_64(t_1171, 4bv64)), t_1171)))))[1:0]));
SF := t_1171[64:63];
ZF := bool2bv(0bv64 == t_1171);

label_0x530e:
if (bv2bool(ZF)) {
  goto label_0x5311;
}

label_0x5310:
assume false;

label_0x5311:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1896bv64));

label_0x5319:
origDEST_1175 := RAX;
origCOUNT_1176 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), CF, LSHIFT_64(origDEST_1175, (MINUS_64(64bv64, origCOUNT_1176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 1bv64)), origDEST_1175[64:63], unconstrained_458));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1176 == 0bv64)), AF, unconstrained_459);

label_0x531d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5324:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5328:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1896bv64));

label_0x5330:
origDEST_1181 := RCX;
origCOUNT_1182 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), CF, LSHIFT_64(origDEST_1181, (MINUS_64(64bv64, origCOUNT_1182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 1bv64)), origDEST_1181[64:63], unconstrained_460));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1182 == 0bv64)), AF, unconstrained_461);

label_0x5334:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_462;
SF := unconstrained_463;
AF := unconstrained_464;
PF := unconstrained_465;

label_0x5338:
if (bv2bool(CF)) {
  goto label_0x533b;
}

label_0x533a:
assume false;

label_0x533b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1896bv64));

label_0x5343:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1888bv64)));

label_0x534a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x534c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1464bv64)));

label_0x5353:
t_1187 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1187[32:31]) == (1bv32[32:31]))), (XOR_1((t_1187[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1187)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5355:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1904bv64), RAX[32:0]);

label_0x535c:
RAX := (0bv32 ++ 4bv32);

label_0x5361:
t_1191 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1191[64:0];
OF := bool2bv(t_1191 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1191 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_466;
SF := unconstrained_467;
ZF := unconstrained_468;
AF := unconstrained_469;

label_0x5365:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x536a:
t1_1193 := RCX;
t2_1194 := RAX;
RCX := PLUS_64(RCX, t2_1194);
CF := bool2bv(LT_64(RCX, t1_1193));
OF := AND_1((bool2bv((t1_1193[64:63]) == (t2_1194[64:63]))), (XOR_1((t1_1193[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1193)), t2_1194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x536d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1912bv64), RCX);

label_0x5375:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1912bv64));

label_0x537d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_470;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5383:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5388:
t_1201 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_471;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1201, 4bv64)), t_1201)), 2bv64)), (XOR_64((RSHIFT_64(t_1201, 4bv64)), t_1201)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1201, 4bv64)), t_1201)), 2bv64)), (XOR_64((RSHIFT_64(t_1201, 4bv64)), t_1201)))))[1:0]));
SF := t_1201[64:63];
ZF := bool2bv(0bv64 == t_1201);

label_0x538b:
if (bv2bool(ZF)) {
  goto label_0x538e;
}

label_0x538d:
assume false;

label_0x538e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1912bv64));

label_0x5396:
origDEST_1205 := RAX;
origCOUNT_1206 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), CF, LSHIFT_64(origDEST_1205, (MINUS_64(64bv64, origCOUNT_1206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 1bv64)), origDEST_1205[64:63], unconstrained_472));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1206 == 0bv64)), AF, unconstrained_473);

label_0x539a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x53a1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x53a5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1912bv64));

label_0x53ad:
origDEST_1211 := RCX;
origCOUNT_1212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), CF, LSHIFT_64(origDEST_1211, (MINUS_64(64bv64, origCOUNT_1212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 1bv64)), origDEST_1211[64:63], unconstrained_474));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1212 == 0bv64)), AF, unconstrained_475);

label_0x53b1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_476;
SF := unconstrained_477;
AF := unconstrained_478;
PF := unconstrained_479;

label_0x53b5:
if (bv2bool(CF)) {
  goto label_0x53b8;
}

label_0x53b7:
assume false;

label_0x53b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1912bv64));

label_0x53c0:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1904bv64)));

label_0x53c7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x53c9:
RAX := (0bv32 ++ 4bv32);

label_0x53ce:
t_1217 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1217[64:0];
OF := bool2bv(t_1217 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1217 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_480;
SF := unconstrained_481;
ZF := unconstrained_482;
AF := unconstrained_483;

label_0x53d2:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x53d7:
t1_1219 := RCX;
t2_1220 := RAX;
RCX := PLUS_64(RCX, t2_1220);
CF := bool2bv(LT_64(RCX, t1_1219));
OF := AND_1((bool2bv((t1_1219[64:63]) == (t2_1220[64:63]))), (XOR_1((t1_1219[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1219)), t2_1220)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x53da:
RAX := RCX;

label_0x53dd:
RCX := (0bv32 ++ 4bv32);

label_0x53e2:
t_1225 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RCX := t_1225[64:0];
OF := bool2bv(t_1225 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1225 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_484;
SF := unconstrained_485;
ZF := unconstrained_486;
AF := unconstrained_487;

label_0x53e6:
RDX := PLUS_64(RSP, 144bv64)[64:0];

label_0x53ee:
t1_1227 := RDX;
t2_1228 := RCX;
RDX := PLUS_64(RDX, t2_1228);
CF := bool2bv(LT_64(RDX, t1_1227));
OF := AND_1((bool2bv((t1_1227[64:63]) == (t2_1228[64:63]))), (XOR_1((t1_1227[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1227)), t2_1228)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x53f1:
RCX := RDX;

label_0x53f4:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x53f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x53f8:
t_1233 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_1233, (RCX[32:0])));
OF := AND_32((XOR_32(t_1233, (RCX[32:0]))), (XOR_32(t_1233, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1233)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x53fa:
RCX := (0bv32 ++ 4bv32);

label_0x53ff:
t_1237 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RCX := t_1237[64:0];
OF := bool2bv(t_1237 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1237 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_488;
SF := unconstrained_489;
ZF := unconstrained_490;
AF := unconstrained_491;

label_0x5403:
RDX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5408:
t1_1239 := RDX;
t2_1240 := RCX;
RDX := PLUS_64(RDX, t2_1240);
CF := bool2bv(LT_64(RDX, t1_1239));
OF := AND_1((bool2bv((t1_1239[64:63]) == (t2_1240[64:63]))), (XOR_1((t1_1239[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1239)), t2_1240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x540b:
RCX := RDX;

label_0x540e:
RDX := (0bv32 ++ 4bv32);

label_0x5413:
t_1245 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RDX := t_1245[64:0];
OF := bool2bv(t_1245 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_1245 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_492;
SF := unconstrained_493;
ZF := unconstrained_494;
AF := unconstrained_495;

label_0x5417:
R8 := PLUS_64(RSP, 144bv64)[64:0];

label_0x541f:
t1_1247 := R8;
t2_1248 := RDX;
R8 := PLUS_64(R8, t2_1248);
CF := bool2bv(LT_64(R8, t1_1247));
OF := AND_1((bool2bv((t1_1247[64:63]) == (t2_1248[64:63]))), (XOR_1((t1_1247[64:63]), (R8[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R8, t1_1247)), t2_1248)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))))[1:0]));
SF := R8[64:63];
ZF := bool2bv(0bv64 == R8);

label_0x5422:
RDX := R8;

label_0x5425:
RDX := (0bv32 ++ LOAD_LE_32(mem, RDX));

label_0x5427:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5429:
t_1253 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_1253, (RDX[32:0])));
OF := AND_32((XOR_32(t_1253, (RDX[32:0]))), (XOR_32(t_1253, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_1253)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x542b:
t_1257 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_1257)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1257, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1257, 4bv32)), t_1257)), 2bv32)), (XOR_32((RSHIFT_32(t_1257, 4bv32)), t_1257)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1257, 4bv32)), t_1257)), 2bv32)), (XOR_32((RSHIFT_32(t_1257, 4bv32)), t_1257)))))[1:0]));
SF := t_1257[32:31];
ZF := bool2bv(0bv32 == t_1257);

label_0x542d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x5778;
}

label_0x5433:
RAX := (0bv32 ++ 4bv32);

label_0x5438:
t_1261 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1261[64:0];
OF := bool2bv(t_1261 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1261 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_496;
SF := unconstrained_497;
ZF := unconstrained_498;
AF := unconstrained_499;

label_0x543c:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5444:
t1_1263 := RCX;
t2_1264 := RAX;
RCX := PLUS_64(RCX, t2_1264);
CF := bool2bv(LT_64(RCX, t1_1263));
OF := AND_1((bool2bv((t1_1263[64:63]) == (t2_1264[64:63]))), (XOR_1((t1_1263[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1263)), t2_1264)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5447:
RAX := RCX;

label_0x544a:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x544c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1512bv64), RAX[32:0]);

label_0x5453:
RAX := (0bv32 ++ 4bv32);

label_0x5458:
t_1269 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1269[64:0];
OF := bool2bv(t_1269 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1269 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_500;
SF := unconstrained_501;
ZF := unconstrained_502;
AF := unconstrained_503;

label_0x545c:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5464:
t1_1271 := RCX;
t2_1272 := RAX;
RCX := PLUS_64(RCX, t2_1272);
CF := bool2bv(LT_64(RCX, t1_1271));
OF := AND_1((bool2bv((t1_1271[64:63]) == (t2_1272[64:63]))), (XOR_1((t1_1271[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1271)), t2_1272)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5467:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1920bv64), RCX);

label_0x546f:
RAX := (0bv32 ++ 4bv32);

label_0x5474:
t_1277 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1277[64:0];
OF := bool2bv(t_1277 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1277 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_504;
SF := unconstrained_505;
ZF := unconstrained_506;
AF := unconstrained_507;

label_0x5478:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5480:
t1_1279 := RCX;
t2_1280 := RAX;
RCX := PLUS_64(RCX, t2_1280);
CF := bool2bv(LT_64(RCX, t1_1279));
OF := AND_1((bool2bv((t1_1279[64:63]) == (t2_1280[64:63]))), (XOR_1((t1_1279[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1279)), t2_1280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5483:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1928bv64), RCX);

label_0x548b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1928bv64));

label_0x5493:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_508;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5499:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x549e:
t_1287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_509;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1287, 4bv64)), t_1287)), 2bv64)), (XOR_64((RSHIFT_64(t_1287, 4bv64)), t_1287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1287, 4bv64)), t_1287)), 2bv64)), (XOR_64((RSHIFT_64(t_1287, 4bv64)), t_1287)))))[1:0]));
SF := t_1287[64:63];
ZF := bool2bv(0bv64 == t_1287);

label_0x54a1:
if (bv2bool(ZF)) {
  goto label_0x54a4;
}

label_0x54a3:
assume false;

label_0x54a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1928bv64));

label_0x54ac:
origDEST_1291 := RAX;
origCOUNT_1292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), CF, LSHIFT_64(origDEST_1291, (MINUS_64(64bv64, origCOUNT_1292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 1bv64)), origDEST_1291[64:63], unconstrained_510));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), AF, unconstrained_511);

label_0x54b0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x54b7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x54bb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1928bv64));

label_0x54c3:
origDEST_1297 := RCX;
origCOUNT_1298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), CF, LSHIFT_64(origDEST_1297, (MINUS_64(64bv64, origCOUNT_1298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 1bv64)), origDEST_1297[64:63], unconstrained_512));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1298 == 0bv64)), AF, unconstrained_513);

label_0x54c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_514;
SF := unconstrained_515;
AF := unconstrained_516;
PF := unconstrained_517;

label_0x54cb:
if (bv2bool(CF)) {
  goto label_0x54ce;
}

label_0x54cd:
assume false;

label_0x54ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1928bv64));

label_0x54d6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1920bv64));

label_0x54de:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x54e0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x54e2:
RAX := (0bv32 ++ 4bv32);

label_0x54e7:
t_1303 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1303[64:0];
OF := bool2bv(t_1303 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1303 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_518;
SF := unconstrained_519;
ZF := unconstrained_520;
AF := unconstrained_521;

label_0x54eb:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x54f3:
t1_1305 := RCX;
t2_1306 := RAX;
RCX := PLUS_64(RCX, t2_1306);
CF := bool2bv(LT_64(RCX, t1_1305));
OF := AND_1((bool2bv((t1_1305[64:63]) == (t2_1306[64:63]))), (XOR_1((t1_1305[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1305)), t2_1306)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x54f6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1936bv64), RCX);

label_0x54fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1936bv64));

label_0x5506:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_522;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x550c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5511:
t_1313 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_523;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)), 2bv64)), (XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)), 2bv64)), (XOR_64((RSHIFT_64(t_1313, 4bv64)), t_1313)))))[1:0]));
SF := t_1313[64:63];
ZF := bool2bv(0bv64 == t_1313);

label_0x5514:
if (bv2bool(ZF)) {
  goto label_0x5517;
}

label_0x5516:
assume false;

label_0x5517:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1936bv64));

label_0x551f:
origDEST_1317 := RAX;
origCOUNT_1318 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), CF, LSHIFT_64(origDEST_1317, (MINUS_64(64bv64, origCOUNT_1318)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 1bv64)), origDEST_1317[64:63], unconstrained_524));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1318 == 0bv64)), AF, unconstrained_525);

label_0x5523:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x552a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x552e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1936bv64));

label_0x5536:
origDEST_1323 := RCX;
origCOUNT_1324 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), CF, LSHIFT_64(origDEST_1323, (MINUS_64(64bv64, origCOUNT_1324)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 1bv64)), origDEST_1323[64:63], unconstrained_526));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1324 == 0bv64)), AF, unconstrained_527);

label_0x553a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_528;
SF := unconstrained_529;
AF := unconstrained_530;
PF := unconstrained_531;

label_0x553e:
if (bv2bool(CF)) {
  goto label_0x5541;
}

label_0x5540:
assume false;

label_0x5541:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1936bv64));

label_0x5549:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1512bv64)));

label_0x5550:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5552:
RAX := (0bv32 ++ 4bv32);

label_0x5557:
t_1329 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1329[64:0];
OF := bool2bv(t_1329 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1329 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_532;
SF := unconstrained_533;
ZF := unconstrained_534;
AF := unconstrained_535;

label_0x555b:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5560:
t1_1331 := RCX;
t2_1332 := RAX;
RCX := PLUS_64(RCX, t2_1332);
CF := bool2bv(LT_64(RCX, t1_1331));
OF := AND_1((bool2bv((t1_1331[64:63]) == (t2_1332[64:63]))), (XOR_1((t1_1331[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1331)), t2_1332)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5563:
RAX := RCX;

label_0x5566:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5568:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1512bv64), RAX[32:0]);

label_0x556f:
RAX := (0bv32 ++ 4bv32);

label_0x5574:
t_1337 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1337[64:0];
OF := bool2bv(t_1337 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1337 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_536;
SF := unconstrained_537;
ZF := unconstrained_538;
AF := unconstrained_539;

label_0x5578:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x557d:
t1_1339 := RCX;
t2_1340 := RAX;
RCX := PLUS_64(RCX, t2_1340);
CF := bool2bv(LT_64(RCX, t1_1339));
OF := AND_1((bool2bv((t1_1339[64:63]) == (t2_1340[64:63]))), (XOR_1((t1_1339[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1339)), t2_1340)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5580:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1944bv64), RCX);

label_0x5588:
RAX := (0bv32 ++ 4bv32);

label_0x558d:
t_1345 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1345[64:0];
OF := bool2bv(t_1345 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1345 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_540;
SF := unconstrained_541;
ZF := unconstrained_542;
AF := unconstrained_543;

label_0x5591:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5596:
t1_1347 := RCX;
t2_1348 := RAX;
RCX := PLUS_64(RCX, t2_1348);
CF := bool2bv(LT_64(RCX, t1_1347));
OF := AND_1((bool2bv((t1_1347[64:63]) == (t2_1348[64:63]))), (XOR_1((t1_1347[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1347)), t2_1348)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5599:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1952bv64), RCX);

label_0x55a1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1952bv64));

label_0x55a9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_544;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x55af:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x55b4:
t_1355 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_545;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1355, 4bv64)), t_1355)), 2bv64)), (XOR_64((RSHIFT_64(t_1355, 4bv64)), t_1355)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1355, 4bv64)), t_1355)), 2bv64)), (XOR_64((RSHIFT_64(t_1355, 4bv64)), t_1355)))))[1:0]));
SF := t_1355[64:63];
ZF := bool2bv(0bv64 == t_1355);

label_0x55b7:
if (bv2bool(ZF)) {
  goto label_0x55ba;
}

label_0x55b9:
assume false;

label_0x55ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1952bv64));

label_0x55c2:
origDEST_1359 := RAX;
origCOUNT_1360 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), CF, LSHIFT_64(origDEST_1359, (MINUS_64(64bv64, origCOUNT_1360)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 1bv64)), origDEST_1359[64:63], unconstrained_546));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1360 == 0bv64)), AF, unconstrained_547);

label_0x55c6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x55cd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x55d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1952bv64));

label_0x55d9:
origDEST_1365 := RCX;
origCOUNT_1366 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), CF, LSHIFT_64(origDEST_1365, (MINUS_64(64bv64, origCOUNT_1366)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 1bv64)), origDEST_1365[64:63], unconstrained_548));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1366 == 0bv64)), AF, unconstrained_549);

label_0x55dd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_550;
SF := unconstrained_551;
AF := unconstrained_552;
PF := unconstrained_553;

label_0x55e1:
if (bv2bool(CF)) {
  goto label_0x55e4;
}

label_0x55e3:
assume false;

label_0x55e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1952bv64));

label_0x55ec:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1944bv64));

label_0x55f4:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x55f6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x55f8:
RAX := (0bv32 ++ 4bv32);

label_0x55fd:
t_1371 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1371[64:0];
OF := bool2bv(t_1371 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1371 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_554;
SF := unconstrained_555;
ZF := unconstrained_556;
AF := unconstrained_557;

label_0x5601:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5606:
t1_1373 := RCX;
t2_1374 := RAX;
RCX := PLUS_64(RCX, t2_1374);
CF := bool2bv(LT_64(RCX, t1_1373));
OF := AND_1((bool2bv((t1_1373[64:63]) == (t2_1374[64:63]))), (XOR_1((t1_1373[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1373)), t2_1374)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5609:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1960bv64), RCX);

label_0x5611:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1960bv64));

label_0x5619:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_558;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x561f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5624:
t_1381 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_559;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1381, 4bv64)), t_1381)), 2bv64)), (XOR_64((RSHIFT_64(t_1381, 4bv64)), t_1381)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1381, 4bv64)), t_1381)), 2bv64)), (XOR_64((RSHIFT_64(t_1381, 4bv64)), t_1381)))))[1:0]));
SF := t_1381[64:63];
ZF := bool2bv(0bv64 == t_1381);

label_0x5627:
if (bv2bool(ZF)) {
  goto label_0x562a;
}

label_0x5629:
assume false;

label_0x562a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1960bv64));

label_0x5632:
origDEST_1385 := RAX;
origCOUNT_1386 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), CF, LSHIFT_64(origDEST_1385, (MINUS_64(64bv64, origCOUNT_1386)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 1bv64)), origDEST_1385[64:63], unconstrained_560));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), AF, unconstrained_561);

label_0x5636:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x563d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5641:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1960bv64));

label_0x5649:
origDEST_1391 := RCX;
origCOUNT_1392 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), CF, LSHIFT_64(origDEST_1391, (MINUS_64(64bv64, origCOUNT_1392)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 1bv64)), origDEST_1391[64:63], unconstrained_562));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv64)), AF, unconstrained_563);

label_0x564d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_564;
SF := unconstrained_565;
AF := unconstrained_566;
PF := unconstrained_567;

label_0x5651:
if (bv2bool(CF)) {
  goto label_0x5654;
}

label_0x5653:
assume false;

label_0x5654:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1960bv64));

label_0x565c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1512bv64)));

label_0x5663:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5665:
RAX := (0bv32 ++ 4bv32);

label_0x566a:
t_1397 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1397[64:0];
OF := bool2bv(t_1397 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1397 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_568;
SF := unconstrained_569;
ZF := unconstrained_570;
AF := unconstrained_571;

label_0x566e:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5673:
t1_1399 := RCX;
t2_1400 := RAX;
RCX := PLUS_64(RCX, t2_1400);
CF := bool2bv(LT_64(RCX, t1_1399));
OF := AND_1((bool2bv((t1_1399[64:63]) == (t2_1400[64:63]))), (XOR_1((t1_1399[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1399)), t2_1400)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5676:
RAX := RCX;

label_0x5679:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x567b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1512bv64), RAX[32:0]);

label_0x5682:
RAX := (0bv32 ++ 4bv32);

label_0x5687:
t_1405 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1405[64:0];
OF := bool2bv(t_1405 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1405 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_572;
SF := unconstrained_573;
ZF := unconstrained_574;
AF := unconstrained_575;

label_0x568b:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5690:
t1_1407 := RCX;
t2_1408 := RAX;
RCX := PLUS_64(RCX, t2_1408);
CF := bool2bv(LT_64(RCX, t1_1407));
OF := AND_1((bool2bv((t1_1407[64:63]) == (t2_1408[64:63]))), (XOR_1((t1_1407[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1407)), t2_1408)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5693:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1968bv64), RCX);

label_0x569b:
RAX := (0bv32 ++ 4bv32);

label_0x56a0:
t_1413 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1413[64:0];
OF := bool2bv(t_1413 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1413 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_576;
SF := unconstrained_577;
ZF := unconstrained_578;
AF := unconstrained_579;

label_0x56a4:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x56a9:
t1_1415 := RCX;
t2_1416 := RAX;
RCX := PLUS_64(RCX, t2_1416);
CF := bool2bv(LT_64(RCX, t1_1415));
OF := AND_1((bool2bv((t1_1415[64:63]) == (t2_1416[64:63]))), (XOR_1((t1_1415[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1415)), t2_1416)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x56ac:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1976bv64), RCX);

label_0x56b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1976bv64));

label_0x56bc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_580;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x56c2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x56c7:
t_1423 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_581;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1423, 4bv64)), t_1423)), 2bv64)), (XOR_64((RSHIFT_64(t_1423, 4bv64)), t_1423)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1423, 4bv64)), t_1423)), 2bv64)), (XOR_64((RSHIFT_64(t_1423, 4bv64)), t_1423)))))[1:0]));
SF := t_1423[64:63];
ZF := bool2bv(0bv64 == t_1423);

label_0x56ca:
if (bv2bool(ZF)) {
  goto label_0x56cd;
}

label_0x56cc:
assume false;

label_0x56cd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1976bv64));

label_0x56d5:
origDEST_1427 := RAX;
origCOUNT_1428 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), CF, LSHIFT_64(origDEST_1427, (MINUS_64(64bv64, origCOUNT_1428)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 1bv64)), origDEST_1427[64:63], unconstrained_582));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1428 == 0bv64)), AF, unconstrained_583);

label_0x56d9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x56e0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x56e4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1976bv64));

label_0x56ec:
origDEST_1433 := RCX;
origCOUNT_1434 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), CF, LSHIFT_64(origDEST_1433, (MINUS_64(64bv64, origCOUNT_1434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 1bv64)), origDEST_1433[64:63], unconstrained_584));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), AF, unconstrained_585);

label_0x56f0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_586;
SF := unconstrained_587;
AF := unconstrained_588;
PF := unconstrained_589;

label_0x56f4:
if (bv2bool(CF)) {
  goto label_0x56f7;
}

label_0x56f6:
assume false;

label_0x56f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1976bv64));

label_0x56ff:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1968bv64));

label_0x5707:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5709:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x570b:
RAX := (0bv32 ++ 4bv32);

label_0x5710:
t_1439 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1439[64:0];
OF := bool2bv(t_1439 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1439 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_590;
SF := unconstrained_591;
ZF := unconstrained_592;
AF := unconstrained_593;

label_0x5714:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5719:
t1_1441 := RCX;
t2_1442 := RAX;
RCX := PLUS_64(RCX, t2_1442);
CF := bool2bv(LT_64(RCX, t1_1441));
OF := AND_1((bool2bv((t1_1441[64:63]) == (t2_1442[64:63]))), (XOR_1((t1_1441[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1441)), t2_1442)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x571c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1984bv64), RCX);

label_0x5724:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1984bv64));

label_0x572c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_594;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5732:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5737:
t_1449 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_595;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1449, 4bv64)), t_1449)), 2bv64)), (XOR_64((RSHIFT_64(t_1449, 4bv64)), t_1449)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1449, 4bv64)), t_1449)), 2bv64)), (XOR_64((RSHIFT_64(t_1449, 4bv64)), t_1449)))))[1:0]));
SF := t_1449[64:63];
ZF := bool2bv(0bv64 == t_1449);

label_0x573a:
if (bv2bool(ZF)) {
  goto label_0x573d;
}

label_0x573c:
assume false;

label_0x573d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1984bv64));

label_0x5745:
origDEST_1453 := RAX;
origCOUNT_1454 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), CF, LSHIFT_64(origDEST_1453, (MINUS_64(64bv64, origCOUNT_1454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 1bv64)), origDEST_1453[64:63], unconstrained_596));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1454 == 0bv64)), AF, unconstrained_597);

label_0x5749:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5750:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5754:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1984bv64));

label_0x575c:
origDEST_1459 := RCX;
origCOUNT_1460 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), CF, LSHIFT_64(origDEST_1459, (MINUS_64(64bv64, origCOUNT_1460)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 1bv64)), origDEST_1459[64:63], unconstrained_598));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1460 == 0bv64)), AF, unconstrained_599);

label_0x5760:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_600;
SF := unconstrained_601;
AF := unconstrained_602;
PF := unconstrained_603;

label_0x5764:
if (bv2bool(CF)) {
  goto label_0x5767;
}

label_0x5766:
assume false;

label_0x5767:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 1984bv64));

label_0x576f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1512bv64)));

label_0x5776:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5778:
RAX := (0bv32 ++ 4bv32);

label_0x577d:
t_1465 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1465[64:0];
OF := bool2bv(t_1465 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1465 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_604;
SF := unconstrained_605;
ZF := unconstrained_606;
AF := unconstrained_607;

label_0x5781:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5786:
t1_1467 := RCX;
t2_1468 := RAX;
RCX := PLUS_64(RCX, t2_1468);
CF := bool2bv(LT_64(RCX, t1_1467));
OF := AND_1((bool2bv((t1_1467[64:63]) == (t2_1468[64:63]))), (XOR_1((t1_1467[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1467)), t2_1468)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5789:
RAX := RCX;

label_0x578c:
RCX := (0bv32 ++ 4bv32);

label_0x5791:
t_1473 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RCX := t_1473[64:0];
OF := bool2bv(t_1473 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1473 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_608;
SF := unconstrained_609;
ZF := unconstrained_610;
AF := unconstrained_611;

label_0x5795:
RDX := PLUS_64(RSP, 144bv64)[64:0];

label_0x579d:
t1_1475 := RDX;
t2_1476 := RCX;
RDX := PLUS_64(RDX, t2_1476);
CF := bool2bv(LT_64(RDX, t1_1475));
OF := AND_1((bool2bv((t1_1475[64:63]) == (t2_1476[64:63]))), (XOR_1((t1_1475[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1475)), t2_1476)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x57a0:
RCX := RDX;

label_0x57a3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x57a5:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x57a7:
t_1481 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_1481, (RCX[32:0])));
OF := AND_32((XOR_32(t_1481, (RCX[32:0]))), (XOR_32(t_1481, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1481)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x57a9:
RCX := (0bv32 ++ 4bv32);

label_0x57ae:
t_1485 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RCX := t_1485[64:0];
OF := bool2bv(t_1485 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1485 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_612;
SF := unconstrained_613;
ZF := unconstrained_614;
AF := unconstrained_615;

label_0x57b2:
RDX := PLUS_64(RSP, 112bv64)[64:0];

label_0x57b7:
t1_1487 := RDX;
t2_1488 := RCX;
RDX := PLUS_64(RDX, t2_1488);
CF := bool2bv(LT_64(RDX, t1_1487));
OF := AND_1((bool2bv((t1_1487[64:63]) == (t2_1488[64:63]))), (XOR_1((t1_1487[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1487)), t2_1488)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x57ba:
RCX := RDX;

label_0x57bd:
RDX := (0bv32 ++ 4bv32);

label_0x57c2:
t_1493 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RDX := t_1493[64:0];
OF := bool2bv(t_1493 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_1493 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_616;
SF := unconstrained_617;
ZF := unconstrained_618;
AF := unconstrained_619;

label_0x57c6:
R8 := PLUS_64(RSP, 144bv64)[64:0];

label_0x57ce:
t1_1495 := R8;
t2_1496 := RDX;
R8 := PLUS_64(R8, t2_1496);
CF := bool2bv(LT_64(R8, t1_1495));
OF := AND_1((bool2bv((t1_1495[64:63]) == (t2_1496[64:63]))), (XOR_1((t1_1495[64:63]), (R8[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R8, t1_1495)), t2_1496)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))))[1:0]));
SF := R8[64:63];
ZF := bool2bv(0bv64 == R8);

label_0x57d1:
RDX := R8;

label_0x57d4:
RDX := (0bv32 ++ LOAD_LE_32(mem, RDX));

label_0x57d6:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x57d8:
t_1501 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_1501, (RDX[32:0])));
OF := AND_32((XOR_32(t_1501, (RDX[32:0]))), (XOR_32(t_1501, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_1501)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x57da:
t_1505 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_1505)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1505, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1505, 4bv32)), t_1505)), 2bv32)), (XOR_32((RSHIFT_32(t_1505, 4bv32)), t_1505)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1505, 4bv32)), t_1505)), 2bv32)), (XOR_32((RSHIFT_32(t_1505, 4bv32)), t_1505)))))[1:0]));
SF := t_1505[32:31];
ZF := bool2bv(0bv32 == t_1505);

label_0x57dc:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x5b27;
}

label_0x57e2:
RAX := (0bv32 ++ 4bv32);

label_0x57e7:
t_1509 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1509[64:0];
OF := bool2bv(t_1509 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1509 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_620;
SF := unconstrained_621;
ZF := unconstrained_622;
AF := unconstrained_623;

label_0x57eb:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x57f3:
t1_1511 := RCX;
t2_1512 := RAX;
RCX := PLUS_64(RCX, t2_1512);
CF := bool2bv(LT_64(RCX, t1_1511));
OF := AND_1((bool2bv((t1_1511[64:63]) == (t2_1512[64:63]))), (XOR_1((t1_1511[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1511)), t2_1512)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x57f6:
RAX := RCX;

label_0x57f9:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x57fb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1516bv64), RAX[32:0]);

label_0x5802:
RAX := (0bv32 ++ 4bv32);

label_0x5807:
t_1517 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1517[64:0];
OF := bool2bv(t_1517 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1517 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_624;
SF := unconstrained_625;
ZF := unconstrained_626;
AF := unconstrained_627;

label_0x580b:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5813:
t1_1519 := RCX;
t2_1520 := RAX;
RCX := PLUS_64(RCX, t2_1520);
CF := bool2bv(LT_64(RCX, t1_1519));
OF := AND_1((bool2bv((t1_1519[64:63]) == (t2_1520[64:63]))), (XOR_1((t1_1519[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1519)), t2_1520)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5816:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1992bv64), RCX);

label_0x581e:
RAX := (0bv32 ++ 4bv32);

label_0x5823:
t_1525 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1525[64:0];
OF := bool2bv(t_1525 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1525 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_628;
SF := unconstrained_629;
ZF := unconstrained_630;
AF := unconstrained_631;

label_0x5827:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x582f:
t1_1527 := RCX;
t2_1528 := RAX;
RCX := PLUS_64(RCX, t2_1528);
CF := bool2bv(LT_64(RCX, t1_1527));
OF := AND_1((bool2bv((t1_1527[64:63]) == (t2_1528[64:63]))), (XOR_1((t1_1527[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1527)), t2_1528)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5832:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2000bv64), RCX);

label_0x583a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2000bv64));

label_0x5842:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_632;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5848:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x584d:
t_1535 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_633;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1535, 4bv64)), t_1535)), 2bv64)), (XOR_64((RSHIFT_64(t_1535, 4bv64)), t_1535)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1535, 4bv64)), t_1535)), 2bv64)), (XOR_64((RSHIFT_64(t_1535, 4bv64)), t_1535)))))[1:0]));
SF := t_1535[64:63];
ZF := bool2bv(0bv64 == t_1535);

label_0x5850:
if (bv2bool(ZF)) {
  goto label_0x5853;
}

label_0x5852:
assume false;

label_0x5853:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2000bv64));

label_0x585b:
origDEST_1539 := RAX;
origCOUNT_1540 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), CF, LSHIFT_64(origDEST_1539, (MINUS_64(64bv64, origCOUNT_1540)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 1bv64)), origDEST_1539[64:63], unconstrained_634));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1540 == 0bv64)), AF, unconstrained_635);

label_0x585f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5866:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x586a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2000bv64));

label_0x5872:
origDEST_1545 := RCX;
origCOUNT_1546 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), CF, LSHIFT_64(origDEST_1545, (MINUS_64(64bv64, origCOUNT_1546)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 1bv64)), origDEST_1545[64:63], unconstrained_636));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1546 == 0bv64)), AF, unconstrained_637);

label_0x5876:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_638;
SF := unconstrained_639;
AF := unconstrained_640;
PF := unconstrained_641;

label_0x587a:
if (bv2bool(CF)) {
  goto label_0x587d;
}

label_0x587c:
assume false;

label_0x587d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2000bv64));

label_0x5885:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 1992bv64));

label_0x588d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x588f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5891:
RAX := (0bv32 ++ 4bv32);

label_0x5896:
t_1551 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1551[64:0];
OF := bool2bv(t_1551 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1551 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_642;
SF := unconstrained_643;
ZF := unconstrained_644;
AF := unconstrained_645;

label_0x589a:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x58a2:
t1_1553 := RCX;
t2_1554 := RAX;
RCX := PLUS_64(RCX, t2_1554);
CF := bool2bv(LT_64(RCX, t1_1553));
OF := AND_1((bool2bv((t1_1553[64:63]) == (t2_1554[64:63]))), (XOR_1((t1_1553[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1553)), t2_1554)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x58a5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2008bv64), RCX);

label_0x58ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2008bv64));

label_0x58b5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_646;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x58bb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x58c0:
t_1561 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_647;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1561, 4bv64)), t_1561)), 2bv64)), (XOR_64((RSHIFT_64(t_1561, 4bv64)), t_1561)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1561, 4bv64)), t_1561)), 2bv64)), (XOR_64((RSHIFT_64(t_1561, 4bv64)), t_1561)))))[1:0]));
SF := t_1561[64:63];
ZF := bool2bv(0bv64 == t_1561);

label_0x58c3:
if (bv2bool(ZF)) {
  goto label_0x58c6;
}

label_0x58c5:
assume false;

label_0x58c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2008bv64));

label_0x58ce:
origDEST_1565 := RAX;
origCOUNT_1566 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), CF, LSHIFT_64(origDEST_1565, (MINUS_64(64bv64, origCOUNT_1566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 1bv64)), origDEST_1565[64:63], unconstrained_648));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1566 == 0bv64)), AF, unconstrained_649);

label_0x58d2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x58d9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x58dd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2008bv64));

label_0x58e5:
origDEST_1571 := RCX;
origCOUNT_1572 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), CF, LSHIFT_64(origDEST_1571, (MINUS_64(64bv64, origCOUNT_1572)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 1bv64)), origDEST_1571[64:63], unconstrained_650));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1572 == 0bv64)), AF, unconstrained_651);

label_0x58e9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_652;
SF := unconstrained_653;
AF := unconstrained_654;
PF := unconstrained_655;

label_0x58ed:
if (bv2bool(CF)) {
  goto label_0x58f0;
}

label_0x58ef:
assume false;

label_0x58f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2008bv64));

label_0x58f8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1516bv64)));

label_0x58ff:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5901:
RAX := (0bv32 ++ 4bv32);

label_0x5906:
t_1577 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1577[64:0];
OF := bool2bv(t_1577 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1577 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_656;
SF := unconstrained_657;
ZF := unconstrained_658;
AF := unconstrained_659;

label_0x590a:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x590f:
t1_1579 := RCX;
t2_1580 := RAX;
RCX := PLUS_64(RCX, t2_1580);
CF := bool2bv(LT_64(RCX, t1_1579));
OF := AND_1((bool2bv((t1_1579[64:63]) == (t2_1580[64:63]))), (XOR_1((t1_1579[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1579)), t2_1580)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5912:
RAX := RCX;

label_0x5915:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5917:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1516bv64), RAX[32:0]);

label_0x591e:
RAX := (0bv32 ++ 4bv32);

label_0x5923:
t_1585 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1585[64:0];
OF := bool2bv(t_1585 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1585 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_660;
SF := unconstrained_661;
ZF := unconstrained_662;
AF := unconstrained_663;

label_0x5927:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x592c:
t1_1587 := RCX;
t2_1588 := RAX;
RCX := PLUS_64(RCX, t2_1588);
CF := bool2bv(LT_64(RCX, t1_1587));
OF := AND_1((bool2bv((t1_1587[64:63]) == (t2_1588[64:63]))), (XOR_1((t1_1587[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1587)), t2_1588)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x592f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2016bv64), RCX);

label_0x5937:
RAX := (0bv32 ++ 4bv32);

label_0x593c:
t_1593 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1593[64:0];
OF := bool2bv(t_1593 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1593 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_664;
SF := unconstrained_665;
ZF := unconstrained_666;
AF := unconstrained_667;

label_0x5940:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5945:
t1_1595 := RCX;
t2_1596 := RAX;
RCX := PLUS_64(RCX, t2_1596);
CF := bool2bv(LT_64(RCX, t1_1595));
OF := AND_1((bool2bv((t1_1595[64:63]) == (t2_1596[64:63]))), (XOR_1((t1_1595[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1595)), t2_1596)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5948:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2024bv64), RCX);

label_0x5950:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2024bv64));

label_0x5958:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_668;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x595e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5963:
t_1603 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_669;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1603, 4bv64)), t_1603)), 2bv64)), (XOR_64((RSHIFT_64(t_1603, 4bv64)), t_1603)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1603, 4bv64)), t_1603)), 2bv64)), (XOR_64((RSHIFT_64(t_1603, 4bv64)), t_1603)))))[1:0]));
SF := t_1603[64:63];
ZF := bool2bv(0bv64 == t_1603);

label_0x5966:
if (bv2bool(ZF)) {
  goto label_0x5969;
}

label_0x5968:
assume false;

label_0x5969:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2024bv64));

label_0x5971:
origDEST_1607 := RAX;
origCOUNT_1608 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), CF, LSHIFT_64(origDEST_1607, (MINUS_64(64bv64, origCOUNT_1608)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 1bv64)), origDEST_1607[64:63], unconstrained_670));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1608 == 0bv64)), AF, unconstrained_671);

label_0x5975:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x597c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5980:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2024bv64));

label_0x5988:
origDEST_1613 := RCX;
origCOUNT_1614 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), CF, LSHIFT_64(origDEST_1613, (MINUS_64(64bv64, origCOUNT_1614)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 1bv64)), origDEST_1613[64:63], unconstrained_672));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1614 == 0bv64)), AF, unconstrained_673);

label_0x598c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_674;
SF := unconstrained_675;
AF := unconstrained_676;
PF := unconstrained_677;

label_0x5990:
if (bv2bool(CF)) {
  goto label_0x5993;
}

label_0x5992:
assume false;

label_0x5993:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2024bv64));

label_0x599b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2016bv64));

label_0x59a3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x59a5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x59a7:
RAX := (0bv32 ++ 4bv32);

label_0x59ac:
t_1619 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1619[64:0];
OF := bool2bv(t_1619 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1619 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_678;
SF := unconstrained_679;
ZF := unconstrained_680;
AF := unconstrained_681;

label_0x59b0:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x59b5:
t1_1621 := RCX;
t2_1622 := RAX;
RCX := PLUS_64(RCX, t2_1622);
CF := bool2bv(LT_64(RCX, t1_1621));
OF := AND_1((bool2bv((t1_1621[64:63]) == (t2_1622[64:63]))), (XOR_1((t1_1621[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1621)), t2_1622)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x59b8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2032bv64), RCX);

label_0x59c0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2032bv64));

label_0x59c8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_682;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x59ce:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x59d3:
t_1629 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_683;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1629, 4bv64)), t_1629)), 2bv64)), (XOR_64((RSHIFT_64(t_1629, 4bv64)), t_1629)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1629, 4bv64)), t_1629)), 2bv64)), (XOR_64((RSHIFT_64(t_1629, 4bv64)), t_1629)))))[1:0]));
SF := t_1629[64:63];
ZF := bool2bv(0bv64 == t_1629);

label_0x59d6:
if (bv2bool(ZF)) {
  goto label_0x59d9;
}

label_0x59d8:
assume false;

label_0x59d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2032bv64));

label_0x59e1:
origDEST_1633 := RAX;
origCOUNT_1634 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), CF, LSHIFT_64(origDEST_1633, (MINUS_64(64bv64, origCOUNT_1634)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 1bv64)), origDEST_1633[64:63], unconstrained_684));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1634 == 0bv64)), AF, unconstrained_685);

label_0x59e5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x59ec:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x59f0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2032bv64));

label_0x59f8:
origDEST_1639 := RCX;
origCOUNT_1640 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), CF, LSHIFT_64(origDEST_1639, (MINUS_64(64bv64, origCOUNT_1640)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 1bv64)), origDEST_1639[64:63], unconstrained_686));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1640 == 0bv64)), AF, unconstrained_687);

label_0x59fc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_688;
SF := unconstrained_689;
AF := unconstrained_690;
PF := unconstrained_691;

label_0x5a00:
if (bv2bool(CF)) {
  goto label_0x5a03;
}

label_0x5a02:
assume false;

label_0x5a03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2032bv64));

label_0x5a0b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1516bv64)));

label_0x5a12:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5a14:
RAX := (0bv32 ++ 4bv32);

label_0x5a19:
t_1645 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1645[64:0];
OF := bool2bv(t_1645 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1645 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_692;
SF := unconstrained_693;
ZF := unconstrained_694;
AF := unconstrained_695;

label_0x5a1d:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5a22:
t1_1647 := RCX;
t2_1648 := RAX;
RCX := PLUS_64(RCX, t2_1648);
CF := bool2bv(LT_64(RCX, t1_1647));
OF := AND_1((bool2bv((t1_1647[64:63]) == (t2_1648[64:63]))), (XOR_1((t1_1647[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1647)), t2_1648)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5a25:
RAX := RCX;

label_0x5a28:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5a2a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1516bv64), RAX[32:0]);

label_0x5a31:
RAX := (0bv32 ++ 4bv32);

label_0x5a36:
t_1653 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1653[64:0];
OF := bool2bv(t_1653 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1653 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_696;
SF := unconstrained_697;
ZF := unconstrained_698;
AF := unconstrained_699;

label_0x5a3a:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5a3f:
t1_1655 := RCX;
t2_1656 := RAX;
RCX := PLUS_64(RCX, t2_1656);
CF := bool2bv(LT_64(RCX, t1_1655));
OF := AND_1((bool2bv((t1_1655[64:63]) == (t2_1656[64:63]))), (XOR_1((t1_1655[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1655)), t2_1656)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5a42:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2040bv64), RCX);

label_0x5a4a:
RAX := (0bv32 ++ 4bv32);

label_0x5a4f:
t_1661 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1661[64:0];
OF := bool2bv(t_1661 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1661 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_700;
SF := unconstrained_701;
ZF := unconstrained_702;
AF := unconstrained_703;

label_0x5a53:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5a58:
t1_1663 := RCX;
t2_1664 := RAX;
RCX := PLUS_64(RCX, t2_1664);
CF := bool2bv(LT_64(RCX, t1_1663));
OF := AND_1((bool2bv((t1_1663[64:63]) == (t2_1664[64:63]))), (XOR_1((t1_1663[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1663)), t2_1664)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5a5b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2048bv64), RCX);

label_0x5a63:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2048bv64));

label_0x5a6b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_704;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5a71:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5a76:
t_1671 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_705;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1671, 4bv64)), t_1671)), 2bv64)), (XOR_64((RSHIFT_64(t_1671, 4bv64)), t_1671)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1671, 4bv64)), t_1671)), 2bv64)), (XOR_64((RSHIFT_64(t_1671, 4bv64)), t_1671)))))[1:0]));
SF := t_1671[64:63];
ZF := bool2bv(0bv64 == t_1671);

label_0x5a79:
if (bv2bool(ZF)) {
  goto label_0x5a7c;
}

label_0x5a7b:
assume false;

label_0x5a7c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2048bv64));

label_0x5a84:
origDEST_1675 := RAX;
origCOUNT_1676 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), CF, LSHIFT_64(origDEST_1675, (MINUS_64(64bv64, origCOUNT_1676)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 1bv64)), origDEST_1675[64:63], unconstrained_706));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1676 == 0bv64)), AF, unconstrained_707);

label_0x5a88:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5a8f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5a93:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2048bv64));

label_0x5a9b:
origDEST_1681 := RCX;
origCOUNT_1682 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), CF, LSHIFT_64(origDEST_1681, (MINUS_64(64bv64, origCOUNT_1682)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 1bv64)), origDEST_1681[64:63], unconstrained_708));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1682 == 0bv64)), AF, unconstrained_709);

label_0x5a9f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_710;
SF := unconstrained_711;
AF := unconstrained_712;
PF := unconstrained_713;

label_0x5aa3:
if (bv2bool(CF)) {
  goto label_0x5aa6;
}

label_0x5aa5:
assume false;

label_0x5aa6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2048bv64));

label_0x5aae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2040bv64));

label_0x5ab6:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5ab8:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5aba:
RAX := (0bv32 ++ 4bv32);

label_0x5abf:
t_1687 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_1687[64:0];
OF := bool2bv(t_1687 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1687 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_714;
SF := unconstrained_715;
ZF := unconstrained_716;
AF := unconstrained_717;

label_0x5ac3:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5ac8:
t1_1689 := RCX;
t2_1690 := RAX;
RCX := PLUS_64(RCX, t2_1690);
CF := bool2bv(LT_64(RCX, t1_1689));
OF := AND_1((bool2bv((t1_1689[64:63]) == (t2_1690[64:63]))), (XOR_1((t1_1689[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1689)), t2_1690)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5acb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2056bv64), RCX);

label_0x5ad3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2056bv64));

label_0x5adb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_718;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5ae1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5ae6:
t_1697 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_719;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1697, 4bv64)), t_1697)), 2bv64)), (XOR_64((RSHIFT_64(t_1697, 4bv64)), t_1697)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1697, 4bv64)), t_1697)), 2bv64)), (XOR_64((RSHIFT_64(t_1697, 4bv64)), t_1697)))))[1:0]));
SF := t_1697[64:63];
ZF := bool2bv(0bv64 == t_1697);

label_0x5ae9:
if (bv2bool(ZF)) {
  goto label_0x5aec;
}

label_0x5aeb:
assume false;

label_0x5aec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2056bv64));

label_0x5af4:
origDEST_1701 := RAX;
origCOUNT_1702 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), CF, LSHIFT_64(origDEST_1701, (MINUS_64(64bv64, origCOUNT_1702)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 1bv64)), origDEST_1701[64:63], unconstrained_720));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), AF, unconstrained_721);

label_0x5af8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5aff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5b03:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2056bv64));

label_0x5b0b:
origDEST_1707 := RCX;
origCOUNT_1708 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), CF, LSHIFT_64(origDEST_1707, (MINUS_64(64bv64, origCOUNT_1708)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 1bv64)), origDEST_1707[64:63], unconstrained_722));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1708 == 0bv64)), AF, unconstrained_723);

label_0x5b0f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_724;
SF := unconstrained_725;
AF := unconstrained_726;
PF := unconstrained_727;

label_0x5b13:
if (bv2bool(CF)) {
  goto label_0x5b16;
}

label_0x5b15:
assume false;

label_0x5b16:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2056bv64));

label_0x5b1e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1516bv64)));

label_0x5b25:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5b27:
RAX := (0bv32 ++ 4bv32);

label_0x5b2c:
t_1713 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1713[64:0];
OF := bool2bv(t_1713 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1713 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_728;
SF := unconstrained_729;
ZF := unconstrained_730;
AF := unconstrained_731;

label_0x5b30:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5b35:
t1_1715 := RCX;
t2_1716 := RAX;
RCX := PLUS_64(RCX, t2_1716);
CF := bool2bv(LT_64(RCX, t1_1715));
OF := AND_1((bool2bv((t1_1715[64:63]) == (t2_1716[64:63]))), (XOR_1((t1_1715[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1715)), t2_1716)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5b38:
RAX := RCX;

label_0x5b3b:
RCX := (0bv32 ++ 4bv32);

label_0x5b40:
t_1721 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RCX := t_1721[64:0];
OF := bool2bv(t_1721 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1721 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_732;
SF := unconstrained_733;
ZF := unconstrained_734;
AF := unconstrained_735;

label_0x5b44:
RDX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5b4c:
t1_1723 := RDX;
t2_1724 := RCX;
RDX := PLUS_64(RDX, t2_1724);
CF := bool2bv(LT_64(RDX, t1_1723));
OF := AND_1((bool2bv((t1_1723[64:63]) == (t2_1724[64:63]))), (XOR_1((t1_1723[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1723)), t2_1724)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x5b4f:
RCX := RDX;

label_0x5b52:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5b54:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5b56:
t_1729 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_1729, (RCX[32:0])));
OF := AND_32((XOR_32(t_1729, (RCX[32:0]))), (XOR_32(t_1729, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1729)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5b58:
RCX := (0bv32 ++ 4bv32);

label_0x5b5d:
t_1733 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RCX := t_1733[64:0];
OF := bool2bv(t_1733 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_1733 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_736;
SF := unconstrained_737;
ZF := unconstrained_738;
AF := unconstrained_739;

label_0x5b61:
RDX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5b66:
t1_1735 := RDX;
t2_1736 := RCX;
RDX := PLUS_64(RDX, t2_1736);
CF := bool2bv(LT_64(RDX, t1_1735));
OF := AND_1((bool2bv((t1_1735[64:63]) == (t2_1736[64:63]))), (XOR_1((t1_1735[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_1735)), t2_1736)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x5b69:
RCX := RDX;

label_0x5b6c:
RDX := (0bv32 ++ 4bv32);

label_0x5b71:
t_1741 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RDX := t_1741[64:0];
OF := bool2bv(t_1741 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_1741 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_740;
SF := unconstrained_741;
ZF := unconstrained_742;
AF := unconstrained_743;

label_0x5b75:
R8 := PLUS_64(RSP, 144bv64)[64:0];

label_0x5b7d:
t1_1743 := R8;
t2_1744 := RDX;
R8 := PLUS_64(R8, t2_1744);
CF := bool2bv(LT_64(R8, t1_1743));
OF := AND_1((bool2bv((t1_1743[64:63]) == (t2_1744[64:63]))), (XOR_1((t1_1743[64:63]), (R8[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R8, t1_1743)), t2_1744)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R8, 4bv64)), R8)), 2bv64)), (XOR_64((RSHIFT_64(R8, 4bv64)), R8)))))[1:0]));
SF := R8[64:63];
ZF := bool2bv(0bv64 == R8);

label_0x5b80:
RDX := R8;

label_0x5b83:
RDX := (0bv32 ++ LOAD_LE_32(mem, RDX));

label_0x5b85:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5b87:
t_1749 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RDX[32:0])));
CF := bool2bv(LT_32(t_1749, (RDX[32:0])));
OF := AND_32((XOR_32(t_1749, (RDX[32:0]))), (XOR_32(t_1749, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_1749)), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x5b89:
t_1753 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_1753)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1753, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1753, 4bv32)), t_1753)), 2bv32)), (XOR_32((RSHIFT_32(t_1753, 4bv32)), t_1753)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1753, 4bv32)), t_1753)), 2bv32)), (XOR_32((RSHIFT_32(t_1753, 4bv32)), t_1753)))))[1:0]));
SF := t_1753[32:31];
ZF := bool2bv(0bv32 == t_1753);

label_0x5b8b:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x5ed6;
}

label_0x5b91:
RAX := (0bv32 ++ 4bv32);

label_0x5b96:
t_1757 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1757[64:0];
OF := bool2bv(t_1757 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1757 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_744;
SF := unconstrained_745;
ZF := unconstrained_746;
AF := unconstrained_747;

label_0x5b9a:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5ba2:
t1_1759 := RCX;
t2_1760 := RAX;
RCX := PLUS_64(RCX, t2_1760);
CF := bool2bv(LT_64(RCX, t1_1759));
OF := AND_1((bool2bv((t1_1759[64:63]) == (t2_1760[64:63]))), (XOR_1((t1_1759[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1759)), t2_1760)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5ba5:
RAX := RCX;

label_0x5ba8:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5baa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1520bv64), RAX[32:0]);

label_0x5bb1:
RAX := (0bv32 ++ 4bv32);

label_0x5bb6:
t_1765 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1765[64:0];
OF := bool2bv(t_1765 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1765 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_748;
SF := unconstrained_749;
ZF := unconstrained_750;
AF := unconstrained_751;

label_0x5bba:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5bc2:
t1_1767 := RCX;
t2_1768 := RAX;
RCX := PLUS_64(RCX, t2_1768);
CF := bool2bv(LT_64(RCX, t1_1767));
OF := AND_1((bool2bv((t1_1767[64:63]) == (t2_1768[64:63]))), (XOR_1((t1_1767[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1767)), t2_1768)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5bc5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2064bv64), RCX);

label_0x5bcd:
RAX := (0bv32 ++ 4bv32);

label_0x5bd2:
t_1773 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1773[64:0];
OF := bool2bv(t_1773 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1773 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_752;
SF := unconstrained_753;
ZF := unconstrained_754;
AF := unconstrained_755;

label_0x5bd6:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5bde:
t1_1775 := RCX;
t2_1776 := RAX;
RCX := PLUS_64(RCX, t2_1776);
CF := bool2bv(LT_64(RCX, t1_1775));
OF := AND_1((bool2bv((t1_1775[64:63]) == (t2_1776[64:63]))), (XOR_1((t1_1775[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1775)), t2_1776)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5be1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2072bv64), RCX);

label_0x5be9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2072bv64));

label_0x5bf1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_756;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5bf7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5bfc:
t_1783 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_757;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1783, 4bv64)), t_1783)), 2bv64)), (XOR_64((RSHIFT_64(t_1783, 4bv64)), t_1783)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1783, 4bv64)), t_1783)), 2bv64)), (XOR_64((RSHIFT_64(t_1783, 4bv64)), t_1783)))))[1:0]));
SF := t_1783[64:63];
ZF := bool2bv(0bv64 == t_1783);

label_0x5bff:
if (bv2bool(ZF)) {
  goto label_0x5c02;
}

label_0x5c01:
assume false;

label_0x5c02:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2072bv64));

label_0x5c0a:
origDEST_1787 := RAX;
origCOUNT_1788 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), CF, LSHIFT_64(origDEST_1787, (MINUS_64(64bv64, origCOUNT_1788)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 1bv64)), origDEST_1787[64:63], unconstrained_758));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1788 == 0bv64)), AF, unconstrained_759);

label_0x5c0e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5c15:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5c19:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2072bv64));

label_0x5c21:
origDEST_1793 := RCX;
origCOUNT_1794 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), CF, LSHIFT_64(origDEST_1793, (MINUS_64(64bv64, origCOUNT_1794)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 1bv64)), origDEST_1793[64:63], unconstrained_760));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1794 == 0bv64)), AF, unconstrained_761);

label_0x5c25:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_762;
SF := unconstrained_763;
AF := unconstrained_764;
PF := unconstrained_765;

label_0x5c29:
if (bv2bool(CF)) {
  goto label_0x5c2c;
}

label_0x5c2b:
assume false;

label_0x5c2c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2072bv64));

label_0x5c34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2064bv64));

label_0x5c3c:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5c3e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5c40:
RAX := (0bv32 ++ 4bv32);

label_0x5c45:
t_1799 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1799[64:0];
OF := bool2bv(t_1799 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1799 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_766;
SF := unconstrained_767;
ZF := unconstrained_768;
AF := unconstrained_769;

label_0x5c49:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5c51:
t1_1801 := RCX;
t2_1802 := RAX;
RCX := PLUS_64(RCX, t2_1802);
CF := bool2bv(LT_64(RCX, t1_1801));
OF := AND_1((bool2bv((t1_1801[64:63]) == (t2_1802[64:63]))), (XOR_1((t1_1801[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1801)), t2_1802)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5c54:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2080bv64), RCX);

label_0x5c5c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2080bv64));

label_0x5c64:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_770;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5c6a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5c6f:
t_1809 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_771;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1809, 4bv64)), t_1809)), 2bv64)), (XOR_64((RSHIFT_64(t_1809, 4bv64)), t_1809)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1809, 4bv64)), t_1809)), 2bv64)), (XOR_64((RSHIFT_64(t_1809, 4bv64)), t_1809)))))[1:0]));
SF := t_1809[64:63];
ZF := bool2bv(0bv64 == t_1809);

label_0x5c72:
if (bv2bool(ZF)) {
  goto label_0x5c75;
}

label_0x5c74:
assume false;

label_0x5c75:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2080bv64));

label_0x5c7d:
origDEST_1813 := RAX;
origCOUNT_1814 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), CF, LSHIFT_64(origDEST_1813, (MINUS_64(64bv64, origCOUNT_1814)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 1bv64)), origDEST_1813[64:63], unconstrained_772));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), AF, unconstrained_773);

label_0x5c81:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5c88:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5c8c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2080bv64));

label_0x5c94:
origDEST_1819 := RCX;
origCOUNT_1820 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), CF, LSHIFT_64(origDEST_1819, (MINUS_64(64bv64, origCOUNT_1820)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 1bv64)), origDEST_1819[64:63], unconstrained_774));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1820 == 0bv64)), AF, unconstrained_775);

label_0x5c98:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_776;
SF := unconstrained_777;
AF := unconstrained_778;
PF := unconstrained_779;

label_0x5c9c:
if (bv2bool(CF)) {
  goto label_0x5c9f;
}

label_0x5c9e:
assume false;

label_0x5c9f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2080bv64));

label_0x5ca7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1520bv64)));

label_0x5cae:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5cb0:
RAX := (0bv32 ++ 4bv32);

label_0x5cb5:
t_1825 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1825[64:0];
OF := bool2bv(t_1825 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1825 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_780;
SF := unconstrained_781;
ZF := unconstrained_782;
AF := unconstrained_783;

label_0x5cb9:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5cbe:
t1_1827 := RCX;
t2_1828 := RAX;
RCX := PLUS_64(RCX, t2_1828);
CF := bool2bv(LT_64(RCX, t1_1827));
OF := AND_1((bool2bv((t1_1827[64:63]) == (t2_1828[64:63]))), (XOR_1((t1_1827[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1827)), t2_1828)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5cc1:
RAX := RCX;

label_0x5cc4:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5cc6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1520bv64), RAX[32:0]);

label_0x5ccd:
RAX := (0bv32 ++ 4bv32);

label_0x5cd2:
t_1833 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1833[64:0];
OF := bool2bv(t_1833 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1833 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_784;
SF := unconstrained_785;
ZF := unconstrained_786;
AF := unconstrained_787;

label_0x5cd6:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5cdb:
t1_1835 := RCX;
t2_1836 := RAX;
RCX := PLUS_64(RCX, t2_1836);
CF := bool2bv(LT_64(RCX, t1_1835));
OF := AND_1((bool2bv((t1_1835[64:63]) == (t2_1836[64:63]))), (XOR_1((t1_1835[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1835)), t2_1836)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5cde:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2088bv64), RCX);

label_0x5ce6:
RAX := (0bv32 ++ 4bv32);

label_0x5ceb:
t_1841 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1841[64:0];
OF := bool2bv(t_1841 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1841 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_788;
SF := unconstrained_789;
ZF := unconstrained_790;
AF := unconstrained_791;

label_0x5cef:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5cf4:
t1_1843 := RCX;
t2_1844 := RAX;
RCX := PLUS_64(RCX, t2_1844);
CF := bool2bv(LT_64(RCX, t1_1843));
OF := AND_1((bool2bv((t1_1843[64:63]) == (t2_1844[64:63]))), (XOR_1((t1_1843[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1843)), t2_1844)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5cf7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2096bv64), RCX);

label_0x5cff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2096bv64));

label_0x5d07:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_792;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5d0d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5d12:
t_1851 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_793;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1851, 4bv64)), t_1851)), 2bv64)), (XOR_64((RSHIFT_64(t_1851, 4bv64)), t_1851)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1851, 4bv64)), t_1851)), 2bv64)), (XOR_64((RSHIFT_64(t_1851, 4bv64)), t_1851)))))[1:0]));
SF := t_1851[64:63];
ZF := bool2bv(0bv64 == t_1851);

label_0x5d15:
if (bv2bool(ZF)) {
  goto label_0x5d18;
}

label_0x5d17:
assume false;

label_0x5d18:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2096bv64));

label_0x5d20:
origDEST_1855 := RAX;
origCOUNT_1856 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), CF, LSHIFT_64(origDEST_1855, (MINUS_64(64bv64, origCOUNT_1856)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 1bv64)), origDEST_1855[64:63], unconstrained_794));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1856 == 0bv64)), AF, unconstrained_795);

label_0x5d24:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5d2b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5d2f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2096bv64));

label_0x5d37:
origDEST_1861 := RCX;
origCOUNT_1862 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), CF, LSHIFT_64(origDEST_1861, (MINUS_64(64bv64, origCOUNT_1862)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 1bv64)), origDEST_1861[64:63], unconstrained_796));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1862 == 0bv64)), AF, unconstrained_797);

label_0x5d3b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_798;
SF := unconstrained_799;
AF := unconstrained_800;
PF := unconstrained_801;

label_0x5d3f:
if (bv2bool(CF)) {
  goto label_0x5d42;
}

label_0x5d41:
assume false;

label_0x5d42:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2096bv64));

label_0x5d4a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2088bv64));

label_0x5d52:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5d54:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5d56:
RAX := (0bv32 ++ 4bv32);

label_0x5d5b:
t_1867 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1867[64:0];
OF := bool2bv(t_1867 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1867 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_802;
SF := unconstrained_803;
ZF := unconstrained_804;
AF := unconstrained_805;

label_0x5d5f:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5d64:
t1_1869 := RCX;
t2_1870 := RAX;
RCX := PLUS_64(RCX, t2_1870);
CF := bool2bv(LT_64(RCX, t1_1869));
OF := AND_1((bool2bv((t1_1869[64:63]) == (t2_1870[64:63]))), (XOR_1((t1_1869[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1869)), t2_1870)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5d67:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2104bv64), RCX);

label_0x5d6f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2104bv64));

label_0x5d77:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_806;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5d7d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5d82:
t_1877 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_807;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1877, 4bv64)), t_1877)), 2bv64)), (XOR_64((RSHIFT_64(t_1877, 4bv64)), t_1877)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1877, 4bv64)), t_1877)), 2bv64)), (XOR_64((RSHIFT_64(t_1877, 4bv64)), t_1877)))))[1:0]));
SF := t_1877[64:63];
ZF := bool2bv(0bv64 == t_1877);

label_0x5d85:
if (bv2bool(ZF)) {
  goto label_0x5d88;
}

label_0x5d87:
assume false;

label_0x5d88:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2104bv64));

label_0x5d90:
origDEST_1881 := RAX;
origCOUNT_1882 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), CF, LSHIFT_64(origDEST_1881, (MINUS_64(64bv64, origCOUNT_1882)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 1bv64)), origDEST_1881[64:63], unconstrained_808));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1882 == 0bv64)), AF, unconstrained_809);

label_0x5d94:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5d9b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5d9f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2104bv64));

label_0x5da7:
origDEST_1887 := RCX;
origCOUNT_1888 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), CF, LSHIFT_64(origDEST_1887, (MINUS_64(64bv64, origCOUNT_1888)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 1bv64)), origDEST_1887[64:63], unconstrained_810));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1888 == 0bv64)), AF, unconstrained_811);

label_0x5dab:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_812;
SF := unconstrained_813;
AF := unconstrained_814;
PF := unconstrained_815;

label_0x5daf:
if (bv2bool(CF)) {
  goto label_0x5db2;
}

label_0x5db1:
assume false;

label_0x5db2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2104bv64));

label_0x5dba:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1520bv64)));

label_0x5dc1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5dc3:
RAX := (0bv32 ++ 4bv32);

label_0x5dc8:
t_1893 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1893[64:0];
OF := bool2bv(t_1893 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1893 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_816;
SF := unconstrained_817;
ZF := unconstrained_818;
AF := unconstrained_819;

label_0x5dcc:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5dd1:
t1_1895 := RCX;
t2_1896 := RAX;
RCX := PLUS_64(RCX, t2_1896);
CF := bool2bv(LT_64(RCX, t1_1895));
OF := AND_1((bool2bv((t1_1895[64:63]) == (t2_1896[64:63]))), (XOR_1((t1_1895[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1895)), t2_1896)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5dd4:
RAX := RCX;

label_0x5dd7:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5dd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1520bv64), RAX[32:0]);

label_0x5de0:
RAX := (0bv32 ++ 4bv32);

label_0x5de5:
t_1901 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1901[64:0];
OF := bool2bv(t_1901 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1901 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_820;
SF := unconstrained_821;
ZF := unconstrained_822;
AF := unconstrained_823;

label_0x5de9:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5dee:
t1_1903 := RCX;
t2_1904 := RAX;
RCX := PLUS_64(RCX, t2_1904);
CF := bool2bv(LT_64(RCX, t1_1903));
OF := AND_1((bool2bv((t1_1903[64:63]) == (t2_1904[64:63]))), (XOR_1((t1_1903[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1903)), t2_1904)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5df1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2112bv64), RCX);

label_0x5df9:
RAX := (0bv32 ++ 4bv32);

label_0x5dfe:
t_1909 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1909[64:0];
OF := bool2bv(t_1909 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1909 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_824;
SF := unconstrained_825;
ZF := unconstrained_826;
AF := unconstrained_827;

label_0x5e02:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5e07:
t1_1911 := RCX;
t2_1912 := RAX;
RCX := PLUS_64(RCX, t2_1912);
CF := bool2bv(LT_64(RCX, t1_1911));
OF := AND_1((bool2bv((t1_1911[64:63]) == (t2_1912[64:63]))), (XOR_1((t1_1911[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1911)), t2_1912)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5e0a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2120bv64), RCX);

label_0x5e12:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2120bv64));

label_0x5e1a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_828;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5e20:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5e25:
t_1919 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_829;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1919, 4bv64)), t_1919)), 2bv64)), (XOR_64((RSHIFT_64(t_1919, 4bv64)), t_1919)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1919, 4bv64)), t_1919)), 2bv64)), (XOR_64((RSHIFT_64(t_1919, 4bv64)), t_1919)))))[1:0]));
SF := t_1919[64:63];
ZF := bool2bv(0bv64 == t_1919);

label_0x5e28:
if (bv2bool(ZF)) {
  goto label_0x5e2b;
}

label_0x5e2a:
assume false;

label_0x5e2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2120bv64));

label_0x5e33:
origDEST_1923 := RAX;
origCOUNT_1924 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), CF, LSHIFT_64(origDEST_1923, (MINUS_64(64bv64, origCOUNT_1924)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 1bv64)), origDEST_1923[64:63], unconstrained_830));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1924 == 0bv64)), AF, unconstrained_831);

label_0x5e37:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5e3e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5e42:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2120bv64));

label_0x5e4a:
origDEST_1929 := RCX;
origCOUNT_1930 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), CF, LSHIFT_64(origDEST_1929, (MINUS_64(64bv64, origCOUNT_1930)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 1bv64)), origDEST_1929[64:63], unconstrained_832));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1930 == 0bv64)), AF, unconstrained_833);

label_0x5e4e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_834;
SF := unconstrained_835;
AF := unconstrained_836;
PF := unconstrained_837;

label_0x5e52:
if (bv2bool(CF)) {
  goto label_0x5e55;
}

label_0x5e54:
assume false;

label_0x5e55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2120bv64));

label_0x5e5d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2112bv64));

label_0x5e65:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5e67:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5e69:
RAX := (0bv32 ++ 4bv32);

label_0x5e6e:
t_1935 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_1935[64:0];
OF := bool2bv(t_1935 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1935 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_838;
SF := unconstrained_839;
ZF := unconstrained_840;
AF := unconstrained_841;

label_0x5e72:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x5e77:
t1_1937 := RCX;
t2_1938 := RAX;
RCX := PLUS_64(RCX, t2_1938);
CF := bool2bv(LT_64(RCX, t1_1937));
OF := AND_1((bool2bv((t1_1937[64:63]) == (t2_1938[64:63]))), (XOR_1((t1_1937[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1937)), t2_1938)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5e7a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2128bv64), RCX);

label_0x5e82:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2128bv64));

label_0x5e8a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_842;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5e90:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5e95:
t_1945 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_843;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1945, 4bv64)), t_1945)), 2bv64)), (XOR_64((RSHIFT_64(t_1945, 4bv64)), t_1945)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1945, 4bv64)), t_1945)), 2bv64)), (XOR_64((RSHIFT_64(t_1945, 4bv64)), t_1945)))))[1:0]));
SF := t_1945[64:63];
ZF := bool2bv(0bv64 == t_1945);

label_0x5e98:
if (bv2bool(ZF)) {
  goto label_0x5e9b;
}

label_0x5e9a:
assume false;

label_0x5e9b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2128bv64));

label_0x5ea3:
origDEST_1949 := RAX;
origCOUNT_1950 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), CF, LSHIFT_64(origDEST_1949, (MINUS_64(64bv64, origCOUNT_1950)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 1bv64)), origDEST_1949[64:63], unconstrained_844));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv64)), AF, unconstrained_845);

label_0x5ea7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5eae:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5eb2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2128bv64));

label_0x5eba:
origDEST_1955 := RCX;
origCOUNT_1956 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), CF, LSHIFT_64(origDEST_1955, (MINUS_64(64bv64, origCOUNT_1956)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 1bv64)), origDEST_1955[64:63], unconstrained_846));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1956 == 0bv64)), AF, unconstrained_847);

label_0x5ebe:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_848;
SF := unconstrained_849;
AF := unconstrained_850;
PF := unconstrained_851;

label_0x5ec2:
if (bv2bool(CF)) {
  goto label_0x5ec5;
}

label_0x5ec4:
assume false;

label_0x5ec5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2128bv64));

label_0x5ecd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1520bv64)));

label_0x5ed4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5ed6:
RAX := (0bv32 ++ 4bv32);

label_0x5edb:
t_1961 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1961[64:0];
OF := bool2bv(t_1961 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1961 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_852;
SF := unconstrained_853;
ZF := unconstrained_854;
AF := unconstrained_855;

label_0x5edf:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x5ee7:
t1_1963 := RCX;
t2_1964 := RAX;
RCX := PLUS_64(RCX, t2_1964);
CF := bool2bv(LT_64(RCX, t1_1963));
OF := AND_1((bool2bv((t1_1963[64:63]) == (t2_1964[64:63]))), (XOR_1((t1_1963[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1963)), t2_1964)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5eea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2136bv64), RCX);

label_0x5ef2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x5efa:
t_1969 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_1969[64:0];
OF := bool2bv(t_1969 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1969 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_856;
SF := unconstrained_857;
ZF := unconstrained_858;
AF := unconstrained_859;

label_0x5efe:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x5f06:
t1_1971 := RCX;
t2_1972 := RAX;
RCX := PLUS_64(RCX, t2_1972);
CF := bool2bv(LT_64(RCX, t1_1971));
OF := AND_1((bool2bv((t1_1971[64:63]) == (t2_1972[64:63]))), (XOR_1((t1_1971[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1971)), t2_1972)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5f09:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2144bv64), RCX);

label_0x5f11:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2144bv64));

label_0x5f19:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_860;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5f1f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5f24:
t_1979 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_861;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)), 2bv64)), (XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)), 2bv64)), (XOR_64((RSHIFT_64(t_1979, 4bv64)), t_1979)))))[1:0]));
SF := t_1979[64:63];
ZF := bool2bv(0bv64 == t_1979);

label_0x5f27:
if (bv2bool(ZF)) {
  goto label_0x5f2a;
}

label_0x5f29:
assume false;

label_0x5f2a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2144bv64));

label_0x5f32:
origDEST_1983 := RAX;
origCOUNT_1984 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), CF, LSHIFT_64(origDEST_1983, (MINUS_64(64bv64, origCOUNT_1984)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 1bv64)), origDEST_1983[64:63], unconstrained_862));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1984 == 0bv64)), AF, unconstrained_863);

label_0x5f36:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5f3d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5f41:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2144bv64));

label_0x5f49:
origDEST_1989 := RCX;
origCOUNT_1990 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), CF, LSHIFT_64(origDEST_1989, (MINUS_64(64bv64, origCOUNT_1990)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 1bv64)), origDEST_1989[64:63], unconstrained_864));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1990 == 0bv64)), AF, unconstrained_865);

label_0x5f4d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_866;
SF := unconstrained_867;
AF := unconstrained_868;
PF := unconstrained_869;

label_0x5f51:
if (bv2bool(CF)) {
  goto label_0x5f54;
}

label_0x5f53:
assume false;

label_0x5f54:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2144bv64));

label_0x5f5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2136bv64));

label_0x5f64:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5f66:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5f68:
RAX := (0bv32 ++ 4bv32);

label_0x5f6d:
t_1995 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_1995[64:0];
OF := bool2bv(t_1995 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_1995 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_870;
SF := unconstrained_871;
ZF := unconstrained_872;
AF := unconstrained_873;

label_0x5f71:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x5f76:
t1_1997 := RCX;
t2_1998 := RAX;
RCX := PLUS_64(RCX, t2_1998);
CF := bool2bv(LT_64(RCX, t1_1997));
OF := AND_1((bool2bv((t1_1997[64:63]) == (t2_1998[64:63]))), (XOR_1((t1_1997[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1997)), t2_1998)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5f79:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2152bv64), RCX);

label_0x5f81:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x5f89:
t_2003 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2003[64:0];
OF := bool2bv(t_2003 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2003 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_874;
SF := unconstrained_875;
ZF := unconstrained_876;
AF := unconstrained_877;

label_0x5f8d:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x5f95:
t1_2005 := RCX;
t2_2006 := RAX;
RCX := PLUS_64(RCX, t2_2006);
CF := bool2bv(LT_64(RCX, t1_2005));
OF := AND_1((bool2bv((t1_2005[64:63]) == (t2_2006[64:63]))), (XOR_1((t1_2005[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2005)), t2_2006)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5f98:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2160bv64), RCX);

label_0x5fa0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2160bv64));

label_0x5fa8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_878;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5fae:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5fb3:
t_2013 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_879;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2013, 4bv64)), t_2013)), 2bv64)), (XOR_64((RSHIFT_64(t_2013, 4bv64)), t_2013)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2013, 4bv64)), t_2013)), 2bv64)), (XOR_64((RSHIFT_64(t_2013, 4bv64)), t_2013)))))[1:0]));
SF := t_2013[64:63];
ZF := bool2bv(0bv64 == t_2013);

label_0x5fb6:
if (bv2bool(ZF)) {
  goto label_0x5fb9;
}

label_0x5fb8:
assume false;

label_0x5fb9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2160bv64));

label_0x5fc1:
origDEST_2017 := RAX;
origCOUNT_2018 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), CF, LSHIFT_64(origDEST_2017, (MINUS_64(64bv64, origCOUNT_2018)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 1bv64)), origDEST_2017[64:63], unconstrained_880));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2018 == 0bv64)), AF, unconstrained_881);

label_0x5fc5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5fcc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5fd0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2160bv64));

label_0x5fd8:
origDEST_2023 := RCX;
origCOUNT_2024 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), CF, LSHIFT_64(origDEST_2023, (MINUS_64(64bv64, origCOUNT_2024)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 1bv64)), origDEST_2023[64:63], unconstrained_882));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2024 == 0bv64)), AF, unconstrained_883);

label_0x5fdc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_884;
SF := unconstrained_885;
AF := unconstrained_886;
PF := unconstrained_887;

label_0x5fe0:
if (bv2bool(CF)) {
  goto label_0x5fe3;
}

label_0x5fe2:
assume false;

label_0x5fe3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2160bv64));

label_0x5feb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2152bv64));

label_0x5ff3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5ff5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5ff7:
RAX := (0bv32 ++ 4bv32);

label_0x5ffc:
t_2029 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_2029[64:0];
OF := bool2bv(t_2029 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2029 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_888;
SF := unconstrained_889;
ZF := unconstrained_890;
AF := unconstrained_891;

label_0x6000:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x6005:
t1_2031 := RCX;
t2_2032 := RAX;
RCX := PLUS_64(RCX, t2_2032);
CF := bool2bv(LT_64(RCX, t1_2031));
OF := AND_1((bool2bv((t1_2031[64:63]) == (t2_2032[64:63]))), (XOR_1((t1_2031[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2031)), t2_2032)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6008:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2168bv64), RCX);

label_0x6010:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x6018:
t_2037 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2037[64:0];
OF := bool2bv(t_2037 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2037 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_892;
SF := unconstrained_893;
ZF := unconstrained_894;
AF := unconstrained_895;

label_0x601c:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x6024:
t1_2039 := RCX;
t2_2040 := RAX;
RCX := PLUS_64(RCX, t2_2040);
CF := bool2bv(LT_64(RCX, t1_2039));
OF := AND_1((bool2bv((t1_2039[64:63]) == (t2_2040[64:63]))), (XOR_1((t1_2039[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2039)), t2_2040)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6027:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2176bv64), RCX);

label_0x602f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2176bv64));

label_0x6037:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_896;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x603d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6042:
t_2047 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_897;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2047, 4bv64)), t_2047)), 2bv64)), (XOR_64((RSHIFT_64(t_2047, 4bv64)), t_2047)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2047, 4bv64)), t_2047)), 2bv64)), (XOR_64((RSHIFT_64(t_2047, 4bv64)), t_2047)))))[1:0]));
SF := t_2047[64:63];
ZF := bool2bv(0bv64 == t_2047);

label_0x6045:
if (bv2bool(ZF)) {
  goto label_0x6048;
}

label_0x6047:
assume false;

label_0x6048:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2176bv64));

label_0x6050:
origDEST_2051 := RAX;
origCOUNT_2052 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), CF, LSHIFT_64(origDEST_2051, (MINUS_64(64bv64, origCOUNT_2052)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 1bv64)), origDEST_2051[64:63], unconstrained_898));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2052 == 0bv64)), AF, unconstrained_899);

label_0x6054:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x605b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x605f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2176bv64));

label_0x6067:
origDEST_2057 := RCX;
origCOUNT_2058 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), CF, LSHIFT_64(origDEST_2057, (MINUS_64(64bv64, origCOUNT_2058)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 1bv64)), origDEST_2057[64:63], unconstrained_900));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), AF, unconstrained_901);

label_0x606b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_902;
SF := unconstrained_903;
AF := unconstrained_904;
PF := unconstrained_905;

label_0x606f:
if (bv2bool(CF)) {
  goto label_0x6072;
}

label_0x6071:
assume false;

label_0x6072:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2176bv64));

label_0x607a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2168bv64));

label_0x6082:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x6084:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6086:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x608d:
t_2063 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2063[32:31]) == (1bv32[32:31]))), (XOR_1((t_2063[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2063)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x608f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x6096:
RAX := (0bv32 ++ 4bv32);

label_0x609b:
t_2067 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_2067[64:0];
OF := bool2bv(t_2067 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2067 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_906;
SF := unconstrained_907;
ZF := unconstrained_908;
AF := unconstrained_909;

label_0x609f:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x60a7:
t1_2069 := RCX;
t2_2070 := RAX;
RCX := PLUS_64(RCX, t2_2070);
CF := bool2bv(LT_64(RCX, t1_2069));
OF := AND_1((bool2bv((t1_2069[64:63]) == (t2_2070[64:63]))), (XOR_1((t1_2069[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2069)), t2_2070)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x60aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2184bv64), RCX);

label_0x60b2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x60ba:
t_2075 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2075[64:0];
OF := bool2bv(t_2075 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2075 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_910;
SF := unconstrained_911;
ZF := unconstrained_912;
AF := unconstrained_913;

label_0x60be:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x60c6:
t1_2077 := RCX;
t2_2078 := RAX;
RCX := PLUS_64(RCX, t2_2078);
CF := bool2bv(LT_64(RCX, t1_2077));
OF := AND_1((bool2bv((t1_2077[64:63]) == (t2_2078[64:63]))), (XOR_1((t1_2077[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2077)), t2_2078)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x60c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2192bv64), RCX);

label_0x60d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2192bv64));

label_0x60d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_914;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x60df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x60e4:
t_2085 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_915;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2085, 4bv64)), t_2085)), 2bv64)), (XOR_64((RSHIFT_64(t_2085, 4bv64)), t_2085)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2085, 4bv64)), t_2085)), 2bv64)), (XOR_64((RSHIFT_64(t_2085, 4bv64)), t_2085)))))[1:0]));
SF := t_2085[64:63];
ZF := bool2bv(0bv64 == t_2085);

label_0x60e7:
if (bv2bool(ZF)) {
  goto label_0x60ea;
}

label_0x60e9:
assume false;

label_0x60ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2192bv64));

label_0x60f2:
origDEST_2089 := RAX;
origCOUNT_2090 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), CF, LSHIFT_64(origDEST_2089, (MINUS_64(64bv64, origCOUNT_2090)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 1bv64)), origDEST_2089[64:63], unconstrained_916));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv64)), AF, unconstrained_917);

label_0x60f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x60fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6101:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2192bv64));

label_0x6109:
origDEST_2095 := RCX;
origCOUNT_2096 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), CF, LSHIFT_64(origDEST_2095, (MINUS_64(64bv64, origCOUNT_2096)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 1bv64)), origDEST_2095[64:63], unconstrained_918));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2096 == 0bv64)), AF, unconstrained_919);

label_0x610d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_920;
SF := unconstrained_921;
AF := unconstrained_922;
PF := unconstrained_923;

label_0x6111:
if (bv2bool(CF)) {
  goto label_0x6114;
}

label_0x6113:
assume false;

label_0x6114:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2192bv64));

label_0x611c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2184bv64));

label_0x6124:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x6126:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6128:
RAX := (0bv32 ++ 4bv32);

label_0x612d:
t_2101 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_2101[64:0];
OF := bool2bv(t_2101 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2101 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_924;
SF := unconstrained_925;
ZF := unconstrained_926;
AF := unconstrained_927;

label_0x6131:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x6136:
t1_2103 := RCX;
t2_2104 := RAX;
RCX := PLUS_64(RCX, t2_2104);
CF := bool2bv(LT_64(RCX, t1_2103));
OF := AND_1((bool2bv((t1_2103[64:63]) == (t2_2104[64:63]))), (XOR_1((t1_2103[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2103)), t2_2104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6139:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2200bv64), RCX);

label_0x6141:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x6149:
t_2109 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2109[64:0];
OF := bool2bv(t_2109 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2109 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_928;
SF := unconstrained_929;
ZF := unconstrained_930;
AF := unconstrained_931;

label_0x614d:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x6155:
t1_2111 := RCX;
t2_2112 := RAX;
RCX := PLUS_64(RCX, t2_2112);
CF := bool2bv(LT_64(RCX, t1_2111));
OF := AND_1((bool2bv((t1_2111[64:63]) == (t2_2112[64:63]))), (XOR_1((t1_2111[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2111)), t2_2112)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6158:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2208bv64), RCX);

label_0x6160:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2208bv64));

label_0x6168:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_932;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x616e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6173:
t_2119 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_933;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2119, 4bv64)), t_2119)), 2bv64)), (XOR_64((RSHIFT_64(t_2119, 4bv64)), t_2119)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2119, 4bv64)), t_2119)), 2bv64)), (XOR_64((RSHIFT_64(t_2119, 4bv64)), t_2119)))))[1:0]));
SF := t_2119[64:63];
ZF := bool2bv(0bv64 == t_2119);

label_0x6176:
if (bv2bool(ZF)) {
  goto label_0x6179;
}

label_0x6178:
assume false;

label_0x6179:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2208bv64));

label_0x6181:
origDEST_2123 := RAX;
origCOUNT_2124 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), CF, LSHIFT_64(origDEST_2123, (MINUS_64(64bv64, origCOUNT_2124)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 1bv64)), origDEST_2123[64:63], unconstrained_934));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), AF, unconstrained_935);

label_0x6185:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x618c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6190:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2208bv64));

label_0x6198:
origDEST_2129 := RCX;
origCOUNT_2130 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), CF, LSHIFT_64(origDEST_2129, (MINUS_64(64bv64, origCOUNT_2130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 1bv64)), origDEST_2129[64:63], unconstrained_936));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2130 == 0bv64)), AF, unconstrained_937);

label_0x619c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_938;
SF := unconstrained_939;
AF := unconstrained_940;
PF := unconstrained_941;

label_0x61a0:
if (bv2bool(CF)) {
  goto label_0x61a3;
}

label_0x61a2:
assume false;

label_0x61a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2208bv64));

label_0x61ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2200bv64));

label_0x61b3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x61b5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x61b7:
RAX := (0bv32 ++ 4bv32);

label_0x61bc:
t_2135 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_2135[64:0];
OF := bool2bv(t_2135 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2135 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_942;
SF := unconstrained_943;
ZF := unconstrained_944;
AF := unconstrained_945;

label_0x61c0:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x61c5:
t1_2137 := RCX;
t2_2138 := RAX;
RCX := PLUS_64(RCX, t2_2138);
CF := bool2bv(LT_64(RCX, t1_2137));
OF := AND_1((bool2bv((t1_2137[64:63]) == (t2_2138[64:63]))), (XOR_1((t1_2137[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2137)), t2_2138)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x61c8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2216bv64), RCX);

label_0x61d0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x61d8:
t_2143 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2143[64:0];
OF := bool2bv(t_2143 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2143 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_946;
SF := unconstrained_947;
ZF := unconstrained_948;
AF := unconstrained_949;

label_0x61dc:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x61e4:
t1_2145 := RCX;
t2_2146 := RAX;
RCX := PLUS_64(RCX, t2_2146);
CF := bool2bv(LT_64(RCX, t1_2145));
OF := AND_1((bool2bv((t1_2145[64:63]) == (t2_2146[64:63]))), (XOR_1((t1_2145[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2145)), t2_2146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x61e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2224bv64), RCX);

label_0x61ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2224bv64));

label_0x61f7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_950;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x61fd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6202:
t_2153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_951;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2153, 4bv64)), t_2153)), 2bv64)), (XOR_64((RSHIFT_64(t_2153, 4bv64)), t_2153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2153, 4bv64)), t_2153)), 2bv64)), (XOR_64((RSHIFT_64(t_2153, 4bv64)), t_2153)))))[1:0]));
SF := t_2153[64:63];
ZF := bool2bv(0bv64 == t_2153);

label_0x6205:
if (bv2bool(ZF)) {
  goto label_0x6208;
}

label_0x6207:
assume false;

label_0x6208:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2224bv64));

label_0x6210:
origDEST_2157 := RAX;
origCOUNT_2158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), CF, LSHIFT_64(origDEST_2157, (MINUS_64(64bv64, origCOUNT_2158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 1bv64)), origDEST_2157[64:63], unconstrained_952));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2158 == 0bv64)), AF, unconstrained_953);

label_0x6214:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x621b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x621f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2224bv64));

label_0x6227:
origDEST_2163 := RCX;
origCOUNT_2164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), CF, LSHIFT_64(origDEST_2163, (MINUS_64(64bv64, origCOUNT_2164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 1bv64)), origDEST_2163[64:63], unconstrained_954));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2164 == 0bv64)), AF, unconstrained_955);

label_0x622b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_956;
SF := unconstrained_957;
AF := unconstrained_958;
PF := unconstrained_959;

label_0x622f:
if (bv2bool(CF)) {
  goto label_0x6232;
}

label_0x6231:
assume false;

label_0x6232:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2224bv64));

label_0x623a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2216bv64));

label_0x6242:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x6244:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6246:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x624d:
t_2169 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2169[32:31]) == (1bv32[32:31]))), (XOR_1((t_2169[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2169)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x624f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x6256:
RAX := (0bv32 ++ 4bv32);

label_0x625b:
t_2173 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_2173[64:0];
OF := bool2bv(t_2173 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2173 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_960;
SF := unconstrained_961;
ZF := unconstrained_962;
AF := unconstrained_963;

label_0x625f:
RCX := PLUS_64(RSP, 144bv64)[64:0];

label_0x6267:
t1_2175 := RCX;
t2_2176 := RAX;
RCX := PLUS_64(RCX, t2_2176);
CF := bool2bv(LT_64(RCX, t1_2175));
OF := AND_1((bool2bv((t1_2175[64:63]) == (t2_2176[64:63]))), (XOR_1((t1_2175[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2175)), t2_2176)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x626a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2232bv64), RCX);

label_0x6272:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x627a:
t_2181 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2181[64:0];
OF := bool2bv(t_2181 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2181 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_964;
SF := unconstrained_965;
ZF := unconstrained_966;
AF := unconstrained_967;

label_0x627e:
RCX := PLUS_64(RSP, 1008bv64)[64:0];

label_0x6286:
t1_2183 := RCX;
t2_2184 := RAX;
RCX := PLUS_64(RCX, t2_2184);
CF := bool2bv(LT_64(RCX, t1_2183));
OF := AND_1((bool2bv((t1_2183[64:63]) == (t2_2184[64:63]))), (XOR_1((t1_2183[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2183)), t2_2184)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6289:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2240bv64), RCX);

label_0x6291:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2240bv64));

label_0x6299:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_968;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x629f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x62a4:
t_2191 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_969;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2191, 4bv64)), t_2191)), 2bv64)), (XOR_64((RSHIFT_64(t_2191, 4bv64)), t_2191)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2191, 4bv64)), t_2191)), 2bv64)), (XOR_64((RSHIFT_64(t_2191, 4bv64)), t_2191)))))[1:0]));
SF := t_2191[64:63];
ZF := bool2bv(0bv64 == t_2191);

label_0x62a7:
if (bv2bool(ZF)) {
  goto label_0x62aa;
}

label_0x62a9:
assume false;

label_0x62aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2240bv64));

label_0x62b2:
origDEST_2195 := RAX;
origCOUNT_2196 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), CF, LSHIFT_64(origDEST_2195, (MINUS_64(64bv64, origCOUNT_2196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 1bv64)), origDEST_2195[64:63], unconstrained_970));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2196 == 0bv64)), AF, unconstrained_971);

label_0x62b6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x62bd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x62c1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2240bv64));

label_0x62c9:
origDEST_2201 := RCX;
origCOUNT_2202 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), CF, LSHIFT_64(origDEST_2201, (MINUS_64(64bv64, origCOUNT_2202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 1bv64)), origDEST_2201[64:63], unconstrained_972));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2202 == 0bv64)), AF, unconstrained_973);

label_0x62cd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_974;
SF := unconstrained_975;
AF := unconstrained_976;
PF := unconstrained_977;

label_0x62d1:
if (bv2bool(CF)) {
  goto label_0x62d4;
}

label_0x62d3:
assume false;

label_0x62d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2240bv64));

label_0x62dc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2232bv64));

label_0x62e4:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x62e6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x62e8:
RAX := (0bv32 ++ 4bv32);

label_0x62ed:
t_2207 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_2207[64:0];
OF := bool2bv(t_2207 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2207 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_978;
SF := unconstrained_979;
ZF := unconstrained_980;
AF := unconstrained_981;

label_0x62f1:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0x62f6:
t1_2209 := RCX;
t2_2210 := RAX;
RCX := PLUS_64(RCX, t2_2210);
CF := bool2bv(LT_64(RCX, t1_2209));
OF := AND_1((bool2bv((t1_2209[64:63]) == (t2_2210[64:63]))), (XOR_1((t1_2209[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2209)), t2_2210)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x62f9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2248bv64), RCX);

label_0x6301:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x6309:
t_2215 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2215[64:0];
OF := bool2bv(t_2215 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2215 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_982;
SF := unconstrained_983;
ZF := unconstrained_984;
AF := unconstrained_985;

label_0x630d:
RCX := PLUS_64(RSP, 592bv64)[64:0];

label_0x6315:
t1_2217 := RCX;
t2_2218 := RAX;
RCX := PLUS_64(RCX, t2_2218);
CF := bool2bv(LT_64(RCX, t1_2217));
OF := AND_1((bool2bv((t1_2217[64:63]) == (t2_2218[64:63]))), (XOR_1((t1_2217[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2217)), t2_2218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6318:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2256bv64), RCX);

label_0x6320:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2256bv64));

label_0x6328:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_986;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x632e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6333:
t_2225 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_987;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2225, 4bv64)), t_2225)), 2bv64)), (XOR_64((RSHIFT_64(t_2225, 4bv64)), t_2225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2225, 4bv64)), t_2225)), 2bv64)), (XOR_64((RSHIFT_64(t_2225, 4bv64)), t_2225)))))[1:0]));
SF := t_2225[64:63];
ZF := bool2bv(0bv64 == t_2225);

label_0x6336:
if (bv2bool(ZF)) {
  goto label_0x6339;
}

label_0x6338:
assume false;

label_0x6339:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2256bv64));

label_0x6341:
origDEST_2229 := RAX;
origCOUNT_2230 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), CF, LSHIFT_64(origDEST_2229, (MINUS_64(64bv64, origCOUNT_2230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 1bv64)), origDEST_2229[64:63], unconstrained_988));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv64)), AF, unconstrained_989);

label_0x6345:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x634c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6350:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2256bv64));

label_0x6358:
origDEST_2235 := RCX;
origCOUNT_2236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), CF, LSHIFT_64(origDEST_2235, (MINUS_64(64bv64, origCOUNT_2236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 1bv64)), origDEST_2235[64:63], unconstrained_990));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2236 == 0bv64)), AF, unconstrained_991);

label_0x635c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_992;
SF := unconstrained_993;
AF := unconstrained_994;
PF := unconstrained_995;

label_0x6360:
if (bv2bool(CF)) {
  goto label_0x6363;
}

label_0x6362:
assume false;

label_0x6363:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2256bv64));

label_0x636b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2248bv64));

label_0x6373:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x6375:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6377:
RAX := (0bv32 ++ 4bv32);

label_0x637c:
t_2241 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_2241[64:0];
OF := bool2bv(t_2241 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2241 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_996;
SF := unconstrained_997;
ZF := unconstrained_998;
AF := unconstrained_999;

label_0x6380:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0x6385:
t1_2243 := RCX;
t2_2244 := RAX;
RCX := PLUS_64(RCX, t2_2244);
CF := bool2bv(LT_64(RCX, t1_2243));
OF := AND_1((bool2bv((t1_2243[64:63]) == (t2_2244[64:63]))), (XOR_1((t1_2243[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2243)), t2_2244)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6388:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2264bv64), RCX);

label_0x6390:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)))));

label_0x6398:
t_2249 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_2249[64:0];
OF := bool2bv(t_2249 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_2249 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_1000;
SF := unconstrained_1001;
ZF := unconstrained_1002;
AF := unconstrained_1003;

label_0x639c:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x63a4:
t1_2251 := RCX;
t2_2252 := RAX;
RCX := PLUS_64(RCX, t2_2252);
CF := bool2bv(LT_64(RCX, t1_2251));
OF := AND_1((bool2bv((t1_2251[64:63]) == (t2_2252[64:63]))), (XOR_1((t1_2251[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2251)), t2_2252)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x63a7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2272bv64), RCX);

label_0x63af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2272bv64));

label_0x63b7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1004;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x63bd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x63c2:
t_2259 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1005;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2259, 4bv64)), t_2259)), 2bv64)), (XOR_64((RSHIFT_64(t_2259, 4bv64)), t_2259)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2259, 4bv64)), t_2259)), 2bv64)), (XOR_64((RSHIFT_64(t_2259, 4bv64)), t_2259)))))[1:0]));
SF := t_2259[64:63];
ZF := bool2bv(0bv64 == t_2259);

label_0x63c5:
if (bv2bool(ZF)) {
  goto label_0x63c8;
}

label_0x63c7:
assume false;

label_0x63c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2272bv64));

label_0x63d0:
origDEST_2263 := RAX;
origCOUNT_2264 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), CF, LSHIFT_64(origDEST_2263, (MINUS_64(64bv64, origCOUNT_2264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 1bv64)), origDEST_2263[64:63], unconstrained_1006));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2264 == 0bv64)), AF, unconstrained_1007);

label_0x63d4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x63db:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x63df:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2272bv64));

label_0x63e7:
origDEST_2269 := RCX;
origCOUNT_2270 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), CF, LSHIFT_64(origDEST_2269, (MINUS_64(64bv64, origCOUNT_2270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 1bv64)), origDEST_2269[64:63], unconstrained_1008));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2270 == 0bv64)), AF, unconstrained_1009);

label_0x63eb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_1010;
SF := unconstrained_1011;
AF := unconstrained_1012;
PF := unconstrained_1013;

label_0x63ef:
if (bv2bool(CF)) {
  goto label_0x63f2;
}

label_0x63f1:
assume false;

label_0x63f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2272bv64));

label_0x63fa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2264bv64));

label_0x6402:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x6404:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6406:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 1452bv64)));

label_0x640d:
t_2275 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2275[32:31]) == (1bv32[32:31]))), (XOR_1((t_2275[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2275)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x640f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 1452bv64), RAX[32:0]);

label_0x6416:
goto label_0x4241;

label_0x641b:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x6422:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2280bv64), RAX);

label_0x642a:
RAX := PLUS_64(RSP, 1408bv64)[64:0];

label_0x6432:
origDEST_2279 := RAX;
origCOUNT_2280 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), CF, LSHIFT_64(origDEST_2279, (MINUS_64(64bv64, origCOUNT_2280)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 1bv64)), origDEST_2279[64:63], unconstrained_1014));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2280 == 0bv64)), AF, unconstrained_1015);

label_0x6436:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2280bv64));

label_0x643e:
t1_2285 := RCX;
t2_2286 := RAX;
RCX := PLUS_64(RCX, t2_2286);
CF := bool2bv(LT_64(RCX, t1_2285));
OF := AND_1((bool2bv((t1_2285[64:63]) == (t2_2286[64:63]))), (XOR_1((t1_2285[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_2285)), t2_2286)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6441:
mem := STORE_LE_64(mem, PLUS_64(RSP, 2288bv64), RCX);

label_0x6449:
RAX := PLUS_64(RSP, 1408bv64)[64:0];

label_0x6451:
origDEST_2291 := RAX;
origCOUNT_2292 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), CF, LSHIFT_64(origDEST_2291, (MINUS_64(64bv64, origCOUNT_2292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 1bv64)), origDEST_2291[64:63], unconstrained_1016));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2292 == 0bv64)), AF, unconstrained_1017);

label_0x6455:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1018;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6459:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x645b:
mem := STORE_LE_8(mem, PLUS_64(RSP, 2296bv64), RCX[32:0][8:0]);

label_0x6462:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x6465:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 2296bv64))));

label_0x646d:
origDEST_2299 := RAX[32:0][8:0];
origCOUNT_2300 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), CF, RSHIFT_8(origDEST_2299, (MINUS_8(8bv8, origCOUNT_2300)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_1019));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv8)), AF, unconstrained_1020);

label_0x646f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 2288bv64));

label_0x6477:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1021;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x6479:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 2288bv64));

label_0x6481:
t_2307 := RAX;
RAX := MINUS_64(RAX, 22bv64);
CF := bool2bv(LT_64(t_2307, 22bv64));
OF := AND_64((XOR_64(t_2307, 22bv64)), (XOR_64(t_2307, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_2307)), 22bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6485:
RDI := RAX;

label_0x6488:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1022;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x648a:
RCX := (0bv32 ++ 22bv32);

label_0x648f:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x6491:
t1_2311 := RSP;
t2_2312 := 2304bv64;
RSP := PLUS_64(RSP, t2_2312);
CF := bool2bv(LT_64(RSP, t1_2311));
OF := AND_1((bool2bv((t1_2311[64:63]) == (t2_2312[64:63]))), (XOR_1((t1_2311[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_2311)), t2_2312)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x6498:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x6499:

ra_2317 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_1012,origCOUNT_1018,origCOUNT_1038,origCOUNT_1044,origCOUNT_1064,origCOUNT_1070,origCOUNT_1090,origCOUNT_1096,origCOUNT_110,origCOUNT_1116,origCOUNT_1122,origCOUNT_1146,origCOUNT_1152,origCOUNT_116,origCOUNT_1176,origCOUNT_1182,origCOUNT_1206,origCOUNT_1212,origCOUNT_1292,origCOUNT_1298,origCOUNT_1318,origCOUNT_1324,origCOUNT_136,origCOUNT_1360,origCOUNT_1366,origCOUNT_1386,origCOUNT_1392,origCOUNT_14,origCOUNT_142,origCOUNT_1428,origCOUNT_1434,origCOUNT_1454,origCOUNT_1460,origCOUNT_1540,origCOUNT_1546,origCOUNT_1566,origCOUNT_1572,origCOUNT_1608,origCOUNT_1614,origCOUNT_162,origCOUNT_1634,origCOUNT_1640,origCOUNT_1676,origCOUNT_168,origCOUNT_1682,origCOUNT_1702,origCOUNT_1708,origCOUNT_1788,origCOUNT_1794,origCOUNT_1814,origCOUNT_1820,origCOUNT_1856,origCOUNT_1862,origCOUNT_1882,origCOUNT_1888,origCOUNT_1924,origCOUNT_1930,origCOUNT_1950,origCOUNT_1956,origCOUNT_1984,origCOUNT_1990,origCOUNT_2018,origCOUNT_2024,origCOUNT_2052,origCOUNT_2058,origCOUNT_2090,origCOUNT_2096,origCOUNT_2124,origCOUNT_2130,origCOUNT_2158,origCOUNT_2164,origCOUNT_2196,origCOUNT_22,origCOUNT_2202,origCOUNT_2230,origCOUNT_2236,origCOUNT_2264,origCOUNT_2270,origCOUNT_2280,origCOUNT_2292,origCOUNT_2300,origCOUNT_236,origCOUNT_30,origCOUNT_36,origCOUNT_380,origCOUNT_386,origCOUNT_406,origCOUNT_412,origCOUNT_44,origCOUNT_502,origCOUNT_508,origCOUNT_52,origCOUNT_528,origCOUNT_534,origCOUNT_58,origCOUNT_590,origCOUNT_596,origCOUNT_616,origCOUNT_622,origCOUNT_654,origCOUNT_66,origCOUNT_660,origCOUNT_680,origCOUNT_686,origCOUNT_710,origCOUNT_716,origCOUNT_74,origCOUNT_784,origCOUNT_790,origCOUNT_8,origCOUNT_80,origCOUNT_810,origCOUNT_816,origCOUNT_88,origCOUNT_896,origCOUNT_902,origCOUNT_922,origCOUNT_928,origCOUNT_986,origCOUNT_992,origDEST_1011,origDEST_1017,origDEST_1037,origDEST_1043,origDEST_1063,origDEST_1069,origDEST_1089,origDEST_109,origDEST_1095,origDEST_1115,origDEST_1121,origDEST_1145,origDEST_115,origDEST_1151,origDEST_1175,origDEST_1181,origDEST_1205,origDEST_1211,origDEST_1291,origDEST_1297,origDEST_13,origDEST_1317,origDEST_1323,origDEST_135,origDEST_1359,origDEST_1365,origDEST_1385,origDEST_1391,origDEST_141,origDEST_1427,origDEST_1433,origDEST_1453,origDEST_1459,origDEST_1539,origDEST_1545,origDEST_1565,origDEST_1571,origDEST_1607,origDEST_161,origDEST_1613,origDEST_1633,origDEST_1639,origDEST_167,origDEST_1675,origDEST_1681,origDEST_1701,origDEST_1707,origDEST_1787,origDEST_1793,origDEST_1813,origDEST_1819,origDEST_1855,origDEST_1861,origDEST_1881,origDEST_1887,origDEST_1923,origDEST_1929,origDEST_1949,origDEST_1955,origDEST_1983,origDEST_1989,origDEST_2017,origDEST_2023,origDEST_2051,origDEST_2057,origDEST_2089,origDEST_2095,origDEST_21,origDEST_2123,origDEST_2129,origDEST_2157,origDEST_2163,origDEST_2195,origDEST_2201,origDEST_2229,origDEST_2235,origDEST_2263,origDEST_2269,origDEST_2279,origDEST_2291,origDEST_2299,origDEST_235,origDEST_29,origDEST_35,origDEST_379,origDEST_385,origDEST_405,origDEST_411,origDEST_43,origDEST_501,origDEST_507,origDEST_51,origDEST_527,origDEST_533,origDEST_57,origDEST_589,origDEST_595,origDEST_615,origDEST_621,origDEST_65,origDEST_653,origDEST_659,origDEST_679,origDEST_685,origDEST_7,origDEST_709,origDEST_715,origDEST_73,origDEST_783,origDEST_789,origDEST_79,origDEST_809,origDEST_815,origDEST_87,origDEST_895,origDEST_901,origDEST_921,origDEST_927,origDEST_985,origDEST_991,ra_2317,t1_1025,t1_1051,t1_1077,t1_1103,t1_1133,t1_1163,t1_1193,t1_1219,t1_1227,t1_123,t1_1239,t1_1247,t1_1263,t1_1271,t1_1279,t1_1305,t1_1331,t1_1339,t1_1347,t1_1373,t1_1399,t1_1407,t1_1415,t1_1441,t1_1467,t1_1475,t1_1487,t1_149,t1_1495,t1_1511,t1_1519,t1_1527,t1_1553,t1_1579,t1_1587,t1_1595,t1_1621,t1_1647,t1_1655,t1_1663,t1_1689,t1_1715,t1_1723,t1_1735,t1_1743,t1_1759,t1_1767,t1_1775,t1_1801,t1_1827,t1_1835,t1_1843,t1_1869,t1_1895,t1_1903,t1_191,t1_1911,t1_1937,t1_1963,t1_1971,t1_199,t1_1997,t1_2005,t1_2031,t1_2039,t1_2069,t1_207,t1_2077,t1_2103,t1_2111,t1_2137,t1_2145,t1_2175,t1_2183,t1_2209,t1_2217,t1_2243,t1_2251,t1_2285,t1_229,t1_2311,t1_243,t1_249,t1_257,t1_265,t1_271,t1_279,t1_287,t1_293,t1_301,t1_321,t1_327,t1_335,t1_351,t1_359,t1_367,t1_393,t1_443,t1_449,t1_457,t1_473,t1_481,t1_489,t1_515,t1_561,t1_569,t1_577,t1_603,t1_641,t1_667,t1_697,t1_755,t1_763,t1_771,t1_797,t1_867,t1_875,t1_883,t1_909,t1_945,t1_97,t1_973,t1_999,t2_1000,t2_1026,t2_1052,t2_1078,t2_1104,t2_1134,t2_1164,t2_1194,t2_1220,t2_1228,t2_124,t2_1240,t2_1248,t2_1264,t2_1272,t2_1280,t2_1306,t2_1332,t2_1340,t2_1348,t2_1374,t2_1400,t2_1408,t2_1416,t2_1442,t2_1468,t2_1476,t2_1488,t2_1496,t2_150,t2_1512,t2_1520,t2_1528,t2_1554,t2_1580,t2_1588,t2_1596,t2_1622,t2_1648,t2_1656,t2_1664,t2_1690,t2_1716,t2_1724,t2_1736,t2_1744,t2_1760,t2_1768,t2_1776,t2_1802,t2_1828,t2_1836,t2_1844,t2_1870,t2_1896,t2_1904,t2_1912,t2_192,t2_1938,t2_1964,t2_1972,t2_1998,t2_200,t2_2006,t2_2032,t2_2040,t2_2070,t2_2078,t2_208,t2_2104,t2_2112,t2_2138,t2_2146,t2_2176,t2_2184,t2_2210,t2_2218,t2_2244,t2_2252,t2_2286,t2_230,t2_2312,t2_244,t2_250,t2_258,t2_266,t2_272,t2_280,t2_288,t2_294,t2_302,t2_322,t2_328,t2_336,t2_352,t2_360,t2_368,t2_394,t2_444,t2_450,t2_458,t2_474,t2_482,t2_490,t2_516,t2_562,t2_570,t2_578,t2_604,t2_642,t2_668,t2_698,t2_756,t2_764,t2_772,t2_798,t2_868,t2_876,t2_884,t2_910,t2_946,t2_974,t2_98,t_1,t_1007,t_1023,t_1033,t_1049,t_105,t_1059,t_1075,t_1085,t_1101,t_1111,t_1127,t_1131,t_1141,t_1157,t_1161,t_1171,t_1187,t_1191,t_1201,t_121,t_1217,t_1225,t_1233,t_1237,t_1245,t_1253,t_1257,t_1261,t_1269,t_1277,t_1287,t_1303,t_131,t_1313,t_1329,t_1337,t_1345,t_1355,t_1371,t_1381,t_1397,t_1405,t_1413,t_1423,t_1439,t_1449,t_1465,t_147,t_1473,t_1481,t_1485,t_1493,t_1501,t_1505,t_1509,t_1517,t_1525,t_1535,t_1551,t_1561,t_157,t_1577,t_1585,t_1593,t_1603,t_1619,t_1629,t_1645,t_1653,t_1661,t_1671,t_1687,t_1697,t_1713,t_1721,t_1729,t_173,t_1733,t_1741,t_1749,t_1753,t_1757,t_1765,t_177,t_1773,t_1783,t_1799,t_1809,t_181,t_1825,t_1833,t_1841,t_185,t_1851,t_1867,t_1877,t_189,t_1893,t_1901,t_1909,t_1919,t_1935,t_1945,t_1961,t_1969,t_197,t_1979,t_1995,t_2003,t_2013,t_2029,t_2037,t_2047,t_205,t_2063,t_2067,t_2075,t_2085,t_2101,t_2109,t_2119,t_213,t_2135,t_2143,t_2153,t_2169,t_217,t_2173,t_2181,t_2191,t_2207,t_221,t_2215,t_2225,t_2241,t_2249,t_225,t_2259,t_2275,t_2307,t_241,t_255,t_263,t_277,t_285,t_299,t_3,t_307,t_311,t_315,t_319,t_333,t_341,t_345,t_349,t_357,t_365,t_375,t_391,t_401,t_417,t_421,t_425,t_429,t_433,t_437,t_441,t_455,t_463,t_467,t_471,t_479,t_487,t_497,t_513,t_523,t_539,t_543,t_547,t_551,t_555,t_559,t_567,t_575,t_585,t_601,t_611,t_627,t_631,t_635,t_639,t_649,t_665,t_675,t_691,t_695,t_705,t_721,t_725,t_729,t_733,t_737,t_741,t_745,t_749,t_753,t_761,t_769,t_779,t_795,t_805,t_821,t_825,t_829,t_833,t_837,t_841,t_845,t_849,t_853,t_857,t_861,t_865,t_873,t_881,t_891,t_907,t_917,t_933,t_937,t_941,t_95,t_951,t_955,t_959,t_963,t_967,t_971,t_981,t_997;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_100: bv1;
const unconstrained_1000: bv1;
const unconstrained_1001: bv1;
const unconstrained_1002: bv1;
const unconstrained_1003: bv1;
const unconstrained_1004: bv1;
const unconstrained_1005: bv1;
const unconstrained_1006: bv1;
const unconstrained_1007: bv1;
const unconstrained_1008: bv1;
const unconstrained_1009: bv1;
const unconstrained_101: bv1;
const unconstrained_1010: bv1;
const unconstrained_1011: bv1;
const unconstrained_1012: bv1;
const unconstrained_1013: bv1;
const unconstrained_1014: bv1;
const unconstrained_1015: bv1;
const unconstrained_1016: bv1;
const unconstrained_1017: bv1;
const unconstrained_1018: bv1;
const unconstrained_1019: bv1;
const unconstrained_102: bv1;
const unconstrained_1020: bv1;
const unconstrained_1021: bv1;
const unconstrained_1022: bv1;
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
const unconstrained_732: bv1;
const unconstrained_733: bv1;
const unconstrained_734: bv1;
const unconstrained_735: bv1;
const unconstrained_736: bv1;
const unconstrained_737: bv1;
const unconstrained_738: bv1;
const unconstrained_739: bv1;
const unconstrained_74: bv1;
const unconstrained_740: bv1;
const unconstrained_741: bv1;
const unconstrained_742: bv1;
const unconstrained_743: bv1;
const unconstrained_744: bv1;
const unconstrained_745: bv1;
const unconstrained_746: bv1;
const unconstrained_747: bv1;
const unconstrained_748: bv1;
const unconstrained_749: bv1;
const unconstrained_75: bv1;
const unconstrained_750: bv1;
const unconstrained_751: bv1;
const unconstrained_752: bv1;
const unconstrained_753: bv1;
const unconstrained_754: bv1;
const unconstrained_755: bv1;
const unconstrained_756: bv1;
const unconstrained_757: bv1;
const unconstrained_758: bv1;
const unconstrained_759: bv1;
const unconstrained_76: bv1;
const unconstrained_760: bv1;
const unconstrained_761: bv1;
const unconstrained_762: bv1;
const unconstrained_763: bv1;
const unconstrained_764: bv1;
const unconstrained_765: bv1;
const unconstrained_766: bv1;
const unconstrained_767: bv1;
const unconstrained_768: bv1;
const unconstrained_769: bv1;
const unconstrained_77: bv1;
const unconstrained_770: bv1;
const unconstrained_771: bv1;
const unconstrained_772: bv1;
const unconstrained_773: bv1;
const unconstrained_774: bv1;
const unconstrained_775: bv1;
const unconstrained_776: bv1;
const unconstrained_777: bv1;
const unconstrained_778: bv1;
const unconstrained_779: bv1;
const unconstrained_78: bv1;
const unconstrained_780: bv1;
const unconstrained_781: bv1;
const unconstrained_782: bv1;
const unconstrained_783: bv1;
const unconstrained_784: bv1;
const unconstrained_785: bv1;
const unconstrained_786: bv1;
const unconstrained_787: bv1;
const unconstrained_788: bv1;
const unconstrained_789: bv1;
const unconstrained_79: bv1;
const unconstrained_790: bv1;
const unconstrained_791: bv1;
const unconstrained_792: bv1;
const unconstrained_793: bv1;
const unconstrained_794: bv1;
const unconstrained_795: bv1;
const unconstrained_796: bv1;
const unconstrained_797: bv1;
const unconstrained_798: bv1;
const unconstrained_799: bv1;
const unconstrained_8: bv1;
const unconstrained_80: bv1;
const unconstrained_800: bv1;
const unconstrained_801: bv1;
const unconstrained_802: bv1;
const unconstrained_803: bv1;
const unconstrained_804: bv1;
const unconstrained_805: bv1;
const unconstrained_806: bv1;
const unconstrained_807: bv1;
const unconstrained_808: bv1;
const unconstrained_809: bv1;
const unconstrained_81: bv1;
const unconstrained_810: bv1;
const unconstrained_811: bv1;
const unconstrained_812: bv1;
const unconstrained_813: bv1;
const unconstrained_814: bv1;
const unconstrained_815: bv1;
const unconstrained_816: bv1;
const unconstrained_817: bv1;
const unconstrained_818: bv1;
const unconstrained_819: bv1;
const unconstrained_82: bv1;
const unconstrained_820: bv1;
const unconstrained_821: bv1;
const unconstrained_822: bv1;
const unconstrained_823: bv1;
const unconstrained_824: bv1;
const unconstrained_825: bv1;
const unconstrained_826: bv1;
const unconstrained_827: bv1;
const unconstrained_828: bv1;
const unconstrained_829: bv1;
const unconstrained_83: bv1;
const unconstrained_830: bv1;
const unconstrained_831: bv1;
const unconstrained_832: bv1;
const unconstrained_833: bv1;
const unconstrained_834: bv1;
const unconstrained_835: bv1;
const unconstrained_836: bv1;
const unconstrained_837: bv1;
const unconstrained_838: bv1;
const unconstrained_839: bv1;
const unconstrained_84: bv1;
const unconstrained_840: bv1;
const unconstrained_841: bv1;
const unconstrained_842: bv1;
const unconstrained_843: bv1;
const unconstrained_844: bv1;
const unconstrained_845: bv1;
const unconstrained_846: bv1;
const unconstrained_847: bv1;
const unconstrained_848: bv1;
const unconstrained_849: bv1;
const unconstrained_85: bv1;
const unconstrained_850: bv1;
const unconstrained_851: bv1;
const unconstrained_852: bv1;
const unconstrained_853: bv1;
const unconstrained_854: bv1;
const unconstrained_855: bv1;
const unconstrained_856: bv1;
const unconstrained_857: bv1;
const unconstrained_858: bv1;
const unconstrained_859: bv1;
const unconstrained_86: bv1;
const unconstrained_860: bv1;
const unconstrained_861: bv1;
const unconstrained_862: bv1;
const unconstrained_863: bv1;
const unconstrained_864: bv1;
const unconstrained_865: bv1;
const unconstrained_866: bv1;
const unconstrained_867: bv1;
const unconstrained_868: bv1;
const unconstrained_869: bv1;
const unconstrained_87: bv1;
const unconstrained_870: bv1;
const unconstrained_871: bv1;
const unconstrained_872: bv1;
const unconstrained_873: bv1;
const unconstrained_874: bv1;
const unconstrained_875: bv1;
const unconstrained_876: bv1;
const unconstrained_877: bv1;
const unconstrained_878: bv1;
const unconstrained_879: bv1;
const unconstrained_88: bv1;
const unconstrained_880: bv1;
const unconstrained_881: bv1;
const unconstrained_882: bv1;
const unconstrained_883: bv1;
const unconstrained_884: bv1;
const unconstrained_885: bv1;
const unconstrained_886: bv1;
const unconstrained_887: bv1;
const unconstrained_888: bv1;
const unconstrained_889: bv1;
const unconstrained_89: bv1;
const unconstrained_890: bv1;
const unconstrained_891: bv1;
const unconstrained_892: bv1;
const unconstrained_893: bv1;
const unconstrained_894: bv1;
const unconstrained_895: bv1;
const unconstrained_896: bv1;
const unconstrained_897: bv1;
const unconstrained_898: bv1;
const unconstrained_899: bv1;
const unconstrained_9: bv1;
const unconstrained_90: bv1;
const unconstrained_900: bv1;
const unconstrained_901: bv1;
const unconstrained_902: bv1;
const unconstrained_903: bv1;
const unconstrained_904: bv1;
const unconstrained_905: bv1;
const unconstrained_906: bv1;
const unconstrained_907: bv1;
const unconstrained_908: bv1;
const unconstrained_909: bv1;
const unconstrained_91: bv1;
const unconstrained_910: bv1;
const unconstrained_911: bv1;
const unconstrained_912: bv1;
const unconstrained_913: bv1;
const unconstrained_914: bv1;
const unconstrained_915: bv1;
const unconstrained_916: bv1;
const unconstrained_917: bv1;
const unconstrained_918: bv1;
const unconstrained_919: bv1;
const unconstrained_92: bv1;
const unconstrained_920: bv1;
const unconstrained_921: bv1;
const unconstrained_922: bv1;
const unconstrained_923: bv1;
const unconstrained_924: bv1;
const unconstrained_925: bv1;
const unconstrained_926: bv1;
const unconstrained_927: bv1;
const unconstrained_928: bv1;
const unconstrained_929: bv1;
const unconstrained_93: bv1;
const unconstrained_930: bv1;
const unconstrained_931: bv1;
const unconstrained_932: bv1;
const unconstrained_933: bv1;
const unconstrained_934: bv1;
const unconstrained_935: bv1;
const unconstrained_936: bv1;
const unconstrained_937: bv1;
const unconstrained_938: bv1;
const unconstrained_939: bv1;
const unconstrained_94: bv1;
const unconstrained_940: bv1;
const unconstrained_941: bv1;
const unconstrained_942: bv1;
const unconstrained_943: bv1;
const unconstrained_944: bv1;
const unconstrained_945: bv1;
const unconstrained_946: bv1;
const unconstrained_947: bv1;
const unconstrained_948: bv1;
const unconstrained_949: bv1;
const unconstrained_95: bv1;
const unconstrained_950: bv1;
const unconstrained_951: bv1;
const unconstrained_952: bv1;
const unconstrained_953: bv1;
const unconstrained_954: bv1;
const unconstrained_955: bv1;
const unconstrained_956: bv1;
const unconstrained_957: bv1;
const unconstrained_958: bv1;
const unconstrained_959: bv1;
const unconstrained_96: bv1;
const unconstrained_960: bv1;
const unconstrained_961: bv1;
const unconstrained_962: bv1;
const unconstrained_963: bv1;
const unconstrained_964: bv1;
const unconstrained_965: bv1;
const unconstrained_966: bv1;
const unconstrained_967: bv1;
const unconstrained_968: bv1;
const unconstrained_969: bv1;
const unconstrained_97: bv1;
const unconstrained_970: bv1;
const unconstrained_971: bv1;
const unconstrained_972: bv1;
const unconstrained_973: bv1;
const unconstrained_974: bv1;
const unconstrained_975: bv1;
const unconstrained_976: bv1;
const unconstrained_977: bv1;
const unconstrained_978: bv1;
const unconstrained_979: bv1;
const unconstrained_98: bv1;
const unconstrained_980: bv1;
const unconstrained_981: bv1;
const unconstrained_982: bv1;
const unconstrained_983: bv1;
const unconstrained_984: bv1;
const unconstrained_985: bv1;
const unconstrained_986: bv1;
const unconstrained_987: bv1;
const unconstrained_988: bv1;
const unconstrained_989: bv1;
const unconstrained_99: bv1;
const unconstrained_990: bv1;
const unconstrained_991: bv1;
const unconstrained_992: bv1;
const unconstrained_993: bv1;
const unconstrained_994: bv1;
const unconstrained_995: bv1;
const unconstrained_996: bv1;
const unconstrained_997: bv1;
const unconstrained_998: bv1;
const unconstrained_999: bv1;
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
var origCOUNT_1012: bv64;
var origCOUNT_1018: bv64;
var origCOUNT_1038: bv64;
var origCOUNT_1044: bv64;
var origCOUNT_1064: bv64;
var origCOUNT_1070: bv64;
var origCOUNT_1090: bv64;
var origCOUNT_1096: bv64;
var origCOUNT_110: bv64;
var origCOUNT_1116: bv64;
var origCOUNT_1122: bv64;
var origCOUNT_1146: bv64;
var origCOUNT_1152: bv64;
var origCOUNT_116: bv64;
var origCOUNT_1176: bv64;
var origCOUNT_1182: bv64;
var origCOUNT_1206: bv64;
var origCOUNT_1212: bv64;
var origCOUNT_1292: bv64;
var origCOUNT_1298: bv64;
var origCOUNT_1318: bv64;
var origCOUNT_1324: bv64;
var origCOUNT_136: bv64;
var origCOUNT_1360: bv64;
var origCOUNT_1366: bv64;
var origCOUNT_1386: bv64;
var origCOUNT_1392: bv64;
var origCOUNT_14: bv64;
var origCOUNT_142: bv64;
var origCOUNT_1428: bv64;
var origCOUNT_1434: bv64;
var origCOUNT_1454: bv64;
var origCOUNT_1460: bv64;
var origCOUNT_1540: bv64;
var origCOUNT_1546: bv64;
var origCOUNT_1566: bv64;
var origCOUNT_1572: bv64;
var origCOUNT_1608: bv64;
var origCOUNT_1614: bv64;
var origCOUNT_162: bv64;
var origCOUNT_1634: bv64;
var origCOUNT_1640: bv64;
var origCOUNT_1676: bv64;
var origCOUNT_168: bv64;
var origCOUNT_1682: bv64;
var origCOUNT_1702: bv64;
var origCOUNT_1708: bv64;
var origCOUNT_1788: bv64;
var origCOUNT_1794: bv64;
var origCOUNT_1814: bv64;
var origCOUNT_1820: bv64;
var origCOUNT_1856: bv64;
var origCOUNT_1862: bv64;
var origCOUNT_1882: bv64;
var origCOUNT_1888: bv64;
var origCOUNT_1924: bv64;
var origCOUNT_1930: bv64;
var origCOUNT_1950: bv64;
var origCOUNT_1956: bv64;
var origCOUNT_1984: bv64;
var origCOUNT_1990: bv64;
var origCOUNT_2018: bv64;
var origCOUNT_2024: bv64;
var origCOUNT_2052: bv64;
var origCOUNT_2058: bv64;
var origCOUNT_2090: bv64;
var origCOUNT_2096: bv64;
var origCOUNT_2124: bv64;
var origCOUNT_2130: bv64;
var origCOUNT_2158: bv64;
var origCOUNT_2164: bv64;
var origCOUNT_2196: bv64;
var origCOUNT_22: bv64;
var origCOUNT_2202: bv64;
var origCOUNT_2230: bv64;
var origCOUNT_2236: bv64;
var origCOUNT_2264: bv64;
var origCOUNT_2270: bv64;
var origCOUNT_2280: bv64;
var origCOUNT_2292: bv64;
var origCOUNT_2300: bv8;
var origCOUNT_236: bv32;
var origCOUNT_30: bv64;
var origCOUNT_36: bv64;
var origCOUNT_380: bv64;
var origCOUNT_386: bv64;
var origCOUNT_406: bv64;
var origCOUNT_412: bv64;
var origCOUNT_44: bv64;
var origCOUNT_502: bv64;
var origCOUNT_508: bv64;
var origCOUNT_52: bv64;
var origCOUNT_528: bv64;
var origCOUNT_534: bv64;
var origCOUNT_58: bv64;
var origCOUNT_590: bv64;
var origCOUNT_596: bv64;
var origCOUNT_616: bv64;
var origCOUNT_622: bv64;
var origCOUNT_654: bv64;
var origCOUNT_66: bv64;
var origCOUNT_660: bv64;
var origCOUNT_680: bv64;
var origCOUNT_686: bv64;
var origCOUNT_710: bv64;
var origCOUNT_716: bv64;
var origCOUNT_74: bv64;
var origCOUNT_784: bv64;
var origCOUNT_790: bv64;
var origCOUNT_8: bv64;
var origCOUNT_80: bv64;
var origCOUNT_810: bv64;
var origCOUNT_816: bv64;
var origCOUNT_88: bv64;
var origCOUNT_896: bv64;
var origCOUNT_902: bv64;
var origCOUNT_922: bv64;
var origCOUNT_928: bv64;
var origCOUNT_986: bv64;
var origCOUNT_992: bv64;
var origDEST_1011: bv64;
var origDEST_1017: bv64;
var origDEST_1037: bv64;
var origDEST_1043: bv64;
var origDEST_1063: bv64;
var origDEST_1069: bv64;
var origDEST_1089: bv64;
var origDEST_109: bv64;
var origDEST_1095: bv64;
var origDEST_1115: bv64;
var origDEST_1121: bv64;
var origDEST_1145: bv64;
var origDEST_115: bv64;
var origDEST_1151: bv64;
var origDEST_1175: bv64;
var origDEST_1181: bv64;
var origDEST_1205: bv64;
var origDEST_1211: bv64;
var origDEST_1291: bv64;
var origDEST_1297: bv64;
var origDEST_13: bv64;
var origDEST_1317: bv64;
var origDEST_1323: bv64;
var origDEST_135: bv64;
var origDEST_1359: bv64;
var origDEST_1365: bv64;
var origDEST_1385: bv64;
var origDEST_1391: bv64;
var origDEST_141: bv64;
var origDEST_1427: bv64;
var origDEST_1433: bv64;
var origDEST_1453: bv64;
var origDEST_1459: bv64;
var origDEST_1539: bv64;
var origDEST_1545: bv64;
var origDEST_1565: bv64;
var origDEST_1571: bv64;
var origDEST_1607: bv64;
var origDEST_161: bv64;
var origDEST_1613: bv64;
var origDEST_1633: bv64;
var origDEST_1639: bv64;
var origDEST_167: bv64;
var origDEST_1675: bv64;
var origDEST_1681: bv64;
var origDEST_1701: bv64;
var origDEST_1707: bv64;
var origDEST_1787: bv64;
var origDEST_1793: bv64;
var origDEST_1813: bv64;
var origDEST_1819: bv64;
var origDEST_1855: bv64;
var origDEST_1861: bv64;
var origDEST_1881: bv64;
var origDEST_1887: bv64;
var origDEST_1923: bv64;
var origDEST_1929: bv64;
var origDEST_1949: bv64;
var origDEST_1955: bv64;
var origDEST_1983: bv64;
var origDEST_1989: bv64;
var origDEST_2017: bv64;
var origDEST_2023: bv64;
var origDEST_2051: bv64;
var origDEST_2057: bv64;
var origDEST_2089: bv64;
var origDEST_2095: bv64;
var origDEST_21: bv64;
var origDEST_2123: bv64;
var origDEST_2129: bv64;
var origDEST_2157: bv64;
var origDEST_2163: bv64;
var origDEST_2195: bv64;
var origDEST_2201: bv64;
var origDEST_2229: bv64;
var origDEST_2235: bv64;
var origDEST_2263: bv64;
var origDEST_2269: bv64;
var origDEST_2279: bv64;
var origDEST_2291: bv64;
var origDEST_2299: bv8;
var origDEST_235: bv32;
var origDEST_29: bv64;
var origDEST_35: bv64;
var origDEST_379: bv64;
var origDEST_385: bv64;
var origDEST_405: bv64;
var origDEST_411: bv64;
var origDEST_43: bv64;
var origDEST_501: bv64;
var origDEST_507: bv64;
var origDEST_51: bv64;
var origDEST_527: bv64;
var origDEST_533: bv64;
var origDEST_57: bv64;
var origDEST_589: bv64;
var origDEST_595: bv64;
var origDEST_615: bv64;
var origDEST_621: bv64;
var origDEST_65: bv64;
var origDEST_653: bv64;
var origDEST_659: bv64;
var origDEST_679: bv64;
var origDEST_685: bv64;
var origDEST_7: bv64;
var origDEST_709: bv64;
var origDEST_715: bv64;
var origDEST_73: bv64;
var origDEST_783: bv64;
var origDEST_789: bv64;
var origDEST_79: bv64;
var origDEST_809: bv64;
var origDEST_815: bv64;
var origDEST_87: bv64;
var origDEST_895: bv64;
var origDEST_901: bv64;
var origDEST_921: bv64;
var origDEST_927: bv64;
var origDEST_985: bv64;
var origDEST_991: bv64;
var ra_2317: bv64;
var t1_1025: bv64;
var t1_1051: bv64;
var t1_1077: bv64;
var t1_1103: bv64;
var t1_1133: bv64;
var t1_1163: bv64;
var t1_1193: bv64;
var t1_1219: bv64;
var t1_1227: bv64;
var t1_123: bv64;
var t1_1239: bv64;
var t1_1247: bv64;
var t1_1263: bv64;
var t1_1271: bv64;
var t1_1279: bv64;
var t1_1305: bv64;
var t1_1331: bv64;
var t1_1339: bv64;
var t1_1347: bv64;
var t1_1373: bv64;
var t1_1399: bv64;
var t1_1407: bv64;
var t1_1415: bv64;
var t1_1441: bv64;
var t1_1467: bv64;
var t1_1475: bv64;
var t1_1487: bv64;
var t1_149: bv64;
var t1_1495: bv64;
var t1_1511: bv64;
var t1_1519: bv64;
var t1_1527: bv64;
var t1_1553: bv64;
var t1_1579: bv64;
var t1_1587: bv64;
var t1_1595: bv64;
var t1_1621: bv64;
var t1_1647: bv64;
var t1_1655: bv64;
var t1_1663: bv64;
var t1_1689: bv64;
var t1_1715: bv64;
var t1_1723: bv64;
var t1_1735: bv64;
var t1_1743: bv64;
var t1_1759: bv64;
var t1_1767: bv64;
var t1_1775: bv64;
var t1_1801: bv64;
var t1_1827: bv64;
var t1_1835: bv64;
var t1_1843: bv64;
var t1_1869: bv64;
var t1_1895: bv64;
var t1_1903: bv64;
var t1_191: bv64;
var t1_1911: bv64;
var t1_1937: bv64;
var t1_1963: bv64;
var t1_1971: bv64;
var t1_199: bv64;
var t1_1997: bv64;
var t1_2005: bv64;
var t1_2031: bv64;
var t1_2039: bv64;
var t1_2069: bv64;
var t1_207: bv64;
var t1_2077: bv64;
var t1_2103: bv64;
var t1_2111: bv64;
var t1_2137: bv64;
var t1_2145: bv64;
var t1_2175: bv64;
var t1_2183: bv64;
var t1_2209: bv64;
var t1_2217: bv64;
var t1_2243: bv64;
var t1_2251: bv64;
var t1_2285: bv64;
var t1_229: bv32;
var t1_2311: bv64;
var t1_243: bv64;
var t1_249: bv32;
var t1_257: bv64;
var t1_265: bv64;
var t1_271: bv32;
var t1_279: bv64;
var t1_287: bv64;
var t1_293: bv32;
var t1_301: bv64;
var t1_321: bv64;
var t1_327: bv32;
var t1_335: bv64;
var t1_351: bv64;
var t1_359: bv64;
var t1_367: bv64;
var t1_393: bv64;
var t1_443: bv64;
var t1_449: bv32;
var t1_457: bv64;
var t1_473: bv64;
var t1_481: bv64;
var t1_489: bv64;
var t1_515: bv64;
var t1_561: bv64;
var t1_569: bv64;
var t1_577: bv64;
var t1_603: bv64;
var t1_641: bv64;
var t1_667: bv64;
var t1_697: bv64;
var t1_755: bv64;
var t1_763: bv64;
var t1_771: bv64;
var t1_797: bv64;
var t1_867: bv64;
var t1_875: bv64;
var t1_883: bv64;
var t1_909: bv64;
var t1_945: bv32;
var t1_97: bv64;
var t1_973: bv64;
var t1_999: bv64;
var t2_1000: bv64;
var t2_1026: bv64;
var t2_1052: bv64;
var t2_1078: bv64;
var t2_1104: bv64;
var t2_1134: bv64;
var t2_1164: bv64;
var t2_1194: bv64;
var t2_1220: bv64;
var t2_1228: bv64;
var t2_124: bv64;
var t2_1240: bv64;
var t2_1248: bv64;
var t2_1264: bv64;
var t2_1272: bv64;
var t2_1280: bv64;
var t2_1306: bv64;
var t2_1332: bv64;
var t2_1340: bv64;
var t2_1348: bv64;
var t2_1374: bv64;
var t2_1400: bv64;
var t2_1408: bv64;
var t2_1416: bv64;
var t2_1442: bv64;
var t2_1468: bv64;
var t2_1476: bv64;
var t2_1488: bv64;
var t2_1496: bv64;
var t2_150: bv64;
var t2_1512: bv64;
var t2_1520: bv64;
var t2_1528: bv64;
var t2_1554: bv64;
var t2_1580: bv64;
var t2_1588: bv64;
var t2_1596: bv64;
var t2_1622: bv64;
var t2_1648: bv64;
var t2_1656: bv64;
var t2_1664: bv64;
var t2_1690: bv64;
var t2_1716: bv64;
var t2_1724: bv64;
var t2_1736: bv64;
var t2_1744: bv64;
var t2_1760: bv64;
var t2_1768: bv64;
var t2_1776: bv64;
var t2_1802: bv64;
var t2_1828: bv64;
var t2_1836: bv64;
var t2_1844: bv64;
var t2_1870: bv64;
var t2_1896: bv64;
var t2_1904: bv64;
var t2_1912: bv64;
var t2_192: bv64;
var t2_1938: bv64;
var t2_1964: bv64;
var t2_1972: bv64;
var t2_1998: bv64;
var t2_200: bv64;
var t2_2006: bv64;
var t2_2032: bv64;
var t2_2040: bv64;
var t2_2070: bv64;
var t2_2078: bv64;
var t2_208: bv64;
var t2_2104: bv64;
var t2_2112: bv64;
var t2_2138: bv64;
var t2_2146: bv64;
var t2_2176: bv64;
var t2_2184: bv64;
var t2_2210: bv64;
var t2_2218: bv64;
var t2_2244: bv64;
var t2_2252: bv64;
var t2_2286: bv64;
var t2_230: bv32;
var t2_2312: bv64;
var t2_244: bv64;
var t2_250: bv32;
var t2_258: bv64;
var t2_266: bv64;
var t2_272: bv32;
var t2_280: bv64;
var t2_288: bv64;
var t2_294: bv32;
var t2_302: bv64;
var t2_322: bv64;
var t2_328: bv32;
var t2_336: bv64;
var t2_352: bv64;
var t2_360: bv64;
var t2_368: bv64;
var t2_394: bv64;
var t2_444: bv64;
var t2_450: bv32;
var t2_458: bv64;
var t2_474: bv64;
var t2_482: bv64;
var t2_490: bv64;
var t2_516: bv64;
var t2_562: bv64;
var t2_570: bv64;
var t2_578: bv64;
var t2_604: bv64;
var t2_642: bv64;
var t2_668: bv64;
var t2_698: bv64;
var t2_756: bv64;
var t2_764: bv64;
var t2_772: bv64;
var t2_798: bv64;
var t2_868: bv64;
var t2_876: bv64;
var t2_884: bv64;
var t2_910: bv64;
var t2_946: bv32;
var t2_974: bv64;
var t2_98: bv64;
var t_1: bv64;
var t_1007: bv64;
var t_1023: bv128;
var t_1033: bv64;
var t_1049: bv128;
var t_105: bv64;
var t_1059: bv64;
var t_1075: bv128;
var t_1085: bv64;
var t_1101: bv128;
var t_1111: bv64;
var t_1127: bv32;
var t_1131: bv128;
var t_1141: bv64;
var t_1157: bv32;
var t_1161: bv128;
var t_1171: bv64;
var t_1187: bv32;
var t_1191: bv128;
var t_1201: bv64;
var t_121: bv128;
var t_1217: bv128;
var t_1225: bv128;
var t_1233: bv32;
var t_1237: bv128;
var t_1245: bv128;
var t_1253: bv32;
var t_1257: bv32;
var t_1261: bv128;
var t_1269: bv128;
var t_1277: bv128;
var t_1287: bv64;
var t_1303: bv128;
var t_131: bv64;
var t_1313: bv64;
var t_1329: bv128;
var t_1337: bv128;
var t_1345: bv128;
var t_1355: bv64;
var t_1371: bv128;
var t_1381: bv64;
var t_1397: bv128;
var t_1405: bv128;
var t_1413: bv128;
var t_1423: bv64;
var t_1439: bv128;
var t_1449: bv64;
var t_1465: bv128;
var t_147: bv128;
var t_1473: bv128;
var t_1481: bv32;
var t_1485: bv128;
var t_1493: bv128;
var t_1501: bv32;
var t_1505: bv32;
var t_1509: bv128;
var t_1517: bv128;
var t_1525: bv128;
var t_1535: bv64;
var t_1551: bv128;
var t_1561: bv64;
var t_157: bv64;
var t_1577: bv128;
var t_1585: bv128;
var t_1593: bv128;
var t_1603: bv64;
var t_1619: bv128;
var t_1629: bv64;
var t_1645: bv128;
var t_1653: bv128;
var t_1661: bv128;
var t_1671: bv64;
var t_1687: bv128;
var t_1697: bv64;
var t_1713: bv128;
var t_1721: bv128;
var t_1729: bv32;
var t_173: bv32;
var t_1733: bv128;
var t_1741: bv128;
var t_1749: bv32;
var t_1753: bv32;
var t_1757: bv128;
var t_1765: bv128;
var t_177: bv32;
var t_1773: bv128;
var t_1783: bv64;
var t_1799: bv128;
var t_1809: bv64;
var t_181: bv32;
var t_1825: bv128;
var t_1833: bv128;
var t_1841: bv128;
var t_185: bv32;
var t_1851: bv64;
var t_1867: bv128;
var t_1877: bv64;
var t_189: bv128;
var t_1893: bv128;
var t_1901: bv128;
var t_1909: bv128;
var t_1919: bv64;
var t_1935: bv128;
var t_1945: bv64;
var t_1961: bv128;
var t_1969: bv128;
var t_197: bv128;
var t_1979: bv64;
var t_1995: bv128;
var t_2003: bv128;
var t_2013: bv64;
var t_2029: bv128;
var t_2037: bv128;
var t_2047: bv64;
var t_205: bv128;
var t_2063: bv32;
var t_2067: bv128;
var t_2075: bv128;
var t_2085: bv64;
var t_2101: bv128;
var t_2109: bv128;
var t_2119: bv64;
var t_213: bv32;
var t_2135: bv128;
var t_2143: bv128;
var t_2153: bv64;
var t_2169: bv32;
var t_217: bv32;
var t_2173: bv128;
var t_2181: bv128;
var t_2191: bv64;
var t_2207: bv128;
var t_221: bv32;
var t_2215: bv128;
var t_2225: bv64;
var t_2241: bv128;
var t_2249: bv128;
var t_225: bv32;
var t_2259: bv64;
var t_2275: bv32;
var t_2307: bv64;
var t_241: bv128;
var t_255: bv128;
var t_263: bv128;
var t_277: bv128;
var t_285: bv128;
var t_299: bv128;
var t_3: bv64;
var t_307: bv32;
var t_311: bv32;
var t_315: bv32;
var t_319: bv128;
var t_333: bv128;
var t_341: bv32;
var t_345: bv32;
var t_349: bv128;
var t_357: bv128;
var t_365: bv128;
var t_375: bv64;
var t_391: bv128;
var t_401: bv64;
var t_417: bv32;
var t_421: bv32;
var t_425: bv32;
var t_429: bv32;
var t_433: bv32;
var t_437: bv32;
var t_441: bv128;
var t_455: bv128;
var t_463: bv32;
var t_467: bv32;
var t_471: bv128;
var t_479: bv128;
var t_487: bv128;
var t_497: bv64;
var t_513: bv128;
var t_523: bv64;
var t_539: bv32;
var t_543: bv32;
var t_547: bv32;
var t_551: bv32;
var t_555: bv32;
var t_559: bv128;
var t_567: bv128;
var t_575: bv128;
var t_585: bv64;
var t_601: bv128;
var t_611: bv64;
var t_627: bv32;
var t_631: bv32;
var t_635: bv32;
var t_639: bv128;
var t_649: bv64;
var t_665: bv128;
var t_675: bv64;
var t_691: bv32;
var t_695: bv128;
var t_705: bv64;
var t_721: bv32;
var t_725: bv32;
var t_729: bv32;
var t_733: bv32;
var t_737: bv32;
var t_741: bv32;
var t_745: bv32;
var t_749: bv32;
var t_753: bv128;
var t_761: bv128;
var t_769: bv128;
var t_779: bv64;
var t_795: bv128;
var t_805: bv64;
var t_821: bv32;
var t_825: bv32;
var t_829: bv32;
var t_833: bv32;
var t_837: bv32;
var t_841: bv32;
var t_845: bv32;
var t_849: bv32;
var t_853: bv32;
var t_857: bv32;
var t_861: bv32;
var t_865: bv128;
var t_873: bv128;
var t_881: bv128;
var t_891: bv64;
var t_907: bv128;
var t_917: bv64;
var t_933: bv32;
var t_937: bv32;
var t_941: bv32;
var t_95: bv128;
var t_951: bv32;
var t_955: bv32;
var t_959: bv32;
var t_963: bv32;
var t_967: bv32;
var t_971: bv128;
var t_981: bv64;
var t_997: bv128;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1280bv64);
axiom policy(2064bv64);
axiom policy(6688bv64);
axiom policy(11152bv64);
axiom policy(14480bv64);
axiom policy(16016bv64);
axiom policy(16160bv64);
axiom policy(25760bv64);
