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
axiom _function_addr_high == 1296bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0xa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0xe:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0xf:
t_3 := RSP;
RSP := MINUS_64(RSP, 256bv64);
CF := bool2bv(LT_64(t_3, 256bv64));
OF := AND_64((XOR_64(t_3, 256bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 256bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x16:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x1d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x22:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x27:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0x2b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x30:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x35:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x39:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3d:
RCX := (0bv32 ++ 63bv32);

label_0x42:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RCX);

label_0x4a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x4d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x55:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x58:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x5d:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x62:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x66:
t_29 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 5bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 5bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 5bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), t_29)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_29, (LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))))), 5bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))))[1:0]));
SF := t_29[32:31];
ZF := bool2bv(0bv32 == t_29);

label_0x6e:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x7a;
}

label_0x70:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))))), 6bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0x78:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x90;
}

label_0x7a:
RCX := PLUS_64((PLUS_64(0bv64, 129bv64)), 0bv64)[64:0];

label_0x81:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 134bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x86"} true;
call arbitrary_func();

label_0x86:
RCX := (0bv32 ++ 1bv32);

label_0x8b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 144bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x90"} true;
call arbitrary_func();

label_0x90:
RAX := (0bv32 ++ 8bv32);

label_0x95:
t_37 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_37[64:0];
OF := bool2bv(t_37 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_37 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_9;
SF := unconstrained_10;
ZF := unconstrained_11;
AF := unconstrained_12;

label_0x99:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xa1:
t1_39 := RCX;
t2_40 := RAX;
RCX := PLUS_64(RCX, t2_40);
CF := bool2bv(LT_64(RCX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xa4:
RAX := RCX;

label_0xa7:
RCX := LOAD_LE_64(mem, RAX);

label_0xaa:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 175bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xaf"} true;
call arbitrary_func();

label_0xaf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0xb6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xbe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0xc6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd9:
t_47 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)), 2bv64)), (XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)), 2bv64)), (XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)))))[1:0]));
SF := t_47[64:63];
ZF := bool2bv(0bv64 == t_47);

label_0xdc:
if (bv2bool(ZF)) {
  goto label_0xdf;
}

label_0xde:
assume false;

label_0xdf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xe7:
origDEST_51 := RAX;
origCOUNT_52 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), CF, LSHIFT_64(origDEST_51, (MINUS_64(64bv64, origCOUNT_52)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_52 == 1bv64)), origDEST_51[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), AF, unconstrained_16);

label_0xeb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xfe:
origDEST_57 := RCX;
origCOUNT_58 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_18);

label_0x102:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_19;
SF := unconstrained_20;
AF := unconstrained_21;
PF := unconstrained_22;

label_0x106:
if (bv2bool(CF)) {
  goto label_0x109;
}

label_0x108:
assume false;

label_0x109:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x111:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x118:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11a:
RAX := (0bv32 ++ 8bv32);

label_0x11f:
t_63 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RAX := t_63[64:0];
OF := bool2bv(t_63 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_63 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_23;
SF := unconstrained_24;
ZF := unconstrained_25;
AF := unconstrained_26;

label_0x123:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x12b:
t1_65 := RCX;
t2_66 := RAX;
RCX := PLUS_64(RCX, t2_66);
CF := bool2bv(LT_64(RCX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x12e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RCX);

label_0x136:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x13e:
t1_71 := RAX;
t2_72 := 8bv64;
RAX := PLUS_64(RAX, t2_72);
CF := bool2bv(LT_64(RAX, t1_71));
OF := AND_1((bool2bv((t1_71[64:63]) == (t2_72[64:63]))), (XOR_1((t1_71[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_71)), t2_72)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x142:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x14a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x152:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x158:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15d:
t_79 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))))[1:0]));
SF := t_79[64:63];
ZF := bool2bv(0bv64 == t_79);

label_0x160:
if (bv2bool(ZF)) {
  goto label_0x163;
}

label_0x162:
assume false;

label_0x163:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x16b:
origDEST_83 := RAX;
origCOUNT_84 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_30);

label_0x16f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x176:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x182:
origDEST_89 := RCX;
origCOUNT_90 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, LSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), origDEST_89[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_32);

label_0x186:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x18a:
if (bv2bool(CF)) {
  goto label_0x18d;
}

label_0x18c:
assume false;

label_0x18d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x195:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19d:
RCX := LOAD_LE_64(mem, RCX);

label_0x1a0:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1a3:
RAX := (0bv32 ++ 8bv32);

label_0x1a8:
t_95 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(3bv64[64:63]) ,(1bv64 ++ 3bv64) ,(0bv64 ++ 3bv64)))));
RAX := t_95[64:0];
OF := bool2bv(t_95 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_95 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_37;
SF := unconstrained_38;
ZF := unconstrained_39;
AF := unconstrained_40;

label_0x1ac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x1b4:
t1_97 := RCX;
t2_98 := RAX;
RCX := PLUS_64(RCX, t2_98);
CF := bool2bv(LT_64(RCX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1b7:
RAX := RCX;

label_0x1ba:
RCX := LOAD_LE_64(mem, RAX);

label_0x1bd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 450bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c2"} true;
call arbitrary_func();

label_0x1c2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 168bv64), RAX[32:0]);

label_0x1c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x1d1:
t1_103 := RAX;
t2_104 := 16bv64;
RAX := PLUS_64(RAX, t2_104);
CF := bool2bv(LT_64(RAX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x1dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1e5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1eb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1f0:
t_111 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)), 2bv64)), (XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)), 2bv64)), (XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)))))[1:0]));
SF := t_111[64:63];
ZF := bool2bv(0bv64 == t_111);

label_0x1f3:
if (bv2bool(ZF)) {
  goto label_0x1f6;
}

label_0x1f5:
assume false;

label_0x1f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1fe:
origDEST_115 := RAX;
origCOUNT_116 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), CF, LSHIFT_64(origDEST_115, (MINUS_64(64bv64, origCOUNT_116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_116 == 1bv64)), origDEST_115[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), AF, unconstrained_44);

label_0x202:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x209:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x20d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x215:
origDEST_121 := RCX;
origCOUNT_122 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_46);

label_0x219:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x21d:
if (bv2bool(CF)) {
  goto label_0x220;
}

label_0x21f:
assume false;

label_0x220:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x228:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x22f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x231:
RAX := (0bv32 ++ 8bv32);

label_0x236:
t_127 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RAX := t_127[64:0];
OF := bool2bv(t_127 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_127 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_51;
SF := unconstrained_52;
ZF := unconstrained_53;
AF := unconstrained_54;

label_0x23a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x242:
t1_129 := RCX;
t2_130 := RAX;
RCX := PLUS_64(RCX, t2_130);
CF := bool2bv(LT_64(RCX, t1_129));
OF := AND_1((bool2bv((t1_129[64:63]) == (t2_130[64:63]))), (XOR_1((t1_129[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_129)), t2_130)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x245:
RAX := RCX;

label_0x248:
RCX := LOAD_LE_64(mem, RAX);

label_0x24b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 592bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x250"} true;
call arbitrary_func();

label_0x250:
mem := STORE_LE_32(mem, PLUS_64(RSP, 184bv64), RAX[32:0]);

label_0x257:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x25f:
t1_135 := RAX;
t2_136 := 20bv64;
RAX := PLUS_64(RAX, t2_136);
CF := bool2bv(LT_64(RAX, t1_135));
OF := AND_1((bool2bv((t1_135[64:63]) == (t2_136[64:63]))), (XOR_1((t1_135[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_135)), t2_136)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x263:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x26b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x273:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x279:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x27e:
t_143 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x281:
if (bv2bool(ZF)) {
  goto label_0x284;
}

label_0x283:
assume false;

label_0x284:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x28c:
origDEST_147 := RAX;
origCOUNT_148 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), CF, LSHIFT_64(origDEST_147, (MINUS_64(64bv64, origCOUNT_148)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_148 == 1bv64)), origDEST_147[64:63], unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), AF, unconstrained_58);

label_0x290:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x297:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x29b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a3:
origDEST_153 := RCX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_60);

label_0x2a7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_61;
SF := unconstrained_62;
AF := unconstrained_63;
PF := unconstrained_64;

label_0x2ab:
if (bv2bool(CF)) {
  goto label_0x2ae;
}

label_0x2ad:
assume false;

label_0x2ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2b6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x2bd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2bf:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), 6bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RSP, 272bv64))))), 6bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x2c7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3d4;
}

label_0x2cd:
RAX := (0bv32 ++ 8bv32);

label_0x2d2:
t_163 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(5bv64[64:63]) ,(1bv64 ++ 5bv64) ,(0bv64 ++ 5bv64)))));
RAX := t_163[64:0];
OF := bool2bv(t_163 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_163 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_65;
SF := unconstrained_66;
ZF := unconstrained_67;
AF := unconstrained_68;

label_0x2d6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2de:
t1_165 := RCX;
t2_166 := RAX;
RCX := PLUS_64(RCX, t2_166);
CF := bool2bv(LT_64(RCX, t1_165));
OF := AND_1((bool2bv((t1_165[64:63]) == (t2_166[64:63]))), (XOR_1((t1_165[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_165)), t2_166)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x2e1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RCX);

label_0x2e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x2f1:
t1_171 := RAX;
t2_172 := 24bv64;
RAX := PLUS_64(RAX, t2_172);
CF := bool2bv(LT_64(RAX, t1_171));
OF := AND_1((bool2bv((t1_171[64:63]) == (t2_172[64:63]))), (XOR_1((t1_171[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_171)), t2_172)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x2fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x305:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x310:
t_179 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_70;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))))[1:0]));
SF := t_179[64:63];
ZF := bool2bv(0bv64 == t_179);

label_0x313:
if (bv2bool(ZF)) {
  goto label_0x316;
}

label_0x315:
assume false;

label_0x316:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x31e:
origDEST_183 := RAX;
origCOUNT_184 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_72);

label_0x322:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x329:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x32d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x335:
origDEST_189 := RCX;
origCOUNT_190 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_74);

label_0x339:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_75;
SF := unconstrained_76;
AF := unconstrained_77;
PF := unconstrained_78;

label_0x33d:
if (bv2bool(CF)) {
  goto label_0x340;
}

label_0x33f:
assume false;

label_0x340:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x348:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x350:
RCX := LOAD_LE_64(mem, RCX);

label_0x353:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x356:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x35e:
t1_195 := RAX;
t2_196 := 24bv64;
RAX := PLUS_64(RAX, t2_196);
CF := bool2bv(LT_64(RAX, t1_195));
OF := AND_1((bool2bv((t1_195[64:63]) == (t2_196[64:63]))), (XOR_1((t1_195[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_195)), t2_196)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x362:
RDX := PLUS_64(RSP, 48bv64)[64:0];

label_0x367:
RCX := LOAD_LE_64(mem, RAX);

label_0x36a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 879bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x36f"} true;
call arbitrary_func();

label_0x36f:
t_201 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))))[1:0]));
SF := t_201[32:31];
ZF := bool2bv(0bv32 == t_201);

label_0x371:
if (bv2bool(ZF)) {
  goto label_0x398;
}

label_0x373:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x37b:
t1_205 := RAX;
t2_206 := 24bv64;
RAX := PLUS_64(RAX, t2_206);
CF := bool2bv(LT_64(RAX, t1_205));
OF := AND_1((bool2bv((t1_205[64:63]) == (t2_206[64:63]))), (XOR_1((t1_205[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_205)), t2_206)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37f:
RDX := LOAD_LE_64(mem, RAX);

label_0x382:
RCX := PLUS_64((PLUS_64(0bv64, 905bv64)), 0bv64)[64:0];

label_0x389:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 910bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38e"} true;
call arbitrary_func();

label_0x38e:
RCX := (0bv32 ++ 1bv32);

label_0x393:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 920bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x398"} true;
call arbitrary_func();

label_0x398:
t_211 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1313130bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1313130bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1313130bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), t_211)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_211, (LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))))), 1313130bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))))[1:0]));
SF := t_211[32:31];
ZF := bool2bv(0bv32 == t_211);

label_0x3a0:
if (bv2bool(ZF)) {
  goto label_0x3d2;
}

label_0x3a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x3aa:
t1_215 := RAX;
t2_216 := 24bv64;
RAX := PLUS_64(RAX, t2_216);
CF := bool2bv(LT_64(RAX, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3ae:
R9 := (0bv32 ++ 1313130bv32);

label_0x3b4:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 68bv64)));

label_0x3b9:
RDX := LOAD_LE_64(mem, RAX);

label_0x3bc:
RCX := PLUS_64((PLUS_64(0bv64, 963bv64)), 0bv64)[64:0];

label_0x3c3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 968bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3c8"} true;
call arbitrary_func();

label_0x3c8:
RCX := (0bv32 ++ 1bv32);

label_0x3cd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 978bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3d2"} true;
call arbitrary_func();

label_0x3d2:
goto label_0x43a;

label_0x3d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x3dc:
t1_221 := RAX;
t2_222 := 24bv64;
RAX := PLUS_64(RAX, t2_222);
CF := bool2bv(LT_64(RAX, t1_221));
OF := AND_1((bool2bv((t1_221[64:63]) == (t2_222[64:63]))), (XOR_1((t1_221[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_221)), t2_222)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3e0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x3e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x3f0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_80;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3f6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3fb:
t_229 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))))[1:0]));
SF := t_229[64:63];
ZF := bool2bv(0bv64 == t_229);

label_0x3fe:
if (bv2bool(ZF)) {
  goto label_0x401;
}

label_0x400:
assume false;

label_0x401:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x409:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_83);

label_0x40d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x414:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x418:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x420:
origDEST_239 := RCX;
origCOUNT_240 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_85);

label_0x424:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_86;
SF := unconstrained_87;
AF := unconstrained_88;
PF := unconstrained_89;

label_0x428:
if (bv2bool(CF)) {
  goto label_0x42b;
}

label_0x42a:
assume false;

label_0x42b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x433:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x43a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x442:
t1_245 := RAX;
t2_246 := 16bv64;
RAX := PLUS_64(RAX, t2_246);
CF := bool2bv(LT_64(RAX, t1_245));
OF := AND_1((bool2bv((t1_245[64:63]) == (t2_246[64:63]))), (XOR_1((t1_245[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_245)), t2_246)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x446:
t_251 := MINUS_32((LOAD_LE_32(mem, RAX)), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 1bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_251)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_251, (LOAD_LE_32(mem, RAX)))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)), 2bv32)), (XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)), 2bv32)), (XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)))))[1:0]));
SF := t_251[32:31];
ZF := bool2bv(0bv32 == t_251);

label_0x449:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x48d;
}

label_0x44b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x453:
t1_255 := RAX;
t2_256 := 8bv64;
RAX := PLUS_64(RAX, t2_256);
CF := bool2bv(LT_64(RAX, t1_255));
OF := AND_1((bool2bv((t1_255[64:63]) == (t2_256[64:63]))), (XOR_1((t1_255[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_255)), t2_256)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x457:
RDX := PLUS_64(RSP, 48bv64)[64:0];

label_0x45c:
RCX := LOAD_LE_64(mem, RAX);

label_0x45f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1124bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x464"} true;
call arbitrary_func();

label_0x464:
t_261 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_261, 4bv32)), t_261)), 2bv32)), (XOR_32((RSHIFT_32(t_261, 4bv32)), t_261)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_261, 4bv32)), t_261)), 2bv32)), (XOR_32((RSHIFT_32(t_261, 4bv32)), t_261)))))[1:0]));
SF := t_261[32:31];
ZF := bool2bv(0bv32 == t_261);

label_0x466:
if (bv2bool(ZF)) {
  goto label_0x48d;
}

label_0x468:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x470:
t1_265 := RAX;
t2_266 := 8bv64;
RAX := PLUS_64(RAX, t2_266);
CF := bool2bv(LT_64(RAX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x474:
RDX := LOAD_LE_64(mem, RAX);

label_0x477:
RCX := PLUS_64((PLUS_64(0bv64, 1150bv64)), 0bv64)[64:0];

label_0x47e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1155bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x483"} true;
call arbitrary_func();

label_0x483:
RCX := (0bv32 ++ 1bv32);

label_0x488:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1165bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x48d"} true;
call arbitrary_func();

label_0x48d:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x494:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x49c:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x4a1:
origDEST_271 := RAX;
origCOUNT_272 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), CF, LSHIFT_64(origDEST_271, (MINUS_64(64bv64, origCOUNT_272)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_272 == 1bv64)), origDEST_271[64:63], unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_272 == 0bv64)), AF, unconstrained_92);

label_0x4a5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x4ad:
t1_277 := RCX;
t2_278 := RAX;
RCX := PLUS_64(RCX, t2_278);
CF := bool2bv(LT_64(RCX, t1_277));
OF := AND_1((bool2bv((t1_277[64:63]) == (t2_278[64:63]))), (XOR_1((t1_277[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_277)), t2_278)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x4b0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RCX);

label_0x4b8:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x4bd:
origDEST_283 := RAX;
origCOUNT_284 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), CF, LSHIFT_64(origDEST_283, (MINUS_64(64bv64, origCOUNT_284)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_284 == 1bv64)), origDEST_283[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), AF, unconstrained_94);

label_0x4c1:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c5:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x4c7:
mem := STORE_LE_8(mem, PLUS_64(RSP, 240bv64), RCX[32:0][8:0]);

label_0x4ce:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x4d1:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 240bv64))));

label_0x4d9:
origDEST_291 := RAX[32:0][8:0];
origCOUNT_292 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), CF, RSHIFT_8(origDEST_291, (MINUS_8(8bv8, origCOUNT_292)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv8)), AF, unconstrained_97);

label_0x4db:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x4e3:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_98;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x4e5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x4ed:
t_299 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_299, 2bv64));
OF := AND_64((XOR_64(t_299, 2bv64)), (XOR_64(t_299, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_299)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f1:
RDI := RAX;

label_0x4f4:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_99;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4f6:
RCX := (0bv32 ++ 2bv32);

label_0x4fb:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x4fd:
t1_303 := RSP;
t2_304 := 256bv64;
RSP := PLUS_64(RSP, t2_304);
CF := bool2bv(LT_64(RSP, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x504:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x505:

ra_309 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_116,origCOUNT_122,origCOUNT_14,origCOUNT_148,origCOUNT_154,origCOUNT_184,origCOUNT_190,origCOUNT_22,origCOUNT_234,origCOUNT_240,origCOUNT_272,origCOUNT_284,origCOUNT_292,origCOUNT_52,origCOUNT_58,origCOUNT_8,origCOUNT_84,origCOUNT_90,origDEST_115,origDEST_121,origDEST_13,origDEST_147,origDEST_153,origDEST_183,origDEST_189,origDEST_21,origDEST_233,origDEST_239,origDEST_271,origDEST_283,origDEST_291,origDEST_51,origDEST_57,origDEST_7,origDEST_83,origDEST_89,ra_309,t1_103,t1_129,t1_135,t1_165,t1_171,t1_195,t1_205,t1_215,t1_221,t1_245,t1_255,t1_265,t1_277,t1_303,t1_39,t1_65,t1_71,t1_97,t2_104,t2_130,t2_136,t2_166,t2_172,t2_196,t2_206,t2_216,t2_222,t2_246,t2_256,t2_266,t2_278,t2_304,t2_40,t2_66,t2_72,t2_98,t_1,t_111,t_127,t_143,t_159,t_163,t_179,t_201,t_211,t_229,t_251,t_261,t_29,t_299,t_3,t_33,t_37,t_47,t_63,t_79,t_95;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
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
var R8: bv64;
var R9: bv64;
var R10: bv64;
var R11: bv64;
var RBP: bv64;
var RDI: bv64;
var RSI: bv64;
var R12: bv64;
var R13: bv64;
var R14: bv64;
var R15: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var RAX: bv64;
var RBX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_116: bv64;
var origCOUNT_122: bv64;
var origCOUNT_14: bv64;
var origCOUNT_148: bv64;
var origCOUNT_154: bv64;
var origCOUNT_184: bv64;
var origCOUNT_190: bv64;
var origCOUNT_22: bv64;
var origCOUNT_234: bv64;
var origCOUNT_240: bv64;
var origCOUNT_272: bv64;
var origCOUNT_284: bv64;
var origCOUNT_292: bv8;
var origCOUNT_52: bv64;
var origCOUNT_58: bv64;
var origCOUNT_8: bv64;
var origCOUNT_84: bv64;
var origCOUNT_90: bv64;
var origDEST_115: bv64;
var origDEST_121: bv64;
var origDEST_13: bv64;
var origDEST_147: bv64;
var origDEST_153: bv64;
var origDEST_183: bv64;
var origDEST_189: bv64;
var origDEST_21: bv64;
var origDEST_233: bv64;
var origDEST_239: bv64;
var origDEST_271: bv64;
var origDEST_283: bv64;
var origDEST_291: bv8;
var origDEST_51: bv64;
var origDEST_57: bv64;
var origDEST_7: bv64;
var origDEST_83: bv64;
var origDEST_89: bv64;
var ra_309: bv64;
var t1_103: bv64;
var t1_129: bv64;
var t1_135: bv64;
var t1_165: bv64;
var t1_171: bv64;
var t1_195: bv64;
var t1_205: bv64;
var t1_215: bv64;
var t1_221: bv64;
var t1_245: bv64;
var t1_255: bv64;
var t1_265: bv64;
var t1_277: bv64;
var t1_303: bv64;
var t1_39: bv64;
var t1_65: bv64;
var t1_71: bv64;
var t1_97: bv64;
var t2_104: bv64;
var t2_130: bv64;
var t2_136: bv64;
var t2_166: bv64;
var t2_172: bv64;
var t2_196: bv64;
var t2_206: bv64;
var t2_216: bv64;
var t2_222: bv64;
var t2_246: bv64;
var t2_256: bv64;
var t2_266: bv64;
var t2_278: bv64;
var t2_304: bv64;
var t2_40: bv64;
var t2_66: bv64;
var t2_72: bv64;
var t2_98: bv64;
var t_1: bv64;
var t_111: bv64;
var t_127: bv128;
var t_143: bv64;
var t_159: bv32;
var t_163: bv128;
var t_179: bv64;
var t_201: bv32;
var t_211: bv32;
var t_229: bv64;
var t_251: bv32;
var t_261: bv32;
var t_29: bv32;
var t_299: bv64;
var t_3: bv64;
var t_33: bv32;
var t_37: bv128;
var t_47: bv64;
var t_63: bv128;
var t_79: bv64;
var t_95: bv128;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1296bv64);
axiom policy(2000bv64);
axiom policy(2208bv64);
axiom policy(2352bv64);
axiom policy(2400bv64);
