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
axiom _function_addr_low == 3488bv64;
axiom _function_addr_high == 4240bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xda0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xda5:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0xda6:
t_3 := RSP;
RSP := MINUS_64(RSP, 192bv64);
CF := bool2bv(LT_64(t_3, 192bv64));
OF := AND_64((XOR_64(t_3, 192bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 192bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xdad:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xdb4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0xdb9:
RAX := PLUS_64(RSP, 64bv64)[64:0];

label_0xdbe:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0xdc2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0xdc7:
RAX := PLUS_64(RSP, 64bv64)[64:0];

label_0xdcc:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0xdd0:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdd4:
RCX := (0bv32 ++ 3bv32);

label_0xdd9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RCX);

label_0xde1:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xde4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xdec:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0xdef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xdf4:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0xdf9:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0xdfd:
RDX := (0bv32 ++ 16bv32);

label_0xe02:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xe07:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3596bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe0c"} true;
call arbitrary_func();

label_0xe0c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 0bv32);

label_0xe14:
goto label_0xe20;

label_0xe16:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xe1a:
t_29 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_29[32:31]) == (1bv32[32:31]))), (XOR_1((t_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_29)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xe1c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0xe20:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xe28:
t1_33 := RAX;
t2_34 := 344bv64;
RAX := PLUS_64(RAX, t2_34);
CF := bool2bv(LT_64(RAX, t1_33));
OF := AND_1((bool2bv((t1_33[64:63]) == (t2_34[64:63]))), (XOR_1((t1_33[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_33)), t2_34)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe2e:
t1_39 := RAX;
t2_40 := 56bv64;
RAX := PLUS_64(RAX, t2_40);
CF := bool2bv(LT_64(RAX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe32:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xe34:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0xe38:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xf78;
}

label_0xe3e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xe46:
t1_49 := RAX;
t2_50 := 344bv64;
RAX := PLUS_64(RAX, t2_50);
CF := bool2bv(LT_64(RAX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe4c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xe50:
RCX := RAX;

label_0xe53:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3672bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe58"} true;
call arbitrary_func();

label_0xe58:
RAX := LOAD_LE_64(mem, RAX);

label_0xe5b:
t1_55 := RAX;
t2_56 := 5bv64;
RAX := PLUS_64(RAX, t2_56);
CF := bool2bv(LT_64(RAX, t1_55));
OF := AND_1((bool2bv((t1_55[64:63]) == (t2_56[64:63]))), (XOR_1((t1_55[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_55)), t2_56)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe5f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0xe62:
t_61 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))))[1:0]));
SF := t_61[32:31];
ZF := bool2bv(0bv32 == t_61);

label_0xe64:
if (bv2bool(ZF)) {
  goto label_0xf73;
}

label_0xe6a:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xe6f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3700bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe74"} true;
call arbitrary_func();

label_0xe74:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0xe79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xe7e:
t1_65 := RAX;
t2_66 := 104bv64;
RAX := PLUS_64(RAX, t2_66);
CF := bool2bv(LT_64(RAX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe82:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0xe8a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xe92:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe98:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xe9d:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0xea0:
if (bv2bool(ZF)) {
  goto label_0xea3;
}

label_0xea2:
assume false;

label_0xea3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xeab:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_13);

label_0xeaf:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xeb6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xeba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xec2:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_15);

label_0xec6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_16;
SF := unconstrained_17;
AF := unconstrained_18;
PF := unconstrained_19;

label_0xeca:
if (bv2bool(CF)) {
  goto label_0xecd;
}

label_0xecc:
assume false;

label_0xecd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xed5:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0xed8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xee0:
t1_89 := RAX;
t2_90 := 344bv64;
RAX := PLUS_64(RAX, t2_90);
CF := bool2bv(LT_64(RAX, t1_89));
OF := AND_1((bool2bv((t1_89[64:63]) == (t2_90[64:63]))), (XOR_1((t1_89[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_89)), t2_90)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xee6:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xeea:
RCX := RAX;

label_0xeed:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3826bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xef2"} true;
call arbitrary_func();

label_0xef2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0xefa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf02:
t1_95 := RCX;
t2_96 := 344bv64;
RCX := PLUS_64(RCX, t2_96);
CF := bool2bv(LT_64(RCX, t1_95));
OF := AND_1((bool2bv((t1_95[64:63]) == (t2_96[64:63]))), (XOR_1((t1_95[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_95)), t2_96)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xf09:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xf0d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3858bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf12"} true;
call arbitrary_func();

label_0xf12:
RAX := LOAD_LE_64(mem, RAX);

label_0xf15:
t1_101 := RAX;
t2_102 := 20bv64;
RAX := PLUS_64(RAX, t2_102);
CF := bool2bv(LT_64(RAX, t1_101));
OF := AND_1((bool2bv((t1_101[64:63]) == (t2_102[64:63]))), (XOR_1((t1_101[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_101)), t2_102)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf19:
t1_107 := RAX;
t2_108 := 4bv64;
RAX := PLUS_64(RAX, t2_108);
CF := bool2bv(LT_64(RAX, t1_107));
OF := AND_1((bool2bv((t1_107[64:63]) == (t2_108[64:63]))), (XOR_1((t1_107[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_107)), t2_108)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf1d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0xf25:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf2d:
t1_113 := RCX;
t2_114 := 344bv64;
RCX := PLUS_64(RCX, t2_114);
CF := bool2bv(LT_64(RCX, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xf34:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xf38:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3901bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf3d"} true;
call arbitrary_func();

label_0xf3d:
RAX := LOAD_LE_64(mem, RAX);

label_0xf40:
t1_119 := RAX;
t2_120 := 20bv64;
RAX := PLUS_64(RAX, t2_120);
CF := bool2bv(LT_64(RAX, t1_119));
OF := AND_1((bool2bv((t1_119[64:63]) == (t2_120[64:63]))), (XOR_1((t1_119[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_119)), t2_120)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf44:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf4c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0xf51:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xf59:
R9 := LOAD_LE_64(mem, RCX);

label_0xf5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xf64:
R8 := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xf67:
RDX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xf69:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xf6e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3955bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xf73"} true;
call arbitrary_func();

label_0xf73:
goto label_0xe16;

label_0xf78:
mem := STORE_LE_8(mem, PLUS_64(RSP, 100bv64), 1bv8);

label_0xf7d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 0bv32);

label_0xf85:
goto label_0xf91;

label_0xf87:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xf8b:
t_125 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_125[32:31]) == (1bv32[32:31]))), (XOR_1((t_125[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_125)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xf8d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0xf91:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 72bv64)));

label_0xf95:
t_129 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_129)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_129, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))))[1:0]));
SF := t_129[32:31];
ZF := bool2bv(0bv32 == t_129);

label_0xf99:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xfc0;
}

label_0xf9b:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xf9f:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xfa4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4009bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xfa9"} true;
call arbitrary_func();

label_0xfa9:
RCX := RAX;

label_0xfac:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4017bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xfb1"} true;
call arbitrary_func();

label_0xfb1:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xfb4:
t_133 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_133)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_133, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0xfb7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xfbe;
}

label_0xfb9:
mem := STORE_LE_8(mem, PLUS_64(RSP, 100bv64), 0bv8);

label_0xfbe:
goto label_0xf87;

label_0xfc0:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 100bv64))));

label_0xfc5:
t_137 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))))[1:0]));
SF := t_137[32:31];
ZF := bool2bv(0bv32 == t_137);

label_0xfc7:
if (bv2bool(ZF)) {
  goto label_0xf78;
}

label_0xfc9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 0bv32);

label_0xfd1:
goto label_0xfdd;

label_0xfd3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xfd7:
t_141 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_141[32:31]) == (1bv32[32:31]))), (XOR_1((t_141[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_141)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xfd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0xfdd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 72bv64)));

label_0xfe1:
t_145 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_145)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_145, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0xfe5:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xfff;
}

label_0xfe7:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xfeb:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xff0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4085bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xff5"} true;
call arbitrary_func();

label_0xff5:
RCX := RAX;

label_0xff8:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4093bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xffd"} true;
call arbitrary_func();

label_0xffd:
goto label_0xfd3;

label_0xfff:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x1004:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4105bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1009"} true;
call arbitrary_func();

label_0x1009:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x1010:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x1018:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0x101d:
origDEST_149 := RAX;
origCOUNT_150 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_22);

label_0x1021:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1029:
t1_155 := RCX;
t2_156 := RAX;
RCX := PLUS_64(RCX, t2_156);
CF := bool2bv(LT_64(RCX, t1_155));
OF := AND_1((bool2bv((t1_155[64:63]) == (t2_156[64:63]))), (XOR_1((t1_155[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_155)), t2_156)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x102c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RCX);

label_0x1034:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0x1039:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_24);

label_0x103d:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1041:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x1043:
mem := STORE_LE_8(mem, PLUS_64(RSP, 176bv64), RCX[32:0][8:0]);

label_0x104a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x104d:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 176bv64))));

label_0x1055:
origDEST_169 := RAX[32:0][8:0];
origCOUNT_170 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), CF, RSHIFT_8(origDEST_169, (MINUS_8(8bv8, origCOUNT_170)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv8)), AF, unconstrained_27);

label_0x1057:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x105f:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x1061:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1069:
t_177 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_177, 1bv64)), (XOR_64(t_177, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_177)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x106c:
RDI := RAX;

label_0x106f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_29;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1071:
RCX := (0bv32 ++ 1bv32);

label_0x1076:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x1078:
t1_181 := RSP;
t2_182 := 192bv64;
RSP := PLUS_64(RSP, t2_182);
CF := bool2bv(LT_64(RSP, t1_181));
OF := AND_1((bool2bv((t1_181[64:63]) == (t2_182[64:63]))), (XOR_1((t1_181[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_181)), t2_182)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x107f:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x1080:

ra_187 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_14,origCOUNT_150,origCOUNT_162,origCOUNT_170,origCOUNT_22,origCOUNT_78,origCOUNT_8,origCOUNT_84,origDEST_13,origDEST_149,origDEST_161,origDEST_169,origDEST_21,origDEST_7,origDEST_77,origDEST_83,ra_187,t1_101,t1_107,t1_113,t1_119,t1_155,t1_181,t1_33,t1_39,t1_49,t1_55,t1_65,t1_89,t1_95,t2_102,t2_108,t2_114,t2_120,t2_156,t2_182,t2_34,t2_40,t2_50,t2_56,t2_66,t2_90,t2_96,t_1,t_125,t_129,t_133,t_137,t_141,t_145,t_177,t_29,t_3,t_45,t_61,t_73;

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
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
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
var origCOUNT_150: bv64;
var origCOUNT_162: bv64;
var origCOUNT_170: bv8;
var origCOUNT_22: bv64;
var origCOUNT_78: bv64;
var origCOUNT_8: bv64;
var origCOUNT_84: bv64;
var origDEST_13: bv64;
var origDEST_149: bv64;
var origDEST_161: bv64;
var origDEST_169: bv8;
var origDEST_21: bv64;
var origDEST_7: bv64;
var origDEST_77: bv64;
var origDEST_83: bv64;
var ra_187: bv64;
var t1_101: bv64;
var t1_107: bv64;
var t1_113: bv64;
var t1_119: bv64;
var t1_155: bv64;
var t1_181: bv64;
var t1_33: bv64;
var t1_39: bv64;
var t1_49: bv64;
var t1_55: bv64;
var t1_65: bv64;
var t1_89: bv64;
var t1_95: bv64;
var t2_102: bv64;
var t2_108: bv64;
var t2_114: bv64;
var t2_120: bv64;
var t2_156: bv64;
var t2_182: bv64;
var t2_34: bv64;
var t2_40: bv64;
var t2_50: bv64;
var t2_56: bv64;
var t2_66: bv64;
var t2_90: bv64;
var t2_96: bv64;
var t_1: bv64;
var t_125: bv32;
var t_129: bv32;
var t_133: bv32;
var t_137: bv32;
var t_141: bv32;
var t_145: bv32;
var t_177: bv64;
var t_29: bv32;
var t_3: bv64;
var t_45: bv32;
var t_61: bv32;
var t_73: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(208bv64);
axiom policy(688bv64);
axiom policy(1184bv64);
axiom policy(3040bv64);
axiom policy(3232bv64);
axiom policy(3488bv64);
axiom policy(4240bv64);
axiom policy(4816bv64);
axiom policy(5840bv64);
axiom policy(6768bv64);
axiom policy(7760bv64);
axiom policy(8352bv64);
axiom policy(8720bv64);
axiom policy(10656bv64);
axiom policy(12272bv64);
axiom policy(13488bv64);
axiom policy(13872bv64);
