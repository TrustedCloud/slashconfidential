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
axiom _function_addr_low == 24016bv64;
axiom _function_addr_high == 24884bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x5dd0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x5dd5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x5dda:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x5ddf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x5de4:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x5de5:
t_3 := RSP;
RSP := MINUS_64(RSP, 320bv64);
CF := bool2bv(LT_64(t_3, 320bv64));
OF := AND_64((XOR_64(t_3, 320bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 320bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x5dec:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5df3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x5dfb:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5e00:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0x5e04:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x5e0c:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5e11:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x5e15:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5e19:
RCX := (0bv32 ++ 1023bv32);

label_0x5e1e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RCX);

label_0x5e26:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5e29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5e31:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x5e34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x5e3c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x5e44:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x5e48:
t_29 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), t_29)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_29, (LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0x5e51:
if (bv2bool(ZF)) {
  goto label_0x5e95;
}

label_0x5e53:
t_33 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 344bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 344bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 344bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 344bv64))), t_33)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_33, (LOAD_LE_64(mem, PLUS_64(RSP, 344bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x5e5c:
if (bv2bool(ZF)) {
  goto label_0x5e95;
}

label_0x5e5e:
t_37 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 352bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 352bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 352bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 352bv64))), t_37)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_37, (LOAD_LE_64(mem, PLUS_64(RSP, 352bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x5e67:
if (bv2bool(ZF)) {
  goto label_0x5e95;
}

label_0x5e69:
t_41 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0x5e71:
if (bv2bool(ZF)) {
  goto label_0x5e7d;
}

label_0x5e73:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RSP, 368bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0x5e7b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5e95;
}

label_0x5e7d:
t_49 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), t_49)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_49, (LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))))[1:0]));
SF := t_49[32:31];
ZF := bool2bv(0bv32 == t_49);

label_0x5e85:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x5e95;
}

label_0x5e87:
t_53 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))), t_53)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_53, (LOAD_LE_32(mem, PLUS_64(RSP, 376bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))))[1:0]));
SF := t_53[32:31];
ZF := bool2bv(0bv32 == t_53);

label_0x5e8f:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x5f15;
}

label_0x5e95:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5e9c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x5ea4:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5eac:
origDEST_57 := RAX;
origCOUNT_58 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_10);

label_0x5eb0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x5eb8:
t1_63 := RCX;
t2_64 := RAX;
RCX := PLUS_64(RCX, t2_64);
CF := bool2bv(LT_64(RCX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5ebb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RCX);

label_0x5ec3:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5ecb:
origDEST_69 := RAX;
origCOUNT_70 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), CF, LSHIFT_64(origDEST_69, (MINUS_64(64bv64, origCOUNT_70)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_70 == 1bv64)), origDEST_69[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), AF, unconstrained_12);

label_0x5ecf:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5ed3:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5ed5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 192bv64), RCX[32:0][8:0]);

label_0x5edc:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5edf:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 192bv64))));

label_0x5ee7:
origDEST_77 := RAX[32:0][8:0];
origCOUNT_78 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), CF, RSHIFT_8(origDEST_77, (MINUS_8(8bv8, origCOUNT_78)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), AF, unconstrained_15);

label_0x5ee9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x5ef1:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5ef3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x5efb:
t_85 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_85, 2bv64));
OF := AND_64((XOR_64(t_85, 2bv64)), (XOR_64(t_85, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_85)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5eff:
RDI := RAX;

label_0x5f02:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_17;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5f04:
RCX := (0bv32 ++ 2bv32);

label_0x5f09:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5f0b:
RAX := (0bv32 ++ 4294967294bv32);

label_0x5f10:
goto label_0x62df;

label_0x5f15:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), 0bv64);

label_0x5f1e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), 0bv64);

label_0x5f27:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), 0bv64);

label_0x5f30:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 368bv64)));

label_0x5f38:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 376bv64)));

label_0x5f3f:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5f44:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 24393bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5f49"} true;
call arbitrary_func();

label_0x5f49:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x5f50:
t_89 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_89)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_89, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))))[1:0]));
SF := t_89[32:31];
ZF := bool2bv(0bv32 == t_89);

label_0x5f58:
if (bv2bool(ZF)) {
  goto label_0x5fe0;
}

label_0x5f5e:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5f65:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x5f6d:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5f75:
origDEST_93 := RAX;
origCOUNT_94 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_19);

label_0x5f79:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x5f81:
t1_99 := RCX;
t2_100 := RAX;
RCX := PLUS_64(RCX, t2_100);
CF := bool2bv(LT_64(RCX, t1_99));
OF := AND_1((bool2bv((t1_99[64:63]) == (t2_100[64:63]))), (XOR_1((t1_99[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_99)), t2_100)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5f84:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RCX);

label_0x5f8c:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5f94:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_21);

label_0x5f98:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5f9c:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5f9e:
mem := STORE_LE_8(mem, PLUS_64(RSP, 216bv64), RCX[32:0][8:0]);

label_0x5fa5:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5fa8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 216bv64))));

label_0x5fb0:
origDEST_113 := RAX[32:0][8:0];
origCOUNT_114 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), CF, RSHIFT_8(origDEST_113, (MINUS_8(8bv8, origCOUNT_114)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv8)), AF, unconstrained_24);

label_0x5fb2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x5fba:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5fbc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x5fc4:
t_121 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_121, 2bv64));
OF := AND_64((XOR_64(t_121, 2bv64)), (XOR_64(t_121, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_121)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5fc8:
RDI := RAX;

label_0x5fcb:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_26;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5fcd:
RCX := (0bv32 ++ 2bv32);

label_0x5fd2:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5fd4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x5fdb:
goto label_0x62df;

label_0x5fe0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x5fe8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x5fed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x5ff5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x5ffa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 360bv64)));

label_0x6001:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x6005:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x600d:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x600f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x6013:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x6018:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 24605bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x601d"} true;
call arbitrary_func();

label_0x601d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x6024:
t_125 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_125)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_125, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))))[1:0]));
SF := t_125[32:31];
ZF := bool2bv(0bv32 == t_125);

label_0x602c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x6033;
}

label_0x602e:
goto label_0x6134;

label_0x6033:
t_129 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_129)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_129, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))))[1:0]));
SF := t_129[32:31];
ZF := bool2bv(0bv32 == t_129);

label_0x603b:
if (bv2bool(ZF)) {
  goto label_0x6042;
}

label_0x603d:
goto label_0x6258;

label_0x6042:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x604a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0x604e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x6050:
t_133 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_133, (RCX[32:0])));
OF := AND_32((XOR_32(t_133, (RCX[32:0]))), (XOR_32(t_133, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_133)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6052:
mem := STORE_LE_32(mem, PLUS_64(RSP, 220bv64), RAX[32:0]);

label_0x6059:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x6061:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6067:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x606c:
t_139 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x606f:
if (bv2bool(ZF)) {
  goto label_0x6072;
}

label_0x6071:
assume false;

label_0x6072:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x607a:
origDEST_143 := RAX;
origCOUNT_144 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_30);

label_0x607e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6085:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6089:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x6091:
origDEST_149 := RCX;
origCOUNT_150 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_32);

label_0x6095:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x6099:
if (bv2bool(CF)) {
  goto label_0x609c;
}

label_0x609b:
assume false;

label_0x609c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x60a4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)));

label_0x60ab:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x60ad:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x60b2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 24759bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x60b7"} true;
call arbitrary_func();

label_0x60b7:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x60be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x60c6:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x60ce:
origDEST_155 := RAX;
origCOUNT_156 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_38);

label_0x60d2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x60da:
t1_161 := RCX;
t2_162 := RAX;
RCX := PLUS_64(RCX, t2_162);
CF := bool2bv(LT_64(RCX, t1_161));
OF := AND_1((bool2bv((t1_161[64:63]) == (t2_162[64:63]))), (XOR_1((t1_161[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_161)), t2_162)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x60dd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RCX);

label_0x60e5:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x60ed:
origDEST_167 := RAX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_40);

label_0x60f1:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x60f5:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x60f7:
mem := STORE_LE_8(mem, PLUS_64(RSP, 240bv64), RCX[32:0][8:0]);

label_0x60fe:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x6101:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 240bv64))));

label_0x6109:
origDEST_175 := RAX[32:0][8:0];
origCOUNT_176 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), CF, RSHIFT_8(origDEST_175, (MINUS_8(8bv8, origCOUNT_176)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv8)), AF, unconstrained_43);

label_0x610b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x6113:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x6115:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x611d:
t_183 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_183, 2bv64));
OF := AND_64((XOR_64(t_183, 2bv64)), (XOR_64(t_183, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_183)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6121:
RDI := RAX;

label_0x6124:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_45;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x6126:
RCX := (0bv32 ++ 2bv32);

label_0x612b:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x612d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_46;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x612f:
goto label_0x62df;

label_0x6134:
t_187 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), t_187)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_187, (LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))))[1:0]));
SF := t_187[32:31];
ZF := bool2bv(0bv32 == t_187);

label_0x6139:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x61ce;
}

label_0x613f:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x6144:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 24905bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x6149"} true;
call arbitrary_func();

label_0x6149:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x6150:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x6158:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x6160:
origDEST_191 := RAX;
origCOUNT_192 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_48);

label_0x6164:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x616c:
t1_197 := RCX;
t2_198 := RAX;
RCX := PLUS_64(RCX, t2_198);
CF := bool2bv(LT_64(RCX, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x616f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RCX);

label_0x6177:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x617f:
origDEST_203 := RAX;
origCOUNT_204 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), CF, LSHIFT_64(origDEST_203, (MINUS_64(64bv64, origCOUNT_204)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv64)), origDEST_203[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), AF, unconstrained_50);

label_0x6183:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6187:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x6189:
mem := STORE_LE_8(mem, PLUS_64(RSP, 264bv64), RCX[32:0][8:0]);

label_0x6190:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x6193:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 264bv64))));

label_0x619b:
origDEST_211 := RAX[32:0][8:0];
origCOUNT_212 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), CF, RSHIFT_8(origDEST_211, (MINUS_8(8bv8, origCOUNT_212)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv8)), AF, unconstrained_53);

label_0x619d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x61a5:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x61a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x61af:
t_219 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_219, 2bv64));
OF := AND_64((XOR_64(t_219, 2bv64)), (XOR_64(t_219, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_219)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x61b3:
RDI := RAX;

label_0x61b6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_55;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x61b8:
RCX := (0bv32 ++ 2bv32);

label_0x61bd:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x61bf:
RAX := (0bv32 ++ 4294967289bv32);

label_0x61c4:
goto label_0x62df;

label_0x61c9:
goto label_0x6258;

label_0x61ce:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x61d3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 25048bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x61d8"} true;
call arbitrary_func();

label_0x61d8:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x61df:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0x61e7:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x61ef:
origDEST_223 := RAX;
origCOUNT_224 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), CF, LSHIFT_64(origDEST_223, (MINUS_64(64bv64, origCOUNT_224)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_224 == 1bv64)), origDEST_223[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), AF, unconstrained_57);

label_0x61f3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x61fb:
t1_229 := RCX;
t2_230 := RAX;
RCX := PLUS_64(RCX, t2_230);
CF := bool2bv(LT_64(RCX, t1_229));
OF := AND_1((bool2bv((t1_229[64:63]) == (t2_230[64:63]))), (XOR_1((t1_229[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_229)), t2_230)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x61fe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RCX);

label_0x6206:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x620e:
origDEST_235 := RAX;
origCOUNT_236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), CF, LSHIFT_64(origDEST_235, (MINUS_64(64bv64, origCOUNT_236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv64)), origDEST_235[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), AF, unconstrained_59);

label_0x6212:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6216:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x6218:
mem := STORE_LE_8(mem, PLUS_64(RSP, 288bv64), RCX[32:0][8:0]);

label_0x621f:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x6222:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 288bv64))));

label_0x622a:
origDEST_243 := RAX[32:0][8:0];
origCOUNT_244 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), CF, RSHIFT_8(origDEST_243, (MINUS_8(8bv8, origCOUNT_244)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv8)), AF, unconstrained_62);

label_0x622c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x6234:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x6236:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x623e:
t_251 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_251, 2bv64));
OF := AND_64((XOR_64(t_251, 2bv64)), (XOR_64(t_251, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_251)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6242:
RDI := RAX;

label_0x6245:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_64;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x6247:
RCX := (0bv32 ++ 2bv32);

label_0x624c:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x624e:
RAX := (0bv32 ++ 4294967288bv32);

label_0x6253:
goto label_0x62df;

label_0x6258:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x625d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 25186bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x6262"} true;
call arbitrary_func();

label_0x6262:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x6269:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0x6271:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x6279:
origDEST_255 := RAX;
origCOUNT_256 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), CF, LSHIFT_64(origDEST_255, (MINUS_64(64bv64, origCOUNT_256)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_256 == 1bv64)), origDEST_255[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), AF, unconstrained_66);

label_0x627d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x6285:
t1_261 := RCX;
t2_262 := RAX;
RCX := PLUS_64(RCX, t2_262);
CF := bool2bv(LT_64(RCX, t1_261));
OF := AND_1((bool2bv((t1_261[64:63]) == (t2_262[64:63]))), (XOR_1((t1_261[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_261)), t2_262)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6288:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RCX);

label_0x6290:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x6298:
origDEST_267 := RAX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_68);

label_0x629c:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x62a0:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x62a2:
mem := STORE_LE_8(mem, PLUS_64(RSP, 312bv64), RCX[32:0][8:0]);

label_0x62a9:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x62ac:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 312bv64))));

label_0x62b4:
origDEST_275 := RAX[32:0][8:0];
origCOUNT_276 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), CF, RSHIFT_8(origDEST_275, (MINUS_8(8bv8, origCOUNT_276)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_276 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv8)), AF, unconstrained_71);

label_0x62b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x62be:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x62c0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x62c8:
t_283 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_283, 2bv64));
OF := AND_64((XOR_64(t_283, 2bv64)), (XOR_64(t_283, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_283)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x62cc:
RDI := RAX;

label_0x62cf:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_73;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x62d1:
RCX := (0bv32 ++ 2bv32);

label_0x62d6:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x62d8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x62df:
t1_287 := RSP;
t2_288 := 320bv64;
RSP := PLUS_64(RSP, t2_288);
CF := bool2bv(LT_64(RSP, t1_287));
OF := AND_1((bool2bv((t1_287[64:63]) == (t2_288[64:63]))), (XOR_1((t1_287[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_287)), t2_288)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x62e6:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x62e7:

ra_293 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_114,origCOUNT_14,origCOUNT_144,origCOUNT_150,origCOUNT_156,origCOUNT_168,origCOUNT_176,origCOUNT_192,origCOUNT_204,origCOUNT_212,origCOUNT_22,origCOUNT_224,origCOUNT_236,origCOUNT_244,origCOUNT_256,origCOUNT_268,origCOUNT_276,origCOUNT_58,origCOUNT_70,origCOUNT_78,origCOUNT_8,origCOUNT_94,origDEST_105,origDEST_113,origDEST_13,origDEST_143,origDEST_149,origDEST_155,origDEST_167,origDEST_175,origDEST_191,origDEST_203,origDEST_21,origDEST_211,origDEST_223,origDEST_235,origDEST_243,origDEST_255,origDEST_267,origDEST_275,origDEST_57,origDEST_69,origDEST_7,origDEST_77,origDEST_93,ra_293,t1_161,t1_197,t1_229,t1_261,t1_287,t1_63,t1_99,t2_100,t2_162,t2_198,t2_230,t2_262,t2_288,t2_64,t_1,t_121,t_125,t_129,t_133,t_139,t_183,t_187,t_219,t_251,t_283,t_29,t_3,t_33,t_37,t_41,t_45,t_49,t_53,t_85,t_89;

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
var origCOUNT_106: bv64;
var origCOUNT_114: bv8;
var origCOUNT_14: bv64;
var origCOUNT_144: bv64;
var origCOUNT_150: bv64;
var origCOUNT_156: bv64;
var origCOUNT_168: bv64;
var origCOUNT_176: bv8;
var origCOUNT_192: bv64;
var origCOUNT_204: bv64;
var origCOUNT_212: bv8;
var origCOUNT_22: bv64;
var origCOUNT_224: bv64;
var origCOUNT_236: bv64;
var origCOUNT_244: bv8;
var origCOUNT_256: bv64;
var origCOUNT_268: bv64;
var origCOUNT_276: bv8;
var origCOUNT_58: bv64;
var origCOUNT_70: bv64;
var origCOUNT_78: bv8;
var origCOUNT_8: bv64;
var origCOUNT_94: bv64;
var origDEST_105: bv64;
var origDEST_113: bv8;
var origDEST_13: bv64;
var origDEST_143: bv64;
var origDEST_149: bv64;
var origDEST_155: bv64;
var origDEST_167: bv64;
var origDEST_175: bv8;
var origDEST_191: bv64;
var origDEST_203: bv64;
var origDEST_21: bv64;
var origDEST_211: bv8;
var origDEST_223: bv64;
var origDEST_235: bv64;
var origDEST_243: bv8;
var origDEST_255: bv64;
var origDEST_267: bv64;
var origDEST_275: bv8;
var origDEST_57: bv64;
var origDEST_69: bv64;
var origDEST_7: bv64;
var origDEST_77: bv8;
var origDEST_93: bv64;
var ra_293: bv64;
var t1_161: bv64;
var t1_197: bv64;
var t1_229: bv64;
var t1_261: bv64;
var t1_287: bv64;
var t1_63: bv64;
var t1_99: bv64;
var t2_100: bv64;
var t2_162: bv64;
var t2_198: bv64;
var t2_230: bv64;
var t2_262: bv64;
var t2_288: bv64;
var t2_64: bv64;
var t_1: bv64;
var t_121: bv64;
var t_125: bv32;
var t_129: bv32;
var t_133: bv32;
var t_139: bv64;
var t_183: bv64;
var t_187: bv32;
var t_219: bv64;
var t_251: bv64;
var t_283: bv64;
var t_29: bv64;
var t_3: bv64;
var t_33: bv64;
var t_37: bv64;
var t_41: bv32;
var t_45: bv32;
var t_49: bv32;
var t_53: bv32;
var t_85: bv64;
var t_89: bv32;


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
