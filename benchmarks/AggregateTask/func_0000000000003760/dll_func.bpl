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
axiom _function_addr_low == 14176bv64;
axiom _function_addr_high == 14660bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x3760:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RBX);

label_0x3765:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RBP);

label_0x376a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RSI);

label_0x376f:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x3770:
t_3 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x3772:
t_5 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x3774:
t_7 := RSP;
RSP := MINUS_64(RSP, 208bv64);
CF := bool2bv(LT_64(t_7, 208bv64));
OF := AND_64((XOR_64(t_7, 208bv64)), (XOR_64(t_7, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_7)), 208bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x377b:
RBX := LOAD_LE_64(mem, PLUS_64((PLUS_64(15678bv64, 14210bv64)), 0bv64));

label_0x3782:
R10 := PLUS_64(RSP, 48bv64)[64:0];

label_0x3787:
RBP := RCX;

label_0x378a:
origDEST_11 := R10;
origCOUNT_12 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
R10 := RSHIFT_64(R10, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), CF, LSHIFT_64(origDEST_11, (MINUS_64(64bv64, origCOUNT_12)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv64)), origDEST_11[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), SF, R10[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), ZF, bool2bv(0bv64 == R10));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), AF, unconstrained_2);

label_0x378e:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3791:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x3796:
origDEST_17 := RCX;
origCOUNT_18 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_5);

label_0x379a:
RAX := (0bv32 ++ 63bv32);

label_0x379f:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x37a2:
R14 := R9;

label_0x37a5:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, RSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_8);

label_0x37a8:
RSI := R8;

label_0x37ab:
mem := STORE_LE_64(mem, PLUS_64(RBX, R10), OR_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RBX, R10))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RBX, R10))));

label_0x37af:
RDI := RDX;

label_0x37b2:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x37b4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), R15);

label_0x37b9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x37be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x37c3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x37c8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x37cd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x37d2:
t_33 := AND_64(R9, R9);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x37d5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3806;
}

label_0x37d7:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x37dc:
RDX := (0bv32 ++ 254bv32);

label_0x37e1:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_13);

label_0x37e5:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x37ea:
t1_43 := RBX;
t2_44 := RAX;
RBX := PLUS_64(RBX, t2_44);
CF := bool2bv(LT_64(RBX, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x37ed:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_15);

label_0x37f1:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x37f4:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_17;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x37f6:
origDEST_57 := RDX[32:0][8:0];
origCOUNT_58 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), CF, RSHIFT_8(origDEST_57, (MINUS_8(8bv8, origCOUNT_58)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), AF, unconstrained_19);

label_0x37f8:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x37fa:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x37fe:
RAX := (0bv32 ++ OR_32((RAX[32:0]), 4294967295bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3801:
goto label_0x3927;

label_0x3806:
t_67 := AND_64(RDX, RDX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x3809:
if (bv2bool(ZF)) {
  goto label_0x37d7;
}

label_0x380b:
RCX := RBP;

label_0x380e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 2147483647bv32);

label_0x3816:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 66bv32);

label_0x381e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RDX);

label_0x3823:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RDX);

label_0x3828:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14381bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5210"} true;
call arbitrary_func();

label_0x382d:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x3835:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x383a:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x3842:
RDX := R14;

label_0x3845:

target_71 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14407bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_71"} true;
call arbitrary_func();

label_0x3847:
R8 := (0bv32 ++ RAX[32:0]);

label_0x384a:
t_73 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x384c:
if (bv2bool(SF)) {
  goto label_0x38b7;
}

label_0x384e:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x3853:
if (bv2bool(SF)) {
  goto label_0x388a;
}

label_0x3855:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x385a:
RAX := RDX;

label_0x385d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3863:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3869:
if (bv2bool(ZF)) {
  goto label_0x386c;
}

label_0x386b:
assume false;

label_0x386c:
RAX := RDX;

label_0x386f:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_27);

label_0x3873:
RCX := LOAD_LE_64(mem, PLUS_64(RBX, (LSHIFT_64(RAX, 3bv64))));

label_0x3877:
RAX := RDX;

label_0x387a:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_29);

label_0x387e:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_30;
SF := unconstrained_31;
AF := unconstrained_32;
PF := unconstrained_33;

label_0x3882:
if (bv2bool(CF)) {
  goto label_0x3885;
}

label_0x3884:
assume false;

label_0x3885:
mem := STORE_LE_8(mem, RDX, R15[32:0][8:0]);

label_0x3888:
goto label_0x388b;

label_0x388a:
assume false;

label_0x388b:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x3890:
RDX := (0bv32 ++ 254bv32);

label_0x3895:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_35);

label_0x3899:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x389e:
t1_103 := RBX;
t2_104 := RAX;
RBX := PLUS_64(RBX, t2_104);
CF := bool2bv(LT_64(RBX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x38a1:
origDEST_109 := RCX;
origCOUNT_110 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_37);

label_0x38a5:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x38a8:
origDEST_117 := RDX[32:0][8:0];
origCOUNT_118 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), CF, RSHIFT_8(origDEST_117, (MINUS_8(8bv8, origCOUNT_118)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), AF, unconstrained_40);

label_0x38aa:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x38ac:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x38ae:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x38b2:
RAX := (0bv32 ++ R8[32:0]);

label_0x38b5:
goto label_0x3927;

label_0x38b7:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x38bb:
t1_125 := RAX;
t2_126 := RDI;
RAX := PLUS_64(RAX, t2_126);
CF := bool2bv(LT_64(RAX, t1_125));
OF := AND_1((bool2bv((t1_125[64:63]) == (t2_126[64:63]))), (XOR_1((t1_125[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_125)), t2_126)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38be:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38c4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38ca:
if (bv2bool(ZF)) {
  goto label_0x38cd;
}

label_0x38cc:
assume false;

label_0x38cd:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x38d1:
t1_135 := RAX;
t2_136 := RDI;
RAX := PLUS_64(RAX, t2_136);
CF := bool2bv(LT_64(RAX, t1_135));
OF := AND_1((bool2bv((t1_135[64:63]) == (t2_136[64:63]))), (XOR_1((t1_135[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_135)), t2_136)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38d4:
origDEST_141 := RAX;
origCOUNT_142 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), CF, LSHIFT_64(origDEST_141, (MINUS_64(64bv64, origCOUNT_142)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_142 == 1bv64)), origDEST_141[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), AF, unconstrained_46);

label_0x38d8:
RCX := LOAD_LE_64(mem, PLUS_64(RBX, (LSHIFT_64(RAX, 3bv64))));

label_0x38dc:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x38e0:
t1_147 := RAX;
t2_148 := RDI;
RAX := PLUS_64(RAX, t2_148);
CF := bool2bv(LT_64(RAX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38e3:
origDEST_153 := RAX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_48);

label_0x38e7:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x38eb:
if (bv2bool(CF)) {
  goto label_0x38ee;
}

label_0x38ed:
assume false;

label_0x38ee:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), (R15[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x38f3:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x38f8:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(RDI, RSI)), 4294967295bv32 ++ 4294967295bv32), R15[32:0][8:0]);

label_0x38fd:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x3902:
R15 := (R15[64:8]) ++ ((0bv7 ++ NOT_1((XOR_1(SF, OF)))));

label_0x3906:
RDX := (0bv32 ++ 254bv32);

label_0x390b:
origDEST_163 := RAX;
origCOUNT_164 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_54);

label_0x390f:
t1_169 := RBX;
t2_170 := RAX;
RBX := PLUS_64(RBX, t2_170);
CF := bool2bv(LT_64(RBX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x3912:
origDEST_175 := RCX;
origCOUNT_176 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_56);

label_0x3916:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3919:
origDEST_183 := RDX[32:0][8:0];
origCOUNT_184 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), CF, RSHIFT_8(origDEST_183, (MINUS_8(8bv8, origCOUNT_184)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), AF, unconstrained_59);

label_0x391b:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x391d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_61;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x391f:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x3923:
RAX := (0bv32 ++ PLUS_64(R15, 4294967295bv32 ++ 4294967294bv32)[32:0]);

label_0x3927:
R11 := PLUS_64(RSP, 208bv64)[64:0];

label_0x392f:
RBX := LOAD_LE_64(mem, PLUS_64(R11, 32bv64));

label_0x3933:
RBP := LOAD_LE_64(mem, PLUS_64(R11, 40bv64));

label_0x3937:
RSI := LOAD_LE_64(mem, PLUS_64(R11, 48bv64));

label_0x393b:
RSP := R11;

label_0x393e:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x3940:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x3942:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x3943:

ra_191 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R11,R14,R15,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_110,origCOUNT_118,origCOUNT_12,origCOUNT_142,origCOUNT_154,origCOUNT_164,origCOUNT_176,origCOUNT_18,origCOUNT_184,origCOUNT_26,origCOUNT_38,origCOUNT_50,origCOUNT_58,origCOUNT_86,origCOUNT_92,origCOUNT_98,origDEST_109,origDEST_11,origDEST_117,origDEST_141,origDEST_153,origDEST_163,origDEST_17,origDEST_175,origDEST_183,origDEST_25,origDEST_37,origDEST_49,origDEST_57,origDEST_85,origDEST_91,origDEST_97,ra_191,t1_103,t1_125,t1_135,t1_147,t1_169,t1_43,t2_104,t2_126,t2_136,t2_148,t2_170,t2_44,t_1,t_159,t_3,t_33,t_5,t_67,t_7,t_73,t_77,target_71;

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
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R12: bv64;
var R13: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R11: bv64;
var R14: bv64;
var R15: bv64;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RBP: bv64;
var RBX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSI: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_110: bv64;
var origCOUNT_118: bv8;
var origCOUNT_12: bv64;
var origCOUNT_142: bv64;
var origCOUNT_154: bv64;
var origCOUNT_164: bv64;
var origCOUNT_176: bv64;
var origCOUNT_18: bv64;
var origCOUNT_184: bv8;
var origCOUNT_26: bv64;
var origCOUNT_38: bv64;
var origCOUNT_50: bv64;
var origCOUNT_58: bv8;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origCOUNT_98: bv64;
var origDEST_109: bv64;
var origDEST_11: bv64;
var origDEST_117: bv8;
var origDEST_141: bv64;
var origDEST_153: bv64;
var origDEST_163: bv64;
var origDEST_17: bv64;
var origDEST_175: bv64;
var origDEST_183: bv8;
var origDEST_25: bv64;
var origDEST_37: bv64;
var origDEST_49: bv64;
var origDEST_57: bv8;
var origDEST_85: bv64;
var origDEST_91: bv64;
var origDEST_97: bv64;
var ra_191: bv64;
var t1_103: bv64;
var t1_125: bv64;
var t1_135: bv64;
var t1_147: bv64;
var t1_169: bv64;
var t1_43: bv64;
var t2_104: bv64;
var t2_126: bv64;
var t2_136: bv64;
var t2_148: bv64;
var t2_170: bv64;
var t2_44: bv64;
var t_1: bv64;
var t_159: bv32;
var t_3: bv64;
var t_33: bv64;
var t_5: bv64;
var t_67: bv64;
var t_7: bv64;
var t_73: bv32;
var t_77: bv32;
var target_71: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4272bv64);
axiom policy(4368bv64);
axiom policy(4464bv64);
axiom policy(4560bv64);
axiom policy(4960bv64);
axiom policy(4976bv64);
axiom policy(5008bv64);
axiom policy(5168bv64);
axiom policy(5216bv64);
axiom policy(5328bv64);
axiom policy(5872bv64);
axiom policy(4944bv64);
axiom policy(5632bv64);
axiom policy(5648bv64);
axiom policy(5760bv64);
axiom policy(5888bv64);
axiom policy(6224bv64);
axiom policy(6272bv64);
axiom policy(6288bv64);
axiom policy(6304bv64);
axiom policy(6320bv64);
axiom policy(6336bv64);
axiom policy(6352bv64);
axiom policy(6448bv64);
axiom policy(6848bv64);
axiom policy(6944bv64);
axiom policy(6960bv64);
axiom policy(7056bv64);
axiom policy(10096bv64);
axiom policy(10528bv64);
axiom policy(11312bv64);
axiom policy(13744bv64);
axiom policy(14160bv64);
axiom policy(14176bv64);
axiom policy(14672bv64);
axiom policy(14832bv64);
axiom policy(14848bv64);
axiom policy(15568bv64);
axiom policy(16528bv64);
axiom policy(19088bv64);
axiom policy(19472bv64);
axiom policy(19840bv64);
axiom policy(20720bv64);
axiom policy(20800bv64);
axiom policy(21008bv64);
axiom policy(21088bv64);
axiom policy(21104bv64);
axiom policy(21120bv64);
axiom policy(21328bv64);
axiom policy(21344bv64);
axiom policy(21360bv64);
axiom policy(21520bv64);
