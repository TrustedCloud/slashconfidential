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
axiom _guard_writeTable_ptr == 24992bv64;
axiom _guard_callTable_ptr == 25008bv64;
axiom _function_addr_low == 10864bv64;
axiom _function_addr_high == 11348bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x2a70:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RBX);

label_0x2a75:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RBP);

label_0x2a7a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RSI);

label_0x2a7f:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x2a80:
t_3 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x2a82:
t_5 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x2a84:
t_7 := RSP;
RSP := MINUS_64(RSP, 208bv64);
CF := bool2bv(LT_64(t_7, 208bv64));
OF := AND_64((XOR_64(t_7, 208bv64)), (XOR_64(t_7, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_7)), 208bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2a8b:
RBX := LOAD_LE_64(mem, PLUS_64((PLUS_64(14094bv64, 10898bv64)), 0bv64));

label_0x2a92:
R10 := PLUS_64(RSP, 48bv64)[64:0];

label_0x2a97:
RBP := RCX;

label_0x2a9a:
origDEST_11 := R10;
origCOUNT_12 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
R10 := RSHIFT_64(R10, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), CF, LSHIFT_64(origDEST_11, (MINUS_64(64bv64, origCOUNT_12)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv64)), origDEST_11[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), SF, R10[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), ZF, bool2bv(0bv64 == R10));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), AF, unconstrained_2);

label_0x2a9e:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2aa1:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x2aa6:
origDEST_17 := RCX;
origCOUNT_18 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_5);

label_0x2aaa:
RAX := (0bv32 ++ 63bv32);

label_0x2aaf:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2ab2:
R14 := R9;

label_0x2ab5:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, RSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_8);

label_0x2ab8:
RSI := R8;

label_0x2abb:
mem := STORE_LE_64(mem, PLUS_64(RBX, R10), OR_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBX, R10))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBX, R10))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RBX, R10))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RBX, R10))));

label_0x2abf:
RDI := RDX;

label_0x2ac2:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2ac4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), R15);

label_0x2ac9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x2ace:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x2ad3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x2ad8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x2add:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x2ae2:
t_33 := AND_64(R9, R9);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x2ae5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2b16;
}

label_0x2ae7:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2aec:
RDX := (0bv32 ++ 254bv32);

label_0x2af1:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_13);

label_0x2af5:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2afa:
t1_43 := RBX;
t2_44 := RAX;
RBX := PLUS_64(RBX, t2_44);
CF := bool2bv(LT_64(RBX, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x2afd:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_15);

label_0x2b01:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2b04:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_17;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2b06:
origDEST_57 := RDX[32:0][8:0];
origCOUNT_58 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), CF, RSHIFT_8(origDEST_57, (MINUS_8(8bv8, origCOUNT_58)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv8)), AF, unconstrained_19);

label_0x2b08:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x2b0a:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x2b0e:
RAX := (0bv32 ++ OR_32((RAX[32:0]), 4294967295bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2b11:
goto label_0x2c37;

label_0x2b16:
t_67 := AND_64(RDX, RDX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x2b19:
if (bv2bool(ZF)) {
  goto label_0x2ae7;
}

label_0x2b1b:
RCX := RBP;

label_0x2b1e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 2147483647bv32);

label_0x2b26:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 66bv32);

label_0x2b2e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RDX);

label_0x2b33:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RDX);

label_0x2b38:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11069bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4520"} true;
call arbitrary_func();

label_0x2b3d:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2b45:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x2b4a:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x2b52:
RDX := R14;

label_0x2b55:

target_71 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11095bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_71"} true;
call arbitrary_func();

label_0x2b57:
R8 := (0bv32 ++ RAX[32:0]);

label_0x2b5a:
t_73 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x2b5c:
if (bv2bool(SF)) {
  goto label_0x2bc7;
}

label_0x2b5e:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x2b63:
if (bv2bool(SF)) {
  goto label_0x2b9a;
}

label_0x2b65:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2b6a:
RAX := RDX;

label_0x2b6d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b73:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b79:
if (bv2bool(ZF)) {
  goto label_0x2b7c;
}

label_0x2b7b:
assume false;

label_0x2b7c:
RAX := RDX;

label_0x2b7f:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_27);

label_0x2b83:
RCX := LOAD_LE_64(mem, PLUS_64(RBX, (LSHIFT_64(RAX, 3bv64))));

label_0x2b87:
RAX := RDX;

label_0x2b8a:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_29);

label_0x2b8e:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_30;
SF := unconstrained_31;
AF := unconstrained_32;
PF := unconstrained_33;

label_0x2b92:
if (bv2bool(CF)) {
  goto label_0x2b95;
}

label_0x2b94:
assume false;

label_0x2b95:
mem := STORE_LE_8(mem, RDX, R15[32:0][8:0]);

label_0x2b98:
goto label_0x2b9b;

label_0x2b9a:
assume false;

label_0x2b9b:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2ba0:
RDX := (0bv32 ++ 254bv32);

label_0x2ba5:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_35);

label_0x2ba9:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2bae:
t1_103 := RBX;
t2_104 := RAX;
RBX := PLUS_64(RBX, t2_104);
CF := bool2bv(LT_64(RBX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x2bb1:
origDEST_109 := RCX;
origCOUNT_110 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_37);

label_0x2bb5:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2bb8:
origDEST_117 := RDX[32:0][8:0];
origCOUNT_118 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), CF, RSHIFT_8(origDEST_117, (MINUS_8(8bv8, origCOUNT_118)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv8)), AF, unconstrained_40);

label_0x2bba:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x2bbc:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2bbe:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x2bc2:
RAX := (0bv32 ++ R8[32:0]);

label_0x2bc5:
goto label_0x2c37;

label_0x2bc7:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x2bcb:
t1_125 := RAX;
t2_126 := RDI;
RAX := PLUS_64(RAX, t2_126);
CF := bool2bv(LT_64(RAX, t1_125));
OF := AND_1((bool2bv((t1_125[64:63]) == (t2_126[64:63]))), (XOR_1((t1_125[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_125)), t2_126)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bd4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bda:
if (bv2bool(ZF)) {
  goto label_0x2bdd;
}

label_0x2bdc:
assume false;

label_0x2bdd:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x2be1:
t1_135 := RAX;
t2_136 := RDI;
RAX := PLUS_64(RAX, t2_136);
CF := bool2bv(LT_64(RAX, t1_135));
OF := AND_1((bool2bv((t1_135[64:63]) == (t2_136[64:63]))), (XOR_1((t1_135[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_135)), t2_136)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2be4:
origDEST_141 := RAX;
origCOUNT_142 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), CF, LSHIFT_64(origDEST_141, (MINUS_64(64bv64, origCOUNT_142)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_142 == 1bv64)), origDEST_141[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), AF, unconstrained_46);

label_0x2be8:
RCX := LOAD_LE_64(mem, PLUS_64(RBX, (LSHIFT_64(RAX, 3bv64))));

label_0x2bec:
RAX := PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x2bf0:
t1_147 := RAX;
t2_148 := RDI;
RAX := PLUS_64(RAX, t2_148);
CF := bool2bv(LT_64(RAX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bf3:
origDEST_153 := RAX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_48);

label_0x2bf7:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x2bfb:
if (bv2bool(CF)) {
  goto label_0x2bfe;
}

label_0x2bfd:
assume false;

label_0x2bfe:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (R15[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), (R15[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x2c03:
RAX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2c08:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(RDI, RSI)), 4294967295bv32 ++ 4294967295bv32), R15[32:0][8:0]);

label_0x2c0d:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2c12:
R15 := (R15[64:8]) ++ ((0bv7 ++ NOT_1((XOR_1(SF, OF)))));

label_0x2c16:
RDX := (0bv32 ++ 254bv32);

label_0x2c1b:
origDEST_163 := RAX;
origCOUNT_164 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_54);

label_0x2c1f:
t1_169 := RBX;
t2_170 := RAX;
RBX := PLUS_64(RBX, t2_170);
CF := bool2bv(LT_64(RBX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x2c22:
origDEST_175 := RCX;
origCOUNT_176 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_56);

label_0x2c26:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2c29:
origDEST_183 := RDX[32:0][8:0];
origCOUNT_184 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), CF, RSHIFT_8(origDEST_183, (MINUS_8(8bv8, origCOUNT_184)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv8)), AF, unconstrained_59);

label_0x2c2b:
mem := STORE_LE_8(mem, RBX, AND_8((LOAD_LE_8(mem, RBX)), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RBX)), 4bv8)), (LOAD_LE_8(mem, RBX)))))))[1:0]));
SF := LOAD_LE_8(mem, RBX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RBX)));

label_0x2c2d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_61;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2c2f:
mem := STORE_LE_16(mem, PLUS_64(RBX, 4294967295bv32 ++ 4294967294bv32), RAX[32:0][16:0]);

label_0x2c33:
RAX := (0bv32 ++ PLUS_64(R15, 4294967295bv32 ++ 4294967294bv32)[32:0]);

label_0x2c37:
R11 := PLUS_64(RSP, 208bv64)[64:0];

label_0x2c3f:
RBX := LOAD_LE_64(mem, PLUS_64(R11, 32bv64));

label_0x2c43:
RBP := LOAD_LE_64(mem, PLUS_64(R11, 40bv64));

label_0x2c47:
RSI := LOAD_LE_64(mem, PLUS_64(R11, 48bv64));

label_0x2c4b:
RSP := R11;

label_0x2c4e:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2c50:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2c52:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2c53:

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
axiom policy(4240bv64);
axiom policy(4416bv64);
axiom policy(4544bv64);
axiom policy(4736bv64);
axiom policy(4784bv64);
axiom policy(4880bv64);
axiom policy(4976bv64);
axiom policy(5072bv64);
axiom policy(5168bv64);
axiom policy(5216bv64);
axiom policy(5296bv64);
axiom policy(5712bv64);
axiom policy(5856bv64);
axiom policy(5872bv64);
axiom policy(6016bv64);
axiom policy(6048bv64);
axiom policy(6640bv64);
axiom policy(6800bv64);
axiom policy(6848bv64);
axiom policy(6960bv64);
axiom policy(7424bv64);
axiom policy(7664bv64);
axiom policy(7824bv64);
axiom policy(8080bv64);
axiom policy(8832bv64);
axiom policy(5840bv64);
axiom policy(8592bv64);
axiom policy(8608bv64);
axiom policy(8720bv64);
axiom policy(10176bv64);
axiom policy(8848bv64);
axiom policy(9184bv64);
axiom policy(9232bv64);
axiom policy(9248bv64);
axiom policy(9264bv64);
axiom policy(9280bv64);
axiom policy(9296bv64);
axiom policy(9312bv64);
axiom policy(9408bv64);
axiom policy(9808bv64);
axiom policy(10080bv64);
axiom policy(10192bv64);
axiom policy(10288bv64);
axiom policy(10864bv64);
axiom policy(11360bv64);
axiom policy(11520bv64);
axiom policy(11536bv64);
axiom policy(12256bv64);
axiom policy(13216bv64);
axiom policy(15776bv64);
axiom policy(16160bv64);
axiom policy(16528bv64);
axiom policy(17408bv64);
axiom policy(17488bv64);
axiom policy(17696bv64);
axiom policy(17776bv64);
axiom policy(17792bv64);
axiom policy(17808bv64);
axiom policy(18016bv64);
axiom policy(18032bv64);
axiom policy(18048bv64);
axiom policy(18208bv64);
