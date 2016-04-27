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
axiom _guard_writeTable_ptr == 29136bv64;
axiom _guard_callTable_ptr == 29152bv64;
axiom _function_addr_low == 5520bv64;
axiom _function_addr_high == 6122bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x1590:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RBP);

label_0x1595:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RDI);

label_0x159a:
t_1 := R12;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x159c:
t_3 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x159e:
t_5 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x15a0:
t_7 := RSP;
RSP := MINUS_64(RSP, 448bv64);
CF := bool2bv(LT_64(t_7, 448bv64));
OF := AND_64((XOR_64(t_7, 448bv64)), (XOR_64(t_7, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_7)), 448bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x15a7:
R14 := LOAD_LE_64(mem, PLUS_64((PLUS_64(23586bv64, 5550bv64)), 0bv64));

label_0x15ae:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x15b3:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x15b6:
origDEST_11 := RCX;
origCOUNT_12 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), CF, LSHIFT_64(origDEST_11, (MINUS_64(64bv64, origCOUNT_12)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv64)), origDEST_11[64:63], unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), AF, unconstrained_3);

label_0x15ba:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x15bd:
R9 := PLUS_64(RSP, 64bv64)[64:0];

label_0x15c2:
origDEST_19 := R9;
origCOUNT_20 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
R9 := RSHIFT_64(R9, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, R9[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == R9));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R9, 4bv64)), R9)), 2bv64)), (XOR_64((RSHIFT_64(R9, 4bv64)), R9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R9, 4bv64)), R9)), 2bv64)), (XOR_64((RSHIFT_64(R9, 4bv64)), R9)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_6);

label_0x15c6:
RAX := (0bv32 ++ 8191bv32);

label_0x15cb:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, RSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_8);

label_0x15ce:
RDI := (0bv32 ++ R15[32:0]);

label_0x15d1:
R12 := R8;

label_0x15d4:
RBP := (0bv32 ++ R15[32:0]);

label_0x15d7:
R8 := (0bv32 ++ R15[32:0]);

label_0x15da:
R11 := (0bv32 ++ R15[32:0]);

label_0x15dd:
mem := STORE_LE_64(mem, PLUS_64(R14, R9), OR_64((LOAD_LE_64(mem, PLUS_64(R14, R9))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R14, R9))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R14, R9))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R14, R9))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R14, R9))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R14, R9))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R14, R9))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R14, R9))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R14, R9))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(R14, R9))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(R14, R9))));

label_0x15e1:
R10 := (0bv32 ++ R15[32:0]);

label_0x15e4:
t_33 := MINUS_8((LOAD_LE_8(mem, RDX)), (RDI[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDX)), (RDI[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDX)), (RDI[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RDX)), t_33)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_33, (LOAD_LE_8(mem, RDX)))), (RDI[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_33, 4bv8)), t_33)), 2bv8)), (XOR_8((RSHIFT_8(t_33, 4bv8)), t_33)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_33, 4bv8)), t_33)), 2bv8)), (XOR_8((RSHIFT_8(t_33, 4bv8)), t_33)))))[1:0]));
SF := t_33[8:7];
ZF := bool2bv(0bv8 == t_33);

label_0x15e7:
if (bv2bool(ZF)) {
  goto label_0x179d;
}

label_0x15ed:


label_0x15f0:
t_37 := MINUS_8((LOAD_LE_8(mem, RDX)), 9bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDX)), 9bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDX)), 9bv8)), (XOR_8((LOAD_LE_8(mem, RDX)), t_37)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_37, (LOAD_LE_8(mem, RDX)))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_37, 4bv8)), t_37)), 2bv8)), (XOR_8((RSHIFT_8(t_37, 4bv8)), t_37)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_37, 4bv8)), t_37)), 2bv8)), (XOR_8((RSHIFT_8(t_37, 4bv8)), t_37)))))[1:0]));
SF := t_37[8:7];
ZF := bool2bv(0bv8 == t_37);

label_0x15f3:
R9 := RDX;

label_0x15f6:
RAX := RDX;

label_0x15f9:
if (bv2bool(ZF)) {
  goto label_0x160d;
}

label_0x15fb:


label_0x1600:
t_41 := MINUS_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RAX)), t_41)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_41, (LOAD_LE_8(mem, RAX)))), (R15[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)), 2bv8)), (XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)), 2bv8)), (XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)))))[1:0]));
SF := t_41[8:7];
ZF := bool2bv(0bv8 == t_41);

label_0x1603:
if (bv2bool(ZF)) {
  goto label_0x160d;
}

label_0x1605:
t_45 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_45[64:63]) == (1bv64[64:63]))), (XOR_1((t_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_45)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1608:
t_49 := MINUS_8((LOAD_LE_8(mem, RAX)), 9bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), 9bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), 9bv8)), (XOR_8((LOAD_LE_8(mem, RAX)), t_49)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_49, (LOAD_LE_8(mem, RAX)))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)), 2bv8)), (XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)), 2bv8)), (XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)))))[1:0]));
SF := t_49[8:7];
ZF := bool2bv(0bv8 == t_49);

label_0x160b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1600;
}

label_0x160d:
t_53 := MINUS_8((LOAD_LE_8(mem, RAX)), 48bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), 48bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), 48bv8)), (XOR_8((LOAD_LE_8(mem, RAX)), t_53)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_53, (LOAD_LE_8(mem, RAX)))), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)), 2bv8)), (XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)), 2bv8)), (XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)))))[1:0]));
SF := t_53[8:7];
ZF := bool2bv(0bv8 == t_53);

label_0x1610:
if (bv2bool(ZF)) {
  goto label_0x1645;
}

label_0x1612:
RCX := RAX;

label_0x1615:
RCX := AND_64(RCX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x161c:
RCX := XOR_64(RCX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1623:
if (bv2bool(ZF)) {
  goto label_0x1626;
}

label_0x1625:
assume false;

label_0x1626:
RCX := RAX;

label_0x1629:
origDEST_61 := RCX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_13);

label_0x162d:
RDX := LOAD_LE_64(mem, PLUS_64(R14, (LSHIFT_64(RCX, 3bv64))));

label_0x1631:
RCX := RAX;

label_0x1634:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_15);

label_0x1638:
CF := RSHIFT_64(RDX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_16;
SF := unconstrained_17;
AF := unconstrained_18;
PF := unconstrained_19;

label_0x163c:
if (bv2bool(CF)) {
  goto label_0x163f;
}

label_0x163e:
assume false;

label_0x163f:
mem := STORE_LE_8(mem, RAX, R15[32:0][8:0]);

label_0x1642:
t_73 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_73[64:63]) == (1bv64[64:63]))), (XOR_1((t_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_73)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1645:
RDX := RAX;

label_0x1648:
t_77 := MINUS_32((R8[32:0]), 2bv32);
CF := bool2bv(LT_32((R8[32:0]), 2bv32));
OF := AND_32((XOR_32((R8[32:0]), 2bv32)), (XOR_32((R8[32:0]), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (R8[32:0]))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x164c:
if (bv2bool(ZF)) {
  goto label_0x166f;
}

label_0x164e:
t_81 := MINUS_32((R8[32:0]), 5bv32);
CF := bool2bv(LT_32((R8[32:0]), 5bv32));
OF := AND_32((XOR_32((R8[32:0]), 5bv32)), (XOR_32((R8[32:0]), t_81)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_81, (R8[32:0]))), 5bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))))[1:0]));
SF := t_81[32:31];
ZF := bool2bv(0bv32 == t_81);

label_0x1652:
if (bv2bool(ZF)) {
  goto label_0x166a;
}

label_0x1654:
t_85 := MINUS_32((R8[32:0]), 7bv32);
CF := bool2bv(LT_32((R8[32:0]), 7bv32));
OF := AND_32((XOR_32((R8[32:0]), 7bv32)), (XOR_32((R8[32:0]), t_85)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_85, (R8[32:0]))), 7bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))))[1:0]));
SF := t_85[32:31];
ZF := bool2bv(0bv32 == t_85);

label_0x1658:
if (bv2bool(ZF)) {
  goto label_0x1665;
}

label_0x165a:
t_89 := MINUS_32((R8[32:0]), 12bv32);
CF := bool2bv(LT_32((R8[32:0]), 12bv32));
OF := AND_32((XOR_32((R8[32:0]), 12bv32)), (XOR_32((R8[32:0]), t_89)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_89, (R8[32:0]))), 12bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))))[1:0]));
SF := t_89[32:31];
ZF := bool2bv(0bv32 == t_89);

label_0x165e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1672;
}

label_0x1660:
R10 := R9;

label_0x1663:
goto label_0x1672;

label_0x1665:
R11 := R9;

label_0x1668:
goto label_0x1672;

label_0x166a:
RBP := R9;

label_0x166d:
goto label_0x1672;

label_0x166f:
RDI := R9;

label_0x1672:
t_93 := R8[32:0];
R8 := (0bv32 ++ PLUS_32((R8[32:0]), 1bv32));
OF := AND_1((bool2bv((t_93[32:31]) == (1bv32[32:31]))), (XOR_1((t_93[32:31]), (R8[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((R8[32:0]), t_93)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))))))[1:0]));
SF := R8[32:0][32:31];
ZF := bool2bv(0bv32 == (R8[32:0]));

label_0x1675:
t_97 := MINUS_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), (R15[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RAX)), t_97)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_97, (LOAD_LE_8(mem, RAX)))), (R15[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))))[1:0]));
SF := t_97[8:7];
ZF := bool2bv(0bv8 == t_97);

label_0x1678:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15f0;
}

label_0x167e:
t_101 := AND_64(RDI, RDI);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x1681:
if (bv2bool(ZF)) {
  goto label_0x179d;
}

label_0x1687:
t_105 := AND_64(RBP, RBP);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))))[1:0]));
SF := t_105[64:63];
ZF := bool2bv(0bv64 == t_105);

label_0x168a:
if (bv2bool(ZF)) {
  goto label_0x179d;
}

label_0x1690:
t_109 := AND_64(R11, R11);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))))[1:0]));
SF := t_109[64:63];
ZF := bool2bv(0bv64 == t_109);

label_0x1693:
if (bv2bool(ZF)) {
  goto label_0x179d;
}

label_0x1699:
t_113 := AND_64(R10, R10);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))))[1:0]));
SF := t_113[64:63];
ZF := bool2bv(0bv64 == t_113);

label_0x169c:
if (bv2bool(ZF)) {
  goto label_0x179d;
}

label_0x16a2:
t_117 := MINUS_8((LOAD_LE_8(mem, R10)), 48bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, R10)), 48bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, R10)), 48bv8)), (XOR_8((LOAD_LE_8(mem, R10)), t_117)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_117, (LOAD_LE_8(mem, R10)))), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_117, 4bv8)), t_117)), 2bv8)), (XOR_8((RSHIFT_8(t_117, 4bv8)), t_117)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_117, 4bv8)), t_117)), 2bv8)), (XOR_8((RSHIFT_8(t_117, 4bv8)), t_117)))))[1:0]));
SF := t_117[8:7];
ZF := bool2bv(0bv8 == t_117);

label_0x16a6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x179d;
}

label_0x16ac:
mem := STORE_LE_64(mem, PLUS_64(RSP, 480bv64), RBX);

label_0x16b4:
RDX := PLUS_64((PLUS_64(19301bv64, 5819bv64)), 0bv64)[64:0];

label_0x16bb:
RCX := R11;

label_0x16be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 488bv64), RSI);

label_0x16c6:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5835bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2fb0"} true;
call arbitrary_func();

label_0x16cb:
t_121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x16ce:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x16d3:
RBX := (RBX[64:8]) ++ ((0bv7 ++ NOT_1(ZF)));

label_0x16d6:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_25;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x16d8:
R8 := (0bv32 ++ PLUS_64(RDX, 100bv64)[32:0]);

label_0x16dc:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5857bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3960"} true;
call arbitrary_func();

label_0x16e1:
RCX := RDI;

label_0x16e4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5865bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1f60"} true;
call arbitrary_func();

label_0x16e9:
RCX := (0bv32 ++ 32bv32);

label_0x16ee:
RSI := RAX;

label_0x16f1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5878bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f60"} true;
call arbitrary_func();

label_0x16f6:
t_125 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))))[1:0]));
SF := t_125[64:63];
ZF := bool2bv(0bv64 == t_125);

label_0x16f9:
if (bv2bool(ZF)) {
  goto label_0x170b;
}

label_0x16fb:
RDX := RSI;

label_0x16fe:
RCX := RAX;

label_0x1701:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5894bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3010"} true;
call arbitrary_func();

label_0x1706:
RDI := RAX;

label_0x1709:
goto label_0x170e;

label_0x170b:
RDI := R15;

label_0x170e:
RCX := RBP;

label_0x1711:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5910bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1f60"} true;
call arbitrary_func();

label_0x1716:
RBP := RAX;

label_0x1719:
R8 := PLUS_64((PLUS_64(19212bv64, 5920bv64)), 0bv64)[64:0];

label_0x1720:
RAX := (0bv32 ++ 69bv32);

label_0x1725:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RBP);

label_0x172a:
R9 := (0bv32 ++ 73bv32);

label_0x1730:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x1735:
t_129 := AND_8((RBX[32:0][8:0]), (RBX[32:0][8:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)), 2bv8)), (XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)), 2bv8)), (XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)))))[1:0]));
SF := t_129[8:7];
ZF := bool2bv(0bv8 == t_129);

label_0x1737:
RDX := (0bv32 ++ PLUS_64(RAX, 31bv64)[32:0]);

label_0x173a:
R9 := (0bv32 ++ ITE_32(bv2bool(NOT_1(ZF)), RAX[32:0], R9[32:0]));

label_0x173e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5955bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38c0"} true;
call arbitrary_func();

label_0x1743:
RCX := (0bv32 ++ 32bv32);

label_0x1748:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5965bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f60"} true;
call arbitrary_func();

label_0x174d:
t_133 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))))[1:0]));
SF := t_133[64:63];
ZF := bool2bv(0bv64 == t_133);

label_0x1750:
if (bv2bool(ZF)) {
  goto label_0x1762;
}

label_0x1752:
RDX := PLUS_64(RSP, 64bv64)[64:0];

label_0x1757:
RCX := RAX;

label_0x175a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5983bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3010"} true;
call arbitrary_func();

label_0x175f:
R15 := RAX;

label_0x1762:
RAX := LOAD_LE_64(mem, R12);

label_0x1766:
RBX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x176a:
RCX := RBX;

label_0x176d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6002bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x50d0"} true;
call arbitrary_func();

label_0x1772:
R8 := R15;

label_0x1775:
RDX := RDI;

label_0x1778:
RCX := R12;

label_0x177b:

target_137 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6013bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_137"} true;
call arbitrary_func();

label_0x177d:
RCX := RSI;

label_0x1780:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6021bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5130"} true;
call arbitrary_func();

label_0x1785:
RCX := RBP;

label_0x1788:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6029bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5130"} true;
call arbitrary_func();

label_0x178d:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0x1795:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0x179d:
R11 := PLUS_64(RSP, 448bv64)[64:0];

label_0x17a5:
RAX := PLUS_64(RSP, 176bv64)[64:0];

label_0x17ad:
origDEST_139 := RAX;
origCOUNT_140 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_30);

label_0x17b1:
RCX := PLUS_64(RSP, 176bv64)[64:0];

label_0x17b9:
t1_145 := R14;
t2_146 := RAX;
R14 := PLUS_64(R14, t2_146);
CF := bool2bv(LT_64(R14, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (R14[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R14, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R14, 4bv64)), R14)), 2bv64)), (XOR_64((RSHIFT_64(R14, 4bv64)), R14)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R14, 4bv64)), R14)), 2bv64)), (XOR_64((RSHIFT_64(R14, 4bv64)), R14)))))[1:0]));
SF := R14[64:63];
ZF := bool2bv(0bv64 == R14);

label_0x17bc:
origDEST_151 := RCX;
origCOUNT_152 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), CF, LSHIFT_64(origDEST_151, (MINUS_64(64bv64, origCOUNT_152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_152 == 1bv64)), origDEST_151[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), AF, unconstrained_32);

label_0x17c0:
RAX := (0bv32 ++ 254bv32);

label_0x17c5:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x17c8:
origDEST_159 := RAX[32:0][8:0];
origCOUNT_160 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), CF, RSHIFT_8(origDEST_159, (MINUS_8(8bv8, origCOUNT_160)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv8)), AF, unconstrained_35);

label_0x17ca:
mem := STORE_LE_8(mem, R14, AND_8((LOAD_LE_8(mem, R14)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, R14)), 4bv8)), (LOAD_LE_8(mem, R14)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, R14)), 4bv8)), (LOAD_LE_8(mem, R14)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, R14)), 4bv8)), (LOAD_LE_8(mem, R14)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, R14)), 4bv8)), (LOAD_LE_8(mem, R14)))))))[1:0]));
SF := LOAD_LE_8(mem, R14)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, R14)));

label_0x17cd:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_37;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x17cf:
mem := STORE_LE_16(mem, PLUS_64(R14, 4294967295bv32 ++ 4294967293bv32), RAX[32:0][16:0]);

label_0x17d4:
mem := STORE_LE_8(mem, PLUS_64(R14, 4294967295bv32 ++ 4294967295bv32), RAX[32:0][8:0]);

label_0x17d8:
RBP := LOAD_LE_64(mem, PLUS_64(R11, 48bv64));

label_0x17dc:
RDI := LOAD_LE_64(mem, PLUS_64(R11, 56bv64));

label_0x17e0:
RSP := R11;

label_0x17e3:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x17e5:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x17e7:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x17e9:

ra_167 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R11,R12,R14,R15,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_12,origCOUNT_140,origCOUNT_152,origCOUNT_160,origCOUNT_20,origCOUNT_26,origCOUNT_62,origCOUNT_68,origDEST_11,origDEST_139,origDEST_151,origDEST_159,origDEST_19,origDEST_25,origDEST_61,origDEST_67,ra_167,t1_145,t2_146,t_1,t_101,t_105,t_109,t_113,t_117,t_121,t_125,t_129,t_133,t_3,t_33,t_37,t_41,t_45,t_49,t_5,t_53,t_7,t_73,t_77,t_81,t_85,t_89,t_93,t_97,target_137;

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
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R13: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R11: bv64;
var R12: bv64;
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
var origCOUNT_12: bv64;
var origCOUNT_140: bv64;
var origCOUNT_152: bv64;
var origCOUNT_160: bv8;
var origCOUNT_20: bv64;
var origCOUNT_26: bv64;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origDEST_11: bv64;
var origDEST_139: bv64;
var origDEST_151: bv64;
var origDEST_159: bv8;
var origDEST_19: bv64;
var origDEST_25: bv64;
var origDEST_61: bv64;
var origDEST_67: bv64;
var ra_167: bv64;
var t1_145: bv64;
var t2_146: bv64;
var t_1: bv64;
var t_101: bv64;
var t_105: bv64;
var t_109: bv64;
var t_113: bv64;
var t_117: bv8;
var t_121: bv64;
var t_125: bv64;
var t_129: bv8;
var t_133: bv64;
var t_3: bv64;
var t_33: bv8;
var t_37: bv8;
var t_41: bv8;
var t_45: bv64;
var t_49: bv8;
var t_5: bv64;
var t_53: bv8;
var t_7: bv64;
var t_73: bv64;
var t_77: bv32;
var t_81: bv32;
var t_85: bv32;
var t_89: bv32;
var t_93: bv32;
var t_97: bv8;
var target_137: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(11504bv64);
axiom policy(4272bv64);
axiom policy(4384bv64);
axiom policy(4576bv64);
axiom policy(4624bv64);
axiom policy(4720bv64);
axiom policy(4816bv64);
axiom policy(4912bv64);
axiom policy(5008bv64);
axiom policy(5120bv64);
axiom policy(5168bv64);
axiom policy(5440bv64);
axiom policy(5520bv64);
axiom policy(6128bv64);
axiom policy(6752bv64);
axiom policy(7392bv64);
axiom policy(8032bv64);
axiom policy(9504bv64);
axiom policy(9632bv64);
axiom policy(9648bv64);
axiom policy(9664bv64);
axiom policy(9824bv64);
axiom policy(9872bv64);
axiom policy(9984bv64);
axiom policy(10080bv64);
axiom policy(10320bv64);
axiom policy(11728bv64);
axiom policy(11488bv64);
axiom policy(11616bv64);
axiom policy(13168bv64);
axiom policy(11744bv64);
axiom policy(12080bv64);
axiom policy(12128bv64);
axiom policy(12144bv64);
axiom policy(12160bv64);
axiom policy(12176bv64);
axiom policy(12192bv64);
axiom policy(12208bv64);
axiom policy(12304bv64);
axiom policy(12400bv64);
axiom policy(12800bv64);
axiom policy(13072bv64);
axiom policy(13184bv64);
axiom policy(13280bv64);
axiom policy(13856bv64);
axiom policy(14352bv64);
axiom policy(14512bv64);
axiom policy(14528bv64);
axiom policy(15248bv64);
axiom policy(16208bv64);
axiom policy(18768bv64);
axiom policy(19152bv64);
axiom policy(19520bv64);
axiom policy(20400bv64);
axiom policy(20480bv64);
axiom policy(20688bv64);
axiom policy(20768bv64);
axiom policy(20784bv64);
axiom policy(20800bv64);
axiom policy(20816bv64);
axiom policy(20832bv64);
axiom policy(21040bv64);
axiom policy(21200bv64);
