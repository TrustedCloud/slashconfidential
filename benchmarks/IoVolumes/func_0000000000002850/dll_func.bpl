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
axiom _function_addr_low == 10320bv64;
axiom _function_addr_high == 11479bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x2850:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RBX);

label_0x2855:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x285a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x285f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x2864:
t_1 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x2865:
t_3 := RSI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x2866:
t_5 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x2867:
t_7 := R12;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_7);

label_0x2869:
t_9 := R13;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_9);

label_0x286b:
t_11 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_11);

label_0x286d:
t_13 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_13);

label_0x286f:
RBP := PLUS_64(RSP, 4294967295bv32 ++ 4294965904bv32)[64:0];

label_0x2877:
t_15 := RSP;
RSP := MINUS_64(RSP, 1648bv64);
CF := bool2bv(LT_64(t_15, 1648bv64));
OF := AND_64((XOR_64(t_15, 1648bv64)), (XOR_64(t_15, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_15)), 1648bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x287e:
RDX := (0bv32 ++ 1024bv32);

label_0x2883:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967264bv32)[64:0];

label_0x2887:
R14 := R8;

label_0x288a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10383bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5120"} true;
call arbitrary_func();

label_0x288f:
R13 := LOAD_LE_64(mem, PLUS_64((PLUS_64(18746bv64, 10390bv64)), 0bv64));

label_0x2896:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x289b:
origDEST_19 := RCX;
origCOUNT_20 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_2);

label_0x289f:
R10 := PLUS_64(RSP, 96bv64)[64:0];

label_0x28a4:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x28a7:
origDEST_27 := R10;
origCOUNT_28 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
R10 := RSHIFT_64(R10, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), CF, LSHIFT_64(origDEST_27, (MINUS_64(64bv64, origCOUNT_28)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_28 == 1bv64)), origDEST_27[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), SF, R10[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), ZF, bool2bv(0bv64 == R10));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), AF, unconstrained_5);

label_0x28ab:
RAX := (0bv32 ++ 16191bv32);

label_0x28b0:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_6;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28b2:
origDEST_33 := RAX;
origCOUNT_34 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, RSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_8);

label_0x28b5:
R8 := (0bv32 ++ 1024bv32);

label_0x28bb:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967264bv32)[64:0];

label_0x28bf:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64), OR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, R10)), 0bv64))));

label_0x28c4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10441bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3960"} true;
call arbitrary_func();

label_0x28c9:
RDI := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28cb:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x28cf:
RBX := (0bv32 ++ 0bv32);
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28d1:
mem := STORE_LE_64(mem, PLUS_64(RBP, 1232bv64), RDI);

label_0x28d8:
RDX := (0bv32 ++ 10000bv32);

label_0x28dd:
mem := STORE_LE_64(mem, PLUS_64(RBP, 1256bv64), RBX);

label_0x28e4:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_12;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28e7:
R12 := (0bv32 ++ 0bv32);
AF := unconstrained_13;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28ea:
RSI := (0bv32 ++ 0bv32);
AF := unconstrained_14;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x28ec:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10481bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3200"} true;
call arbitrary_func();

label_0x28f1:
RAX := LOAD_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967208bv32));

label_0x28f5:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x28fa:
mem := STORE_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967224bv32), RAX);

label_0x28fe:
RDX := (0bv32 ++ 10000bv32);

label_0x2903:
RAX := PLUS_64((PLUS_64(14686bv64, 10506bv64)), 0bv64)[64:0];

label_0x290a:
mem := STORE_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32), RAX);

label_0x290e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10515bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3200"} true;
call arbitrary_func();

label_0x2913:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2918:
RCX := R14;

label_0x291b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x2920:
RAX := PLUS_64((PLUS_64(14657bv64, 10535bv64)), 0bv64)[64:0];

label_0x2927:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x292c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10545bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3310"} true;
call arbitrary_func();

label_0x2931:
RCX := LOAD_LE_64(mem, PLUS_64(RBP, 1472bv64));

label_0x2938:
R14 := RAX;

label_0x293b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10560bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3370"} true;
call arbitrary_func();

label_0x2940:
t_41 := MINUS_64(R14, RAX);
CF := bool2bv(LT_64(R14, RAX));
OF := AND_64((XOR_64(R14, RAX)), (XOR_64(R14, t_41)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_41, R14)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x2943:
if (bv2bool(ZF)) {
  goto label_0x2b4e;
}

label_0x2949:


label_0x2950:
t_45 := MINUS_8((LOAD_LE_8(mem, R14)), 44bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, R14)), 44bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, R14)), 44bv8)), (XOR_8((LOAD_LE_8(mem, R14)), t_45)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_45, (LOAD_LE_8(mem, R14)))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)), 2bv8)), (XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)), 2bv8)), (XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)))))[1:0]));
SF := t_45[8:7];
ZF := bool2bv(0bv8 == t_45);

label_0x2954:
RBX := R14;

label_0x2957:
if (bv2bool(ZF)) {
  goto label_0x296d;
}

label_0x2959:


label_0x2960:
t_49 := MINUS_8((LOAD_LE_8(mem, RBX)), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RBX)), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RBX)), 0bv8)), (XOR_8((LOAD_LE_8(mem, RBX)), t_49)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_49, (LOAD_LE_8(mem, RBX)))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)), 2bv8)), (XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)), 2bv8)), (XOR_8((RSHIFT_8(t_49, 4bv8)), t_49)))))[1:0]));
SF := t_49[8:7];
ZF := bool2bv(0bv8 == t_49);

label_0x2963:
if (bv2bool(ZF)) {
  goto label_0x296d;
}

label_0x2965:
t_53 := RBX;
RBX := PLUS_64(RBX, 1bv64);
OF := AND_1((bool2bv((t_53[64:63]) == (1bv64[64:63]))), (XOR_1((t_53[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t_53)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x2968:
t_57 := MINUS_8((LOAD_LE_8(mem, RBX)), 44bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RBX)), 44bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RBX)), 44bv8)), (XOR_8((LOAD_LE_8(mem, RBX)), t_57)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_57, (LOAD_LE_8(mem, RBX)))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_57, 4bv8)), t_57)), 2bv8)), (XOR_8((RSHIFT_8(t_57, 4bv8)), t_57)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_57, 4bv8)), t_57)), 2bv8)), (XOR_8((RSHIFT_8(t_57, 4bv8)), t_57)))))[1:0]));
SF := t_57[8:7];
ZF := bool2bv(0bv8 == t_57);

label_0x296b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2960;
}

label_0x296d:
t_61 := MINUS_8((LOAD_LE_8(mem, RBX)), 48bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RBX)), 48bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RBX)), 48bv8)), (XOR_8((LOAD_LE_8(mem, RBX)), t_61)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_61, (LOAD_LE_8(mem, RBX)))), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)), 2bv8)), (XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)), 2bv8)), (XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)))))[1:0]));
SF := t_61[8:7];
ZF := bool2bv(0bv8 == t_61);

label_0x2970:
if (bv2bool(ZF)) {
  goto label_0x29a4;
}

label_0x2972:
RAX := RBX;

label_0x2975:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x297b:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2981:
if (bv2bool(ZF)) {
  goto label_0x2984;
}

label_0x2983:
assume false;

label_0x2984:
RAX := RBX;

label_0x2987:
origDEST_69 := RAX;
origCOUNT_70 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), CF, LSHIFT_64(origDEST_69, (MINUS_64(64bv64, origCOUNT_70)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_70 == 1bv64)), origDEST_69[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), AF, unconstrained_18);

label_0x298b:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, (LSHIFT_64(RAX, 3bv64)))), 0bv64));

label_0x2990:
RAX := RBX;

label_0x2993:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_20);

label_0x2997:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_21;
SF := unconstrained_22;
AF := unconstrained_23;
PF := unconstrained_24;

label_0x299b:
if (bv2bool(CF)) {
  goto label_0x299e;
}

label_0x299d:
assume false;

label_0x299e:
mem := STORE_LE_8(mem, RBX, 0bv8);

label_0x29a1:
t_81 := RBX;
RBX := PLUS_64(RBX, 1bv64);
OF := AND_1((bool2bv((t_81[64:63]) == (1bv64[64:63]))), (XOR_1((t_81[64:63]), (RBX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RBX, t_81)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)), 2bv64)), (XOR_64((RSHIFT_64(RBX, 4bv64)), RBX)))))[1:0]));
SF := RBX[64:63];
ZF := bool2bv(0bv64 == RBX);

label_0x29a4:
t_85 := MINUS_8((LOAD_LE_8(mem, RBX)), 44bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RBX)), 44bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RBX)), 44bv8)), (XOR_8((LOAD_LE_8(mem, RBX)), t_85)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_85, (LOAD_LE_8(mem, RBX)))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)), 2bv8)), (XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)), 2bv8)), (XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)))))[1:0]));
SF := t_85[8:7];
ZF := bool2bv(0bv8 == t_85);

label_0x29a7:
RDI := RBX;

label_0x29aa:
if (bv2bool(ZF)) {
  goto label_0x29bd;
}

label_0x29ac:


label_0x29b0:
t_89 := MINUS_8((LOAD_LE_8(mem, RDI)), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDI)), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDI)), 0bv8)), (XOR_8((LOAD_LE_8(mem, RDI)), t_89)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_89, (LOAD_LE_8(mem, RDI)))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)), 2bv8)), (XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)), 2bv8)), (XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)))))[1:0]));
SF := t_89[8:7];
ZF := bool2bv(0bv8 == t_89);

label_0x29b3:
if (bv2bool(ZF)) {
  goto label_0x29bd;
}

label_0x29b5:
t_93 := RDI;
RDI := PLUS_64(RDI, 1bv64);
OF := AND_1((bool2bv((t_93[64:63]) == (1bv64[64:63]))), (XOR_1((t_93[64:63]), (RDI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDI, t_93)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))))[1:0]));
SF := RDI[64:63];
ZF := bool2bv(0bv64 == RDI);

label_0x29b8:
t_97 := MINUS_8((LOAD_LE_8(mem, RDI)), 44bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDI)), 44bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDI)), 44bv8)), (XOR_8((LOAD_LE_8(mem, RDI)), t_97)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_97, (LOAD_LE_8(mem, RDI)))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))))[1:0]));
SF := t_97[8:7];
ZF := bool2bv(0bv8 == t_97);

label_0x29bb:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x29b0;
}

label_0x29bd:
t_101 := MINUS_8((LOAD_LE_8(mem, RDI)), 48bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDI)), 48bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDI)), 48bv8)), (XOR_8((LOAD_LE_8(mem, RDI)), t_101)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_101, (LOAD_LE_8(mem, RDI)))), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_101, 4bv8)), t_101)), 2bv8)), (XOR_8((RSHIFT_8(t_101, 4bv8)), t_101)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_101, 4bv8)), t_101)), 2bv8)), (XOR_8((RSHIFT_8(t_101, 4bv8)), t_101)))))[1:0]));
SF := t_101[8:7];
ZF := bool2bv(0bv8 == t_101);

label_0x29c0:
if (bv2bool(ZF)) {
  goto label_0x29f4;
}

label_0x29c2:
RAX := RDI;

label_0x29c5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29cb:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29d1:
if (bv2bool(ZF)) {
  goto label_0x29d4;
}

label_0x29d3:
assume false;

label_0x29d4:
RAX := RDI;

label_0x29d7:
origDEST_109 := RAX;
origCOUNT_110 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), CF, LSHIFT_64(origDEST_109, (MINUS_64(64bv64, origCOUNT_110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_110 == 1bv64)), origDEST_109[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_110 == 0bv64)), AF, unconstrained_28);

label_0x29db:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(R13, (LSHIFT_64(RAX, 3bv64)))), 0bv64));

label_0x29e0:
RAX := RDI;

label_0x29e3:
origDEST_115 := RAX;
origCOUNT_116 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), CF, LSHIFT_64(origDEST_115, (MINUS_64(64bv64, origCOUNT_116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_116 == 1bv64)), origDEST_115[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_116 == 0bv64)), AF, unconstrained_30);

label_0x29e7:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x29eb:
if (bv2bool(CF)) {
  goto label_0x29ee;
}

label_0x29ed:
assume false;

label_0x29ee:
mem := STORE_LE_8(mem, RDI, 0bv8);

label_0x29f1:
t_121 := RDI;
RDI := PLUS_64(RDI, 1bv64);
OF := AND_1((bool2bv((t_121[64:63]) == (1bv64[64:63]))), (XOR_1((t_121[64:63]), (RDI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDI, t_121)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))))[1:0]));
SF := RDI[64:63];
ZF := bool2bv(0bv64 == RDI);

label_0x29f4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, R14)));

label_0x29f8:
t_125 := MINUS_8((RAX[32:0][8:0]), 69bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 69bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 69bv8)), (XOR_8((RAX[32:0][8:0]), t_125)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_125, (RAX[32:0][8:0]))), 69bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_125, 4bv8)), t_125)), 2bv8)), (XOR_8((RSHIFT_8(t_125, 4bv8)), t_125)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_125, 4bv8)), t_125)), 2bv8)), (XOR_8((RSHIFT_8(t_125, 4bv8)), t_125)))))[1:0]));
SF := t_125[8:7];
ZF := bool2bv(0bv8 == t_125);

label_0x29fa:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2a40;
}

label_0x29fc:
R8 := (R8[64:8]) ++ 1bv8;

label_0x29ff:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x2a03:
RDX := RBX;

label_0x2a06:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10763bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ce0"} true;
call arbitrary_func();

label_0x2a0b:
RDI := LOAD_LE_64(mem, PLUS_64(RBP, 1232bv64));

label_0x2a12:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2a17:
t_129 := RDI;
RDI := PLUS_64(RDI, 1bv64);
OF := AND_1((bool2bv((t_129[64:63]) == (1bv64[64:63]))), (XOR_1((t_129[64:63]), (RDI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDI, t_129)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))))[1:0]));
SF := RDI[64:63];
ZF := bool2bv(0bv64 == RDI);

label_0x2a1a:
RDX := RBX;

label_0x2a1d:
mem := STORE_LE_64(mem, PLUS_64(RBP, 1232bv64), RDI);

label_0x2a24:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10793bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1430"} true;
call arbitrary_func();

label_0x2a29:
t_133 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))))[1:0]));
SF := t_133[64:63];
ZF := bool2bv(0bv64 == t_133);

label_0x2a2c:
if (bv2bool(ZF)) {
  goto label_0x2b23;
}

label_0x2a32:
RAX := LOAD_LE_64(mem, RAX);

label_0x2a35:
t1_137 := R15;
t2_138 := RAX;
R15 := PLUS_64(R15, t2_138);
CF := bool2bv(LT_64(R15, t1_137));
OF := AND_1((bool2bv((t1_137[64:63]) == (t2_138[64:63]))), (XOR_1((t1_137[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t1_137)), t2_138)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x2a38:
t_143 := RSI;
RSI := MINUS_64(RSI, RAX);
CF := bool2bv(LT_64(t_143, RAX));
OF := AND_64((XOR_64(t_143, RAX)), (XOR_64(t_143, RSI)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSI, t_143)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))))[1:0]));
SF := RSI[64:63];
ZF := bool2bv(0bv64 == RSI);

label_0x2a3b:
goto label_0x2b23;

label_0x2a40:
t_147 := MINUS_8((RAX[32:0][8:0]), 73bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 73bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 73bv8)), (XOR_8((RAX[32:0][8:0]), t_147)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_147, (RAX[32:0][8:0]))), 73bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_147, 4bv8)), t_147)), 2bv8)), (XOR_8((RSHIFT_8(t_147, 4bv8)), t_147)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_147, 4bv8)), t_147)), 2bv8)), (XOR_8((RSHIFT_8(t_147, 4bv8)), t_147)))))[1:0]));
SF := t_147[8:7];
ZF := bool2bv(0bv8 == t_147);

label_0x2a42:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2a85;
}

label_0x2a44:
R8 := (R8[64:8]) ++ 1bv8;

label_0x2a47:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x2a4b:
RDX := RBX;

label_0x2a4e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10835bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ce0"} true;
call arbitrary_func();

label_0x2a53:
t_151 := LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64));
mem := STORE_LE_64(mem, PLUS_64(RBP, 1256bv64), PLUS_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), 1bv64));
OF := AND_1((bool2bv((t_151[64:63]) == (1bv64[64:63]))), (XOR_1((t_151[64:63]), (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), t_151)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64))));

label_0x2a5a:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2a5f:
RDX := RBX;

label_0x2a62:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10855bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1430"} true;
call arbitrary_func();

label_0x2a67:
RDI := LOAD_LE_64(mem, PLUS_64(RBP, 1232bv64));

label_0x2a6e:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x2a71:
if (bv2bool(ZF)) {
  goto label_0x2b23;
}

label_0x2a77:
RAX := LOAD_LE_64(mem, RAX);

label_0x2a7a:
t1_159 := R12;
t2_160 := RAX;
R12 := PLUS_64(R12, t2_160);
CF := bool2bv(LT_64(R12, t1_159));
OF := AND_1((bool2bv((t1_159[64:63]) == (t2_160[64:63]))), (XOR_1((t1_159[64:63]), (R12[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R12, t1_159)), t2_160)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))))[1:0]));
SF := R12[64:63];
ZF := bool2bv(0bv64 == R12);

label_0x2a7d:
t_165 := RSI;
RSI := MINUS_64(RSI, RAX);
CF := bool2bv(LT_64(t_165, RAX));
OF := AND_64((XOR_64(t_165, RAX)), (XOR_64(t_165, RSI)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSI, t_165)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))))[1:0]));
SF := RSI[64:63];
ZF := bool2bv(0bv64 == RSI);

label_0x2a80:
goto label_0x2b23;

label_0x2a85:
t_169 := MINUS_8((RAX[32:0][8:0]), 66bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 66bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 66bv8)), (XOR_8((RAX[32:0][8:0]), t_169)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_169, (RAX[32:0][8:0]))), 66bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_169, 4bv8)), t_169)), 2bv8)), (XOR_8((RSHIFT_8(t_169, 4bv8)), t_169)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_169, 4bv8)), t_169)), 2bv8)), (XOR_8((RSHIFT_8(t_169, 4bv8)), t_169)))))[1:0]));
SF := t_169[8:7];
ZF := bool2bv(0bv8 == t_169);

label_0x2a87:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2add;
}

label_0x2a89:
RCX := RDI;

label_0x2a8c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10897bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1390"} true;
call arbitrary_func();

label_0x2a91:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_37;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2a93:
RCX := RDI;

label_0x2a96:
R8 := (0bv32 ++ PLUS_64(RDX, 10bv64)[32:0]);

label_0x2a9a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10911bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x33e0"} true;
call arbitrary_func();

label_0x2a9f:
RDX := RBX;

label_0x2aa2:
RDI := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2aa5:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x2aa9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10926bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1430"} true;
call arbitrary_func();

label_0x2aae:
t_173 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))))[1:0]));
SF := t_173[64:63];
ZF := bool2bv(0bv64 == t_173);

label_0x2ab1:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2ac8;
}

label_0x2ab3:
R8 := RDI;

label_0x2ab6:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2abb:
RDX := RBX;

label_0x2abe:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10947bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1a60"} true;
call arbitrary_func();

label_0x2ac3:
t1_177 := RSI;
t2_178 := RDI;
RSI := PLUS_64(RSI, t2_178);
CF := bool2bv(LT_64(RSI, t1_177));
OF := AND_1((bool2bv((t1_177[64:63]) == (t2_178[64:63]))), (XOR_1((t1_177[64:63]), (RSI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSI, t1_177)), t2_178)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))))[1:0]));
SF := RSI[64:63];
ZF := bool2bv(0bv64 == RSI);

label_0x2ac6:
goto label_0x2b1c;

label_0x2ac8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0x2acb:
t_183 := MINUS_8((RAX[32:0][8:0]), 1bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 1bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 1bv8)), (XOR_8((RAX[32:0][8:0]), t_183)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_183, (RAX[32:0][8:0]))), 1bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_183, 4bv8)), t_183)), 2bv8)), (XOR_8((RSHIFT_8(t_183, 4bv8)), t_183)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_183, 4bv8)), t_183)), 2bv8)), (XOR_8((RSHIFT_8(t_183, 4bv8)), t_183)))))[1:0]));
SF := t_183[8:7];
ZF := bool2bv(0bv8 == t_183);

label_0x2acd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2ad4;
}

label_0x2acf:
t1_187 := R15;
t2_188 := RDI;
R15 := PLUS_64(R15, t2_188);
CF := bool2bv(LT_64(R15, t1_187));
OF := AND_1((bool2bv((t1_187[64:63]) == (t2_188[64:63]))), (XOR_1((t1_187[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t1_187)), t2_188)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x2ad2:
goto label_0x2b1c;

label_0x2ad4:
t_193 := AND_8((RAX[32:0][8:0]), (RAX[32:0][8:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_39;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)), 2bv8)), (XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)), 2bv8)), (XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)))))[1:0]));
SF := t_193[8:7];
ZF := bool2bv(0bv8 == t_193);

label_0x2ad6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2b1c;
}

label_0x2ad8:
t1_197 := R12;
t2_198 := RDI;
R12 := PLUS_64(R12, t2_198);
CF := bool2bv(LT_64(R12, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (R12[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R12, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))))[1:0]));
SF := R12[64:63];
ZF := bool2bv(0bv64 == R12);

label_0x2adb:
goto label_0x2b1c;

label_0x2add:
t_203 := MINUS_8((RAX[32:0][8:0]), 83bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 83bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 83bv8)), (XOR_8((RAX[32:0][8:0]), t_203)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_203, (RAX[32:0][8:0]))), 83bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_203, 4bv8)), t_203)), 2bv8)), (XOR_8((RSHIFT_8(t_203, 4bv8)), t_203)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_203, 4bv8)), t_203)), 2bv8)), (XOR_8((RSHIFT_8(t_203, 4bv8)), t_203)))))[1:0]));
SF := t_203[8:7];
ZF := bool2bv(0bv8 == t_203);

label_0x2adf:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2b1c;
}

label_0x2ae1:
RCX := RDI;

label_0x2ae4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10985bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1390"} true;
call arbitrary_func();

label_0x2ae9:
RCX := RAX;

label_0x2aec:
RBX := RAX;

label_0x2aef:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10996bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1390"} true;
call arbitrary_func();

label_0x2af4:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_40;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2af6:
RCX := RDI;

label_0x2af9:
R8 := (0bv32 ++ PLUS_64(RDX, 10bv64)[32:0]);

label_0x2afd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11010bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x33e0"} true;
call arbitrary_func();

label_0x2b02:
RDX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2b05:
RCX := RBX;

label_0x2b08:
t1_207 := R15;
t2_208 := RDX;
R15 := PLUS_64(R15, t2_208);
CF := bool2bv(LT_64(R15, t1_207));
OF := AND_1((bool2bv((t1_207[64:63]) == (t2_208[64:63]))), (XOR_1((t1_207[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t1_207)), t2_208)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x2b0b:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_41;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2b0d:
R8 := (0bv32 ++ PLUS_64(RDX, 10bv64)[32:0]);

label_0x2b11:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11030bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x33e0"} true;
call arbitrary_func();

label_0x2b16:
RCX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2b19:
t1_213 := R12;
t2_214 := RCX;
R12 := PLUS_64(R12, t2_214);
CF := bool2bv(LT_64(R12, t1_213));
OF := AND_1((bool2bv((t1_213[64:63]) == (t2_214[64:63]))), (XOR_1((t1_213[64:63]), (R12[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R12, t1_213)), t2_214)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R12, 4bv64)), R12)), 2bv64)), (XOR_64((RSHIFT_64(R12, 4bv64)), R12)))))[1:0]));
SF := R12[64:63];
ZF := bool2bv(0bv64 == R12);

label_0x2b1c:
RDI := LOAD_LE_64(mem, PLUS_64(RBP, 1232bv64));

label_0x2b23:
RCX := LOAD_LE_64(mem, PLUS_64(RBP, 1472bv64));

label_0x2b2a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11055bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3380"} true;
call arbitrary_func();

label_0x2b2f:
RCX := LOAD_LE_64(mem, PLUS_64(RBP, 1472bv64));

label_0x2b36:
R14 := RAX;

label_0x2b39:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11070bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3370"} true;
call arbitrary_func();

label_0x2b3e:
t_219 := MINUS_64(R14, RAX);
CF := bool2bv(LT_64(R14, RAX));
OF := AND_64((XOR_64(R14, RAX)), (XOR_64(R14, t_219)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_219, R14)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)), 2bv64)), (XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)), 2bv64)), (XOR_64((RSHIFT_64(t_219, 4bv64)), t_219)))))[1:0]));
SF := t_219[64:63];
ZF := bool2bv(0bv64 == t_219);

label_0x2b41:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2950;
}

label_0x2b47:
RBX := LOAD_LE_64(mem, PLUS_64(RBP, 1256bv64));

label_0x2b4e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RBX);

label_0x2b53:
R8 := PLUS_64((PLUS_64(14118bv64, 11098bv64)), 0bv64)[64:0];

label_0x2b5a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RDI);

label_0x2b5f:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967264bv32)[64:0];

label_0x2b63:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RSI);

label_0x2b68:
R9 := (0bv32 ++ 83bv32);

label_0x2b6e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), R12);

label_0x2b73:
RDX := (0bv32 ++ 1024bv32);

label_0x2b78:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R15);

label_0x2b7d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11138bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38c0"} true;
call arbitrary_func();

label_0x2b82:
RCX := (0bv32 ++ 32bv32);

label_0x2b87:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11148bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f60"} true;
call arbitrary_func();

label_0x2b8c:
t_223 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))))[1:0]));
SF := t_223[64:63];
ZF := bool2bv(0bv64 == t_223);

label_0x2b8f:
if (bv2bool(ZF)) {
  goto label_0x2ba5;
}

label_0x2b91:
RDX := PLUS_64(RBP, 4294967295bv32 ++ 4294967264bv32)[64:0];

label_0x2b95:
RCX := RAX;

label_0x2b98:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11165bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3010"} true;
call arbitrary_func();

label_0x2b9d:
RSI := RAX;

label_0x2ba0:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_43;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2ba3:
goto label_0x2bab;

label_0x2ba5:
R15 := (0bv32 ++ 0bv32);
AF := unconstrained_44;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2ba8:
RSI := (0bv32 ++ R15[32:0]);

label_0x2bab:
RCX := (0bv32 ++ 32bv32);

label_0x2bb0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11189bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f60"} true;
call arbitrary_func();

label_0x2bb5:
t_227 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_227, 4bv64)), t_227)), 2bv64)), (XOR_64((RSHIFT_64(t_227, 4bv64)), t_227)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_227, 4bv64)), t_227)), 2bv64)), (XOR_64((RSHIFT_64(t_227, 4bv64)), t_227)))))[1:0]));
SF := t_227[64:63];
ZF := bool2bv(0bv64 == t_227);

label_0x2bb8:
if (bv2bool(ZF)) {
  goto label_0x2bce;
}

label_0x2bba:
RDX := LOAD_LE_64(mem, PLUS_64(RBP, 1464bv64));

label_0x2bc1:
RCX := RAX;

label_0x2bc4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11209bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3010"} true;
call arbitrary_func();

label_0x2bc9:
RDI := RAX;

label_0x2bcc:
goto label_0x2bd1;

label_0x2bce:
RDI := R15;

label_0x2bd1:
R14 := LOAD_LE_64(mem, PLUS_64(RBP, 1480bv64));

label_0x2bd8:
RAX := LOAD_LE_64(mem, R14);

label_0x2bdb:
RBX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x2bdf:
RCX := RBX;

label_0x2be2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11239bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x50d0"} true;
call arbitrary_func();

label_0x2be7:
R8 := RSI;

label_0x2bea:
RDX := RDI;

label_0x2bed:
RCX := R14;

label_0x2bf0:

target_231 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11250bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_231"} true;
call arbitrary_func();

label_0x2bf2:
RAX := PLUS_64((PLUS_64(13911bv64, 11257bv64)), 0bv64)[64:0];

label_0x2bf9:
mem := STORE_LE_32(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967176bv32), R15[32:0]);

label_0x2bfd:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2c02:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x2c07:
mem := STORE_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967168bv32), R15);

label_0x2c0b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11280bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2760"} true;
call arbitrary_func();

label_0x2c10:
t_233 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))))[1:0]));
SF := t_233[64:63];
ZF := bool2bv(0bv64 == t_233);

label_0x2c13:
if (bv2bool(ZF)) {
  goto label_0x2c2c;
}

label_0x2c15:
RCX := RAX;

label_0x2c18:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11293bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f70"} true;
call arbitrary_func();

label_0x2c1d:
RCX := PLUS_64(RSP, 96bv64)[64:0];

label_0x2c22:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11303bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2760"} true;
call arbitrary_func();

label_0x2c27:
t_237 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))))[1:0]));
SF := t_237[64:63];
ZF := bool2bv(0bv64 == t_237);

label_0x2c2a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2c15;
}

label_0x2c2c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x2c31:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11318bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f70"} true;
call arbitrary_func();

label_0x2c36:
RAX := PLUS_64((PLUS_64(13643bv64, 11325bv64)), 0bv64)[64:0];

label_0x2c3d:
mem := STORE_LE_32(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967240bv32), R15[32:0]);

label_0x2c41:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x2c46:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x2c4a:
RAX := PLUS_64((PLUS_64(13823bv64, 11345bv64)), 0bv64)[64:0];

label_0x2c51:
mem := STORE_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967232bv32), R15);

label_0x2c55:
mem := STORE_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32), RAX);

label_0x2c59:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11358bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2760"} true;
call arbitrary_func();

label_0x2c5e:
t_241 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))))[1:0]));
SF := t_241[64:63];
ZF := bool2bv(0bv64 == t_241);

label_0x2c61:
if (bv2bool(ZF)) {
  goto label_0x2c79;
}

label_0x2c63:
RCX := RAX;

label_0x2c66:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11371bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f70"} true;
call arbitrary_func();

label_0x2c6b:
RCX := PLUS_64(RBP, 4294967295bv32 ++ 4294967200bv32)[64:0];

label_0x2c6f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11380bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2760"} true;
call arbitrary_func();

label_0x2c74:
t_245 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_245, 4bv64)), t_245)), 2bv64)), (XOR_64((RSHIFT_64(t_245, 4bv64)), t_245)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_245, 4bv64)), t_245)), 2bv64)), (XOR_64((RSHIFT_64(t_245, 4bv64)), t_245)))))[1:0]));
SF := t_245[64:63];
ZF := bool2bv(0bv64 == t_245);

label_0x2c77:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2c63;
}

label_0x2c79:
RCX := LOAD_LE_64(mem, PLUS_64(RBP, 4294967295bv32 ++ 4294967224bv32));

label_0x2c7d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11394bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f70"} true;
call arbitrary_func();

label_0x2c82:
RAX := PLUS_64(RBP, 992bv64)[64:0];

label_0x2c89:
origDEST_249 := RAX;
origCOUNT_250 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), CF, LSHIFT_64(origDEST_249, (MINUS_64(64bv64, origCOUNT_250)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_250 == 1bv64)), origDEST_249[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), AF, unconstrained_51);

label_0x2c8d:
RCX := PLUS_64(RBP, 992bv64)[64:0];

label_0x2c94:
t1_255 := R13;
t2_256 := RAX;
R13 := PLUS_64(R13, t2_256);
CF := bool2bv(LT_64(R13, t1_255));
OF := AND_1((bool2bv((t1_255[64:63]) == (t2_256[64:63]))), (XOR_1((t1_255[64:63]), (R13[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R13, t1_255)), t2_256)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R13, 4bv64)), R13)), 2bv64)), (XOR_64((RSHIFT_64(R13, 4bv64)), R13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R13, 4bv64)), R13)), 2bv64)), (XOR_64((RSHIFT_64(R13, 4bv64)), R13)))))[1:0]));
SF := R13[64:63];
ZF := bool2bv(0bv64 == R13);

label_0x2c97:
origDEST_261 := RCX;
origCOUNT_262 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_53);

label_0x2c9b:
RAX := (0bv32 ++ 254bv32);

label_0x2ca0:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2ca3:
origDEST_269 := RAX[32:0][8:0];
origCOUNT_270 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), CF, RSHIFT_8(origDEST_269, (MINUS_8(8bv8, origCOUNT_270)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv8)), AF, unconstrained_56);

label_0x2ca5:
mem := STORE_LE_8(mem, PLUS_64(R13, 0bv64), AND_8((LOAD_LE_8(mem, PLUS_64(R13, 0bv64))), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(R13, 0bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(R13, 0bv64))))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(R13, 0bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(R13, 0bv64))))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(R13, 0bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(R13, 0bv64))))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, PLUS_64(R13, 0bv64))), 4bv8)), (LOAD_LE_8(mem, PLUS_64(R13, 0bv64))))))))[1:0]));
SF := LOAD_LE_8(mem, PLUS_64(R13, 0bv64))[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, PLUS_64(R13, 0bv64))));

label_0x2ca9:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_58;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2cab:
mem := STORE_LE_64(mem, PLUS_64(R13, 4294967295bv32 ++ 4294967277bv32), RAX);

label_0x2caf:
mem := STORE_LE_64(mem, PLUS_64(R13, 4294967295bv32 ++ 4294967285bv32), RAX);

label_0x2cb3:
mem := STORE_LE_16(mem, PLUS_64(R13, 4294967295bv32 ++ 4294967293bv32), RAX[32:0][16:0]);

label_0x2cb8:
mem := STORE_LE_8(mem, PLUS_64(R13, 4294967295bv32 ++ 4294967295bv32), RAX[32:0][8:0]);

label_0x2cbc:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 1712bv64));

label_0x2cc4:
t1_277 := RSP;
t2_278 := 1648bv64;
RSP := PLUS_64(RSP, t2_278);
CF := bool2bv(LT_64(RSP, t1_277));
OF := AND_1((bool2bv((t1_277[64:63]) == (t2_278[64:63]))), (XOR_1((t1_277[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_277)), t2_278)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2ccb:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2ccd:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2ccf:
R13 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2cd1:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2cd3:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2cd4:
RSI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2cd5:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x2cd6:

ra_283 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R12,R13,R14,R15,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_110,origCOUNT_116,origCOUNT_20,origCOUNT_250,origCOUNT_262,origCOUNT_270,origCOUNT_28,origCOUNT_34,origCOUNT_70,origCOUNT_76,origDEST_109,origDEST_115,origDEST_19,origDEST_249,origDEST_261,origDEST_269,origDEST_27,origDEST_33,origDEST_69,origDEST_75,ra_283,t1_137,t1_159,t1_177,t1_187,t1_197,t1_207,t1_213,t1_255,t1_277,t2_138,t2_160,t2_178,t2_188,t2_198,t2_208,t2_214,t2_256,t2_278,t_1,t_101,t_11,t_121,t_125,t_129,t_13,t_133,t_143,t_147,t_15,t_151,t_155,t_165,t_169,t_173,t_183,t_193,t_203,t_219,t_223,t_227,t_233,t_237,t_241,t_245,t_3,t_41,t_45,t_49,t_5,t_53,t_57,t_61,t_7,t_81,t_85,t_89,t_9,t_93,t_97,target_231;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R11: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R12: bv64;
var R13: bv64;
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
var origCOUNT_116: bv64;
var origCOUNT_20: bv64;
var origCOUNT_250: bv64;
var origCOUNT_262: bv64;
var origCOUNT_270: bv8;
var origCOUNT_28: bv64;
var origCOUNT_34: bv64;
var origCOUNT_70: bv64;
var origCOUNT_76: bv64;
var origDEST_109: bv64;
var origDEST_115: bv64;
var origDEST_19: bv64;
var origDEST_249: bv64;
var origDEST_261: bv64;
var origDEST_269: bv8;
var origDEST_27: bv64;
var origDEST_33: bv64;
var origDEST_69: bv64;
var origDEST_75: bv64;
var ra_283: bv64;
var t1_137: bv64;
var t1_159: bv64;
var t1_177: bv64;
var t1_187: bv64;
var t1_197: bv64;
var t1_207: bv64;
var t1_213: bv64;
var t1_255: bv64;
var t1_277: bv64;
var t2_138: bv64;
var t2_160: bv64;
var t2_178: bv64;
var t2_188: bv64;
var t2_198: bv64;
var t2_208: bv64;
var t2_214: bv64;
var t2_256: bv64;
var t2_278: bv64;
var t_1: bv64;
var t_101: bv8;
var t_11: bv64;
var t_121: bv64;
var t_125: bv8;
var t_129: bv64;
var t_13: bv64;
var t_133: bv64;
var t_143: bv64;
var t_147: bv8;
var t_15: bv64;
var t_151: bv64;
var t_155: bv64;
var t_165: bv64;
var t_169: bv8;
var t_173: bv64;
var t_183: bv8;
var t_193: bv8;
var t_203: bv8;
var t_219: bv64;
var t_223: bv64;
var t_227: bv64;
var t_233: bv64;
var t_237: bv64;
var t_241: bv64;
var t_245: bv64;
var t_3: bv64;
var t_41: bv64;
var t_45: bv8;
var t_49: bv8;
var t_5: bv64;
var t_53: bv64;
var t_57: bv8;
var t_61: bv8;
var t_7: bv64;
var t_81: bv64;
var t_85: bv8;
var t_89: bv8;
var t_9: bv64;
var t_93: bv64;
var t_97: bv8;
var target_231: bv64;


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
