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
axiom _function_addr_low == 5328bv64;
axiom _function_addr_high == 5628bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x14d0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RBX);

label_0x14d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RBP);

label_0x14da:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RSI);

label_0x14df:
t_1 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x14e1:
t_3 := RSP;
RSP := MINUS_64(RSP, 32bv64);
CF := bool2bv(LT_64(t_3, 32bv64));
OF := AND_64((XOR_64(t_3, 32bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 32bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x14e5:
RBP := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x14e7:
R14 := R9;

label_0x14ea:
RBX := (0bv32 ++ RBP[32:0]);

label_0x14ec:
R10 := (0bv32 ++ RBP[32:0]);

label_0x14ef:
RSI := (0bv32 ++ RBP[32:0]);

label_0x14f1:
t_7 := MINUS_8((LOAD_LE_8(mem, R8)), (RBX[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, R8)), (RBX[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, R8)), (RBX[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, R8)), t_7)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_7, (LOAD_LE_8(mem, R8)))), (RBX[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)), 2bv8)), (XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)), 2bv8)), (XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)))))[1:0]));
SF := t_7[8:7];
ZF := bool2bv(0bv8 == t_7);

label_0x14f4:
if (bv2bool(ZF)) {
  goto label_0x15e6;
}

label_0x14fa:
R11 := LOAD_LE_64(mem, PLUS_64((PLUS_64(24511bv64, 5377bv64)), 0bv64));

label_0x1501:
t_11 := MINUS_8((LOAD_LE_8(mem, R8)), 9bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, R8)), 9bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, R8)), 9bv8)), (XOR_8((LOAD_LE_8(mem, R8)), t_11)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_11, (LOAD_LE_8(mem, R8)))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)), 2bv8)), (XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)), 2bv8)), (XOR_8((RSHIFT_8(t_11, 4bv8)), t_11)))))[1:0]));
SF := t_11[8:7];
ZF := bool2bv(0bv8 == t_11);

label_0x1505:
R9 := R8;

label_0x1508:
RAX := R8;

label_0x150b:
if (bv2bool(ZF)) {
  goto label_0x151d;
}

label_0x150d:


label_0x1510:
t_15 := MINUS_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RAX)), t_15)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_15, (LOAD_LE_8(mem, RAX)))), (RBP[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)), 2bv8)), (XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)), 2bv8)), (XOR_8((RSHIFT_8(t_15, 4bv8)), t_15)))))[1:0]));
SF := t_15[8:7];
ZF := bool2bv(0bv8 == t_15);

label_0x1513:
if (bv2bool(ZF)) {
  goto label_0x151d;
}

label_0x1515:
t_19 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_19[64:63]) == (1bv64[64:63]))), (XOR_1((t_19[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_19)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1518:
t_23 := MINUS_8((LOAD_LE_8(mem, RAX)), 9bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), 9bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), 9bv8)), (XOR_8((LOAD_LE_8(mem, RAX)), t_23)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_23, (LOAD_LE_8(mem, RAX)))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_23, 4bv8)), t_23)), 2bv8)), (XOR_8((RSHIFT_8(t_23, 4bv8)), t_23)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_23, 4bv8)), t_23)), 2bv8)), (XOR_8((RSHIFT_8(t_23, 4bv8)), t_23)))))[1:0]));
SF := t_23[8:7];
ZF := bool2bv(0bv8 == t_23);

label_0x151b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1510;
}

label_0x151d:
t_27 := MINUS_8((LOAD_LE_8(mem, RAX)), 48bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), 48bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), 48bv8)), (XOR_8((LOAD_LE_8(mem, RAX)), t_27)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_27, (LOAD_LE_8(mem, RAX)))), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_27, 4bv8)), t_27)), 2bv8)), (XOR_8((RSHIFT_8(t_27, 4bv8)), t_27)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_27, 4bv8)), t_27)), 2bv8)), (XOR_8((RSHIFT_8(t_27, 4bv8)), t_27)))))[1:0]));
SF := t_27[8:7];
ZF := bool2bv(0bv8 == t_27);

label_0x1520:
if (bv2bool(ZF)) {
  goto label_0x1555;
}

label_0x1522:
RCX := RAX;

label_0x1525:
RCX := AND_64(RCX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x152c:
RCX := XOR_64(RCX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1533:
if (bv2bool(ZF)) {
  goto label_0x1536;
}

label_0x1535:
assume false;

label_0x1536:
RCX := RAX;

label_0x1539:
origDEST_35 := RCX;
origCOUNT_36 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_5);

label_0x153d:
RDX := LOAD_LE_64(mem, PLUS_64(R11, (LSHIFT_64(RCX, 3bv64))));

label_0x1541:
RCX := RAX;

label_0x1544:
origDEST_41 := RCX;
origCOUNT_42 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_7);

label_0x1548:
CF := RSHIFT_64(RDX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x154c:
if (bv2bool(CF)) {
  goto label_0x154f;
}

label_0x154e:
assume false;

label_0x154f:
mem := STORE_LE_8(mem, RAX, RBP[32:0][8:0]);

label_0x1552:
t_47 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_47[64:63]) == (1bv64[64:63]))), (XOR_1((t_47[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_47)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1555:
R8 := RAX;

label_0x1558:
t_51 := AND_32((R10[32:0]), (R10[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_51, 4bv32)), t_51)), 2bv32)), (XOR_32((RSHIFT_32(t_51, 4bv32)), t_51)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_51, 4bv32)), t_51)), 2bv32)), (XOR_32((RSHIFT_32(t_51, 4bv32)), t_51)))))[1:0]));
SF := t_51[32:31];
ZF := bool2bv(0bv32 == t_51);

label_0x155b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1562;
}

label_0x155d:
RSI := R9;

label_0x1560:
goto label_0x1579;

label_0x1562:
t_55 := MINUS_32((R10[32:0]), 2bv32);
CF := bool2bv(LT_32((R10[32:0]), 2bv32));
OF := AND_32((XOR_32((R10[32:0]), 2bv32)), (XOR_32((R10[32:0]), t_55)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_55, (R10[32:0]))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))))[1:0]));
SF := t_55[32:31];
ZF := bool2bv(0bv32 == t_55);

label_0x1566:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x156d;
}

label_0x1568:
RBX := R9;

label_0x156b:
goto label_0x1579;

label_0x156d:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1579;
}

label_0x156f:
t_59 := AND_64(RSI, RSI);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))))[1:0]));
SF := t_59[64:63];
ZF := bool2bv(0bv64 == t_59);

label_0x1572:
if (bv2bool(ZF)) {
  goto label_0x1579;
}

label_0x1574:
t_63 := AND_64(RBX, RBX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))))[1:0]));
SF := t_63[64:63];
ZF := bool2bv(0bv64 == t_63);

label_0x1577:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1583;
}

label_0x1579:
t_67 := R10[32:0];
R10 := (0bv32 ++ PLUS_32((R10[32:0]), 1bv32));
OF := AND_1((bool2bv((t_67[32:31]) == (1bv32[32:31]))), (XOR_1((t_67[32:31]), (R10[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((R10[32:0]), t_67)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R10[32:0]), 4bv32)), (R10[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R10[32:0]), 4bv32)), (R10[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R10[32:0]), 4bv32)), (R10[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R10[32:0]), 4bv32)), (R10[32:0]))))))[1:0]));
SF := R10[32:0][32:31];
ZF := bool2bv(0bv32 == (R10[32:0]));

label_0x157c:
t_71 := MINUS_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RAX)), (RBP[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RAX)), t_71)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_71, (LOAD_LE_8(mem, RAX)))), (RBP[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_71, 4bv8)), t_71)), 2bv8)), (XOR_8((RSHIFT_8(t_71, 4bv8)), t_71)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_71, 4bv8)), t_71)), 2bv8)), (XOR_8((RSHIFT_8(t_71, 4bv8)), t_71)))))[1:0]));
SF := t_71[8:7];
ZF := bool2bv(0bv8 == t_71);

label_0x157f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1501;
}

label_0x1581:
goto label_0x15e6;

label_0x1583:
RCX := (0bv32 ++ 32bv32);

label_0x1588:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RDI);

label_0x158d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5522bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1880"} true;
call arbitrary_func();

label_0x1592:
t_75 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))))[1:0]));
SF := t_75[64:63];
ZF := bool2bv(0bv64 == t_75);

label_0x1595:
if (bv2bool(ZF)) {
  goto label_0x15a7;
}

label_0x1597:
RDX := RBX;

label_0x159a:
RCX := RAX;

label_0x159d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5538bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x18d0"} true;
call arbitrary_func();

label_0x15a2:
RDI := RAX;

label_0x15a5:
goto label_0x15aa;

label_0x15a7:
RDI := RBP;

label_0x15aa:
RCX := (0bv32 ++ 32bv32);

label_0x15af:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5556bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1880"} true;
call arbitrary_func();

label_0x15b4:
t_79 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))))[1:0]));
SF := t_79[64:63];
ZF := bool2bv(0bv64 == t_79);

label_0x15b7:
if (bv2bool(ZF)) {
  goto label_0x15c7;
}

label_0x15b9:
RDX := RSI;

label_0x15bc:
RCX := RAX;

label_0x15bf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5572bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x18d0"} true;
call arbitrary_func();

label_0x15c4:
RBP := RAX;

label_0x15c7:
RAX := LOAD_LE_64(mem, R14);

label_0x15ca:
RBX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x15ce:
RCX := RBX;

label_0x15d1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5590bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5210"} true;
call arbitrary_func();

label_0x15d6:
R8 := RDI;

label_0x15d9:
RDX := RBP;

label_0x15dc:
RCX := R14;

label_0x15df:

target_83 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5601bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_83"} true;
call arbitrary_func();

label_0x15e1:
RDI := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15e6:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x15eb:
RBP := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15f0:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x15f5:
t1_85 := RSP;
t2_86 := 32bv64;
RSP := PLUS_64(RSP, t2_86);
CF := bool2bv(LT_64(RSP, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x15f9:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x15fb:

ra_91 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R11,R14,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_36,origCOUNT_42,origDEST_35,origDEST_41,ra_91,t1_85,t2_86,t_1,t_11,t_15,t_19,t_23,t_27,t_3,t_47,t_51,t_55,t_59,t_63,t_67,t_7,t_71,t_75,t_79,target_83;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_12: bv1;
const unconstrained_13: bv1;
const unconstrained_14: bv1;
const unconstrained_15: bv1;
const unconstrained_16: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R12: bv64;
var R13: bv64;
var R15: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R11: bv64;
var R14: bv64;
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
var origCOUNT_36: bv64;
var origCOUNT_42: bv64;
var origDEST_35: bv64;
var origDEST_41: bv64;
var ra_91: bv64;
var t1_85: bv64;
var t2_86: bv64;
var t_1: bv64;
var t_11: bv8;
var t_15: bv8;
var t_19: bv64;
var t_23: bv8;
var t_27: bv8;
var t_3: bv64;
var t_47: bv64;
var t_51: bv32;
var t_55: bv32;
var t_59: bv64;
var t_63: bv64;
var t_67: bv32;
var t_7: bv8;
var t_71: bv8;
var t_75: bv64;
var t_79: bv64;
var target_83: bv64;


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
