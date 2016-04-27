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
axiom _function_addr_low == 8032bv64;
axiom _function_addr_high == 9501bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x1f60:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1f62:
R9 := RCX;

label_0x1f65:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(20684bv64, 8044bv64)), 0bv64), RAX);

label_0x1f6c:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(20685bv64, 8051bv64)), 0bv64), RAX);

label_0x1f73:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20687bv64, 8057bv64)), 0bv64), RAX[32:0][8:0]);

label_0x1f79:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x1f7c:
R8 := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, 1bv64))));

label_0x1f81:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x1f84:
t_1 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_1)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_1, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_1, 4bv8)), t_1)), 2bv8)), (XOR_8((RSHIFT_8(t_1, 4bv8)), t_1)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_1, 4bv8)), t_1)), 2bv8)), (XOR_8((RSHIFT_8(t_1, 4bv8)), t_1)))))[1:0]));
SF := t_1[8:7];
ZF := bool2bv(0bv8 == t_1);

label_0x1f86:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1f8d;
}

label_0x1f88:
t_5 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_5, 48bv8));
OF := AND_8((XOR_8(t_5, 48bv8)), (XOR_8(t_5, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_5)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x1f8b:
goto label_0x1f9b;

label_0x1f8d:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x1f90:
t_9 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_9)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_9, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_9, 4bv8)), t_9)), 2bv8)), (XOR_8((RSHIFT_8(t_9, 4bv8)), t_9)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_9, 4bv8)), t_9)), 2bv8)), (XOR_8((RSHIFT_8(t_9, 4bv8)), t_9)))))[1:0]));
SF := t_9[8:7];
ZF := bool2bv(0bv8 == t_9);

label_0x1f92:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1f99;
}

label_0x1f94:
t_13 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_13, 55bv8));
OF := AND_8((XOR_8(t_13, 55bv8)), (XOR_8(t_13, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_13)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x1f97:
goto label_0x1f9b;

label_0x1f99:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_2;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1f9b:
RAX := (0bv32 ++ PLUS_64(R8, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x1f9f:
t_17 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_17)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_17, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))))[1:0]));
SF := t_17[8:7];
ZF := bool2bv(0bv8 == t_17);

label_0x1fa1:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1fa9;
}

label_0x1fa3:
t_21 := R8[32:0][8:0];
R8 := (R8[64:8]) ++ (MINUS_8((R8[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_21, 48bv8));
OF := AND_8((XOR_8(t_21, 48bv8)), (XOR_8(t_21, (R8[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((R8[32:0][8:0]), t_21)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))))))[1:0]));
SF := R8[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (R8[32:0][8:0]));

label_0x1fa7:
goto label_0x1fba;

label_0x1fa9:
RAX := (0bv32 ++ PLUS_64(R8, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x1fad:
t_25 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_25)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_25, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)), 2bv8)), (XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)), 2bv8)), (XOR_8((RSHIFT_8(t_25, 4bv8)), t_25)))))[1:0]));
SF := t_25[8:7];
ZF := bool2bv(0bv8 == t_25);

label_0x1faf:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1fb7;
}

label_0x1fb1:
t_29 := R8[32:0][8:0];
R8 := (R8[64:8]) ++ (MINUS_8((R8[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_29, 55bv8));
OF := AND_8((XOR_8(t_29, 55bv8)), (XOR_8(t_29, (R8[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((R8[32:0][8:0]), t_29)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((R8[32:0][8:0]), 4bv8)), (R8[32:0][8:0]))))))[1:0]));
SF := R8[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (R8[32:0][8:0]));

label_0x1fb5:
goto label_0x1fba;

label_0x1fb7:
R8 := (R8[64:8]) ++ 0bv8;
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1fba:
origDEST_33 := RDX[32:0][8:0];
origCOUNT_34 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RDX := (RDX[64:8]) ++ (LSHIFT_8((RDX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), CF, RSHIFT_8(origDEST_33, (MINUS_8(8bv8, origCOUNT_34)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv8)), XOR_1((RDX[32:0][8:0][8:7]), CF), unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), SF, RDX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), ZF, bool2bv(0bv8 == (RDX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv8)), AF, unconstrained_5);

label_0x1fbd:
RDX := (RDX[64:8]) ++ (OR_8((RDX[32:0][8:0]), (R8[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x1fc0:
R8 := 17592186054145bv64;

label_0x1fca:
t_41 := MINUS_8((RDX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RDX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RDX[32:0][8:0]), 44bv8)), (XOR_8((RDX[32:0][8:0]), t_41)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_41, (RDX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)), 2bv8)), (XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)), 2bv8)), (XOR_8((RSHIFT_8(t_41, 4bv8)), t_41)))))[1:0]));
SF := t_41[8:7];
ZF := bool2bv(0bv8 == t_41);

label_0x1fcd:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1fda;
}

label_0x1fcf:
RAX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0x1fd2:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x1fd6:
if (bv2bool(NOT_1(CF))) {
  goto label_0x1fda;
}

label_0x1fd8:
RDX := (RDX[64:8]) ++ 88bv8;

label_0x1fda:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20568bv64, 8160bv64)), 0bv64), RDX[32:0][8:0]);

label_0x1fe0:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, 3bv64))));

label_0x1fe4:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, 2bv64))));

label_0x1fe8:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x1feb:
t_45 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_45)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_45, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)), 2bv8)), (XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)), 2bv8)), (XOR_8((RSHIFT_8(t_45, 4bv8)), t_45)))))[1:0]));
SF := t_45[8:7];
ZF := bool2bv(0bv8 == t_45);

label_0x1fed:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1ff4;
}

label_0x1fef:
t_49 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_49, 48bv8));
OF := AND_8((XOR_8(t_49, 48bv8)), (XOR_8(t_49, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_49)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x1ff2:
goto label_0x2002;

label_0x1ff4:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x1ff7:
t_53 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_53)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_53, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)), 2bv8)), (XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)), 2bv8)), (XOR_8((RSHIFT_8(t_53, 4bv8)), t_53)))))[1:0]));
SF := t_53[8:7];
ZF := bool2bv(0bv8 == t_53);

label_0x1ff9:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2000;
}

label_0x1ffb:
t_57 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_57, 55bv8));
OF := AND_8((XOR_8(t_57, 55bv8)), (XOR_8(t_57, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_57)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x1ffe:
goto label_0x2002;

label_0x2000:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2002:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2005:
t_61 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_61)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_61, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)), 2bv8)), (XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)), 2bv8)), (XOR_8((RSHIFT_8(t_61, 4bv8)), t_61)))))[1:0]));
SF := t_61[8:7];
ZF := bool2bv(0bv8 == t_61);

label_0x2007:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x200e;
}

label_0x2009:
t_65 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_65, 48bv8));
OF := AND_8((XOR_8(t_65, 48bv8)), (XOR_8(t_65, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_65)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x200c:
goto label_0x201c;

label_0x200e:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2011:
t_69 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_69)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_69, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)), 2bv8)), (XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)), 2bv8)), (XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)))))[1:0]));
SF := t_69[8:7];
ZF := bool2bv(0bv8 == t_69);

label_0x2013:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x201a;
}

label_0x2015:
t_73 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_73, 55bv8));
OF := AND_8((XOR_8(t_73, 55bv8)), (XOR_8(t_73, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_73)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2018:
goto label_0x201c;

label_0x201a:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_12;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x201c:
origDEST_77 := RCX[32:0][8:0];
origCOUNT_78 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), CF, RSHIFT_8(origDEST_77, (MINUS_8(8bv8, origCOUNT_78)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv8)), AF, unconstrained_14);

label_0x201f:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2021:
t_85 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_85)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_85, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)), 2bv8)), (XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)), 2bv8)), (XOR_8((RSHIFT_8(t_85, 4bv8)), t_85)))))[1:0]));
SF := t_85[8:7];
ZF := bool2bv(0bv8 == t_85);

label_0x2024:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2031;
}

label_0x2026:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2029:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_16;
SF := unconstrained_17;
AF := unconstrained_18;
PF := unconstrained_19;

label_0x202d:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2031;
}

label_0x202f:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x2031:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20482bv64, 8247bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2037:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 4bv64))));

label_0x203c:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 5bv64))));

label_0x2041:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2044:
t_89 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_89)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_89, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)), 2bv8)), (XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)), 2bv8)), (XOR_8((RSHIFT_8(t_89, 4bv8)), t_89)))))[1:0]));
SF := t_89[8:7];
ZF := bool2bv(0bv8 == t_89);

label_0x2046:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x204d;
}

label_0x2048:
t_93 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_93, 48bv8));
OF := AND_8((XOR_8(t_93, 48bv8)), (XOR_8(t_93, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_93)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x204b:
goto label_0x205b;

label_0x204d:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2050:
t_97 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_97)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_97, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)), 2bv8)), (XOR_8((RSHIFT_8(t_97, 4bv8)), t_97)))))[1:0]));
SF := t_97[8:7];
ZF := bool2bv(0bv8 == t_97);

label_0x2052:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2059;
}

label_0x2054:
t_101 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_101, 55bv8));
OF := AND_8((XOR_8(t_101, 55bv8)), (XOR_8(t_101, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_101)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2057:
goto label_0x205b;

label_0x2059:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_20;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x205b:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x205e:
t_105 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_105)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_105, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_105, 4bv8)), t_105)), 2bv8)), (XOR_8((RSHIFT_8(t_105, 4bv8)), t_105)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_105, 4bv8)), t_105)), 2bv8)), (XOR_8((RSHIFT_8(t_105, 4bv8)), t_105)))))[1:0]));
SF := t_105[8:7];
ZF := bool2bv(0bv8 == t_105);

label_0x2060:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2067;
}

label_0x2062:
t_109 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_109, 48bv8));
OF := AND_8((XOR_8(t_109, 48bv8)), (XOR_8(t_109, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_109)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2065:
goto label_0x2075;

label_0x2067:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x206a:
t_113 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_113)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_113, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_113, 4bv8)), t_113)), 2bv8)), (XOR_8((RSHIFT_8(t_113, 4bv8)), t_113)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_113, 4bv8)), t_113)), 2bv8)), (XOR_8((RSHIFT_8(t_113, 4bv8)), t_113)))))[1:0]));
SF := t_113[8:7];
ZF := bool2bv(0bv8 == t_113);

label_0x206c:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2073;
}

label_0x206e:
t_117 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_117, 55bv8));
OF := AND_8((XOR_8(t_117, 55bv8)), (XOR_8(t_117, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_117)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2071:
goto label_0x2075;

label_0x2073:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_21;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2075:
origDEST_121 := RCX[32:0][8:0];
origCOUNT_122 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), CF, RSHIFT_8(origDEST_121, (MINUS_8(8bv8, origCOUNT_122)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv8)), AF, unconstrained_23);

label_0x2078:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x207a:
t_129 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_129)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_129, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)), 2bv8)), (XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)), 2bv8)), (XOR_8((RSHIFT_8(t_129, 4bv8)), t_129)))))[1:0]));
SF := t_129[8:7];
ZF := bool2bv(0bv8 == t_129);

label_0x207d:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x208a;
}

label_0x207f:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2082:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x2086:
if (bv2bool(NOT_1(CF))) {
  goto label_0x208a;
}

label_0x2088:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x208a:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20394bv64, 8336bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2090:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 6bv64))));

label_0x2095:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 7bv64))));

label_0x209a:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x209d:
t_133 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_133)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_133, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_133, 4bv8)), t_133)), 2bv8)), (XOR_8((RSHIFT_8(t_133, 4bv8)), t_133)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_133, 4bv8)), t_133)), 2bv8)), (XOR_8((RSHIFT_8(t_133, 4bv8)), t_133)))))[1:0]));
SF := t_133[8:7];
ZF := bool2bv(0bv8 == t_133);

label_0x209f:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20a6;
}

label_0x20a1:
t_137 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_137, 48bv8));
OF := AND_8((XOR_8(t_137, 48bv8)), (XOR_8(t_137, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_137)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x20a4:
goto label_0x20b4;

label_0x20a6:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x20a9:
t_141 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_141)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_141, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_141, 4bv8)), t_141)), 2bv8)), (XOR_8((RSHIFT_8(t_141, 4bv8)), t_141)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_141, 4bv8)), t_141)), 2bv8)), (XOR_8((RSHIFT_8(t_141, 4bv8)), t_141)))))[1:0]));
SF := t_141[8:7];
ZF := bool2bv(0bv8 == t_141);

label_0x20ab:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20b2;
}

label_0x20ad:
t_145 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_145, 55bv8));
OF := AND_8((XOR_8(t_145, 55bv8)), (XOR_8(t_145, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_145)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x20b0:
goto label_0x20b4;

label_0x20b2:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_29;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x20b4:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x20b7:
t_149 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_149)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_149, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_149, 4bv8)), t_149)), 2bv8)), (XOR_8((RSHIFT_8(t_149, 4bv8)), t_149)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_149, 4bv8)), t_149)), 2bv8)), (XOR_8((RSHIFT_8(t_149, 4bv8)), t_149)))))[1:0]));
SF := t_149[8:7];
ZF := bool2bv(0bv8 == t_149);

label_0x20b9:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20c0;
}

label_0x20bb:
t_153 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_153, 48bv8));
OF := AND_8((XOR_8(t_153, 48bv8)), (XOR_8(t_153, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_153)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x20be:
goto label_0x20ce;

label_0x20c0:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x20c3:
t_157 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_157)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_157, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_157, 4bv8)), t_157)), 2bv8)), (XOR_8((RSHIFT_8(t_157, 4bv8)), t_157)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_157, 4bv8)), t_157)), 2bv8)), (XOR_8((RSHIFT_8(t_157, 4bv8)), t_157)))))[1:0]));
SF := t_157[8:7];
ZF := bool2bv(0bv8 == t_157);

label_0x20c5:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20cc;
}

label_0x20c7:
t_161 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_161, 55bv8));
OF := AND_8((XOR_8(t_161, 55bv8)), (XOR_8(t_161, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_161)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x20ca:
goto label_0x20ce;

label_0x20cc:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_30;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x20ce:
origDEST_165 := RCX[32:0][8:0];
origCOUNT_166 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), CF, RSHIFT_8(origDEST_165, (MINUS_8(8bv8, origCOUNT_166)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv8)), AF, unconstrained_32);

label_0x20d1:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x20d3:
t_173 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_173)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_173, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_173, 4bv8)), t_173)), 2bv8)), (XOR_8((RSHIFT_8(t_173, 4bv8)), t_173)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_173, 4bv8)), t_173)), 2bv8)), (XOR_8((RSHIFT_8(t_173, 4bv8)), t_173)))))[1:0]));
SF := t_173[8:7];
ZF := bool2bv(0bv8 == t_173);

label_0x20d6:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20e3;
}

label_0x20d8:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x20db:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_34;
SF := unconstrained_35;
AF := unconstrained_36;
PF := unconstrained_37;

label_0x20df:
if (bv2bool(NOT_1(CF))) {
  goto label_0x20e3;
}

label_0x20e1:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x20e3:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20306bv64, 8425bv64)), 0bv64), RCX[32:0][8:0]);

label_0x20e9:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 9bv64))));

label_0x20ee:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 10bv64))));

label_0x20f3:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x20f6:
t_177 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_177)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_177, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_177, 4bv8)), t_177)), 2bv8)), (XOR_8((RSHIFT_8(t_177, 4bv8)), t_177)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_177, 4bv8)), t_177)), 2bv8)), (XOR_8((RSHIFT_8(t_177, 4bv8)), t_177)))))[1:0]));
SF := t_177[8:7];
ZF := bool2bv(0bv8 == t_177);

label_0x20f8:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x20ff;
}

label_0x20fa:
t_181 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_181, 48bv8));
OF := AND_8((XOR_8(t_181, 48bv8)), (XOR_8(t_181, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_181)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x20fd:
goto label_0x210d;

label_0x20ff:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2102:
t_185 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_185)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_185, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_185, 4bv8)), t_185)), 2bv8)), (XOR_8((RSHIFT_8(t_185, 4bv8)), t_185)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_185, 4bv8)), t_185)), 2bv8)), (XOR_8((RSHIFT_8(t_185, 4bv8)), t_185)))))[1:0]));
SF := t_185[8:7];
ZF := bool2bv(0bv8 == t_185);

label_0x2104:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x210b;
}

label_0x2106:
t_189 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_189, 55bv8));
OF := AND_8((XOR_8(t_189, 55bv8)), (XOR_8(t_189, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_189)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2109:
goto label_0x210d;

label_0x210b:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_38;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x210d:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2110:
t_193 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_193)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_193, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)), 2bv8)), (XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)), 2bv8)), (XOR_8((RSHIFT_8(t_193, 4bv8)), t_193)))))[1:0]));
SF := t_193[8:7];
ZF := bool2bv(0bv8 == t_193);

label_0x2112:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2119;
}

label_0x2114:
t_197 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_197, 48bv8));
OF := AND_8((XOR_8(t_197, 48bv8)), (XOR_8(t_197, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_197)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2117:
goto label_0x2127;

label_0x2119:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x211c:
t_201 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_201)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_201, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_201, 4bv8)), t_201)), 2bv8)), (XOR_8((RSHIFT_8(t_201, 4bv8)), t_201)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_201, 4bv8)), t_201)), 2bv8)), (XOR_8((RSHIFT_8(t_201, 4bv8)), t_201)))))[1:0]));
SF := t_201[8:7];
ZF := bool2bv(0bv8 == t_201);

label_0x211e:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2125;
}

label_0x2120:
t_205 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_205, 55bv8));
OF := AND_8((XOR_8(t_205, 55bv8)), (XOR_8(t_205, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_205)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2123:
goto label_0x2127;

label_0x2125:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_39;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2127:
origDEST_209 := RCX[32:0][8:0];
origCOUNT_210 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), CF, RSHIFT_8(origDEST_209, (MINUS_8(8bv8, origCOUNT_210)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv8)), AF, unconstrained_41);

label_0x212a:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x212c:
t_217 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_217)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_217, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_217, 4bv8)), t_217)), 2bv8)), (XOR_8((RSHIFT_8(t_217, 4bv8)), t_217)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_217, 4bv8)), t_217)), 2bv8)), (XOR_8((RSHIFT_8(t_217, 4bv8)), t_217)))))[1:0]));
SF := t_217[8:7];
ZF := bool2bv(0bv8 == t_217);

label_0x212f:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x213c;
}

label_0x2131:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2134:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_43;
SF := unconstrained_44;
AF := unconstrained_45;
PF := unconstrained_46;

label_0x2138:
if (bv2bool(NOT_1(CF))) {
  goto label_0x213c;
}

label_0x213a:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x213c:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20218bv64, 8514bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2142:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 11bv64))));

label_0x2147:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 12bv64))));

label_0x214c:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x214f:
t_221 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_221)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_221, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_221, 4bv8)), t_221)), 2bv8)), (XOR_8((RSHIFT_8(t_221, 4bv8)), t_221)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_221, 4bv8)), t_221)), 2bv8)), (XOR_8((RSHIFT_8(t_221, 4bv8)), t_221)))))[1:0]));
SF := t_221[8:7];
ZF := bool2bv(0bv8 == t_221);

label_0x2151:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2158;
}

label_0x2153:
t_225 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_225, 48bv8));
OF := AND_8((XOR_8(t_225, 48bv8)), (XOR_8(t_225, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_225)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2156:
goto label_0x2166;

label_0x2158:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x215b:
t_229 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_229)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_229, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_229, 4bv8)), t_229)), 2bv8)), (XOR_8((RSHIFT_8(t_229, 4bv8)), t_229)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_229, 4bv8)), t_229)), 2bv8)), (XOR_8((RSHIFT_8(t_229, 4bv8)), t_229)))))[1:0]));
SF := t_229[8:7];
ZF := bool2bv(0bv8 == t_229);

label_0x215d:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2164;
}

label_0x215f:
t_233 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_233, 55bv8));
OF := AND_8((XOR_8(t_233, 55bv8)), (XOR_8(t_233, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_233)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2162:
goto label_0x2166;

label_0x2164:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_47;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2166:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2169:
t_237 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_237)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_237, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_237, 4bv8)), t_237)), 2bv8)), (XOR_8((RSHIFT_8(t_237, 4bv8)), t_237)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_237, 4bv8)), t_237)), 2bv8)), (XOR_8((RSHIFT_8(t_237, 4bv8)), t_237)))))[1:0]));
SF := t_237[8:7];
ZF := bool2bv(0bv8 == t_237);

label_0x216b:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2172;
}

label_0x216d:
t_241 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_241, 48bv8));
OF := AND_8((XOR_8(t_241, 48bv8)), (XOR_8(t_241, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_241)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2170:
goto label_0x2180;

label_0x2172:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2175:
t_245 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_245)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_245, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_245, 4bv8)), t_245)), 2bv8)), (XOR_8((RSHIFT_8(t_245, 4bv8)), t_245)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_245, 4bv8)), t_245)), 2bv8)), (XOR_8((RSHIFT_8(t_245, 4bv8)), t_245)))))[1:0]));
SF := t_245[8:7];
ZF := bool2bv(0bv8 == t_245);

label_0x2177:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x217e;
}

label_0x2179:
t_249 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_249, 55bv8));
OF := AND_8((XOR_8(t_249, 55bv8)), (XOR_8(t_249, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_249)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x217c:
goto label_0x2180;

label_0x217e:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_48;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2180:
origDEST_253 := RCX[32:0][8:0];
origCOUNT_254 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), CF, RSHIFT_8(origDEST_253, (MINUS_8(8bv8, origCOUNT_254)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_254 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv8)), AF, unconstrained_50);

label_0x2183:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2185:
t_261 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_261)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_261, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_261, 4bv8)), t_261)), 2bv8)), (XOR_8((RSHIFT_8(t_261, 4bv8)), t_261)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_261, 4bv8)), t_261)), 2bv8)), (XOR_8((RSHIFT_8(t_261, 4bv8)), t_261)))))[1:0]));
SF := t_261[8:7];
ZF := bool2bv(0bv8 == t_261);

label_0x2188:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2195;
}

label_0x218a:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x218d:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_52;
SF := unconstrained_53;
AF := unconstrained_54;
PF := unconstrained_55;

label_0x2191:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2195;
}

label_0x2193:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x2195:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20130bv64, 8603bv64)), 0bv64), RCX[32:0][8:0]);

label_0x219b:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 14bv64))));

label_0x21a0:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 15bv64))));

label_0x21a5:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x21a8:
t_265 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_265)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_265, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_265, 4bv8)), t_265)), 2bv8)), (XOR_8((RSHIFT_8(t_265, 4bv8)), t_265)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_265, 4bv8)), t_265)), 2bv8)), (XOR_8((RSHIFT_8(t_265, 4bv8)), t_265)))))[1:0]));
SF := t_265[8:7];
ZF := bool2bv(0bv8 == t_265);

label_0x21aa:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x21b1;
}

label_0x21ac:
t_269 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_269, 48bv8));
OF := AND_8((XOR_8(t_269, 48bv8)), (XOR_8(t_269, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_269)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x21af:
goto label_0x21bf;

label_0x21b1:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x21b4:
t_273 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_273)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_273, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_273, 4bv8)), t_273)), 2bv8)), (XOR_8((RSHIFT_8(t_273, 4bv8)), t_273)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_273, 4bv8)), t_273)), 2bv8)), (XOR_8((RSHIFT_8(t_273, 4bv8)), t_273)))))[1:0]));
SF := t_273[8:7];
ZF := bool2bv(0bv8 == t_273);

label_0x21b6:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x21bd;
}

label_0x21b8:
t_277 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_277, 55bv8));
OF := AND_8((XOR_8(t_277, 55bv8)), (XOR_8(t_277, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_277)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x21bb:
goto label_0x21bf;

label_0x21bd:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_56;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x21bf:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x21c2:
t_281 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_281)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_281, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_281, 4bv8)), t_281)), 2bv8)), (XOR_8((RSHIFT_8(t_281, 4bv8)), t_281)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_281, 4bv8)), t_281)), 2bv8)), (XOR_8((RSHIFT_8(t_281, 4bv8)), t_281)))))[1:0]));
SF := t_281[8:7];
ZF := bool2bv(0bv8 == t_281);

label_0x21c4:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x21cb;
}

label_0x21c6:
t_285 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_285, 48bv8));
OF := AND_8((XOR_8(t_285, 48bv8)), (XOR_8(t_285, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_285)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x21c9:
goto label_0x21d9;

label_0x21cb:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x21ce:
t_289 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_289)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_289, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_289, 4bv8)), t_289)), 2bv8)), (XOR_8((RSHIFT_8(t_289, 4bv8)), t_289)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_289, 4bv8)), t_289)), 2bv8)), (XOR_8((RSHIFT_8(t_289, 4bv8)), t_289)))))[1:0]));
SF := t_289[8:7];
ZF := bool2bv(0bv8 == t_289);

label_0x21d0:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x21d7;
}

label_0x21d2:
t_293 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_293, 55bv8));
OF := AND_8((XOR_8(t_293, 55bv8)), (XOR_8(t_293, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_293)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x21d5:
goto label_0x21d9;

label_0x21d7:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_57;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x21d9:
origDEST_297 := RCX[32:0][8:0];
origCOUNT_298 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), CF, RSHIFT_8(origDEST_297, (MINUS_8(8bv8, origCOUNT_298)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv8)), AF, unconstrained_59);

label_0x21dc:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x21de:
t_305 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_305)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_305, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_305, 4bv8)), t_305)), 2bv8)), (XOR_8((RSHIFT_8(t_305, 4bv8)), t_305)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_305, 4bv8)), t_305)), 2bv8)), (XOR_8((RSHIFT_8(t_305, 4bv8)), t_305)))))[1:0]));
SF := t_305[8:7];
ZF := bool2bv(0bv8 == t_305);

label_0x21e1:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x21ee;
}

label_0x21e3:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x21e6:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_61;
SF := unconstrained_62;
AF := unconstrained_63;
PF := unconstrained_64;

label_0x21ea:
if (bv2bool(NOT_1(CF))) {
  goto label_0x21ee;
}

label_0x21ec:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x21ee:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(20042bv64, 8692bv64)), 0bv64), RCX[32:0][8:0]);

label_0x21f4:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 16bv64))));

label_0x21f9:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 17bv64))));

label_0x21fe:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2201:
t_309 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_309)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_309, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_309, 4bv8)), t_309)), 2bv8)), (XOR_8((RSHIFT_8(t_309, 4bv8)), t_309)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_309, 4bv8)), t_309)), 2bv8)), (XOR_8((RSHIFT_8(t_309, 4bv8)), t_309)))))[1:0]));
SF := t_309[8:7];
ZF := bool2bv(0bv8 == t_309);

label_0x2203:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x220a;
}

label_0x2205:
t_313 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_313, 48bv8));
OF := AND_8((XOR_8(t_313, 48bv8)), (XOR_8(t_313, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_313)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2208:
goto label_0x2218;

label_0x220a:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x220d:
t_317 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_317)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_317, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_317, 4bv8)), t_317)), 2bv8)), (XOR_8((RSHIFT_8(t_317, 4bv8)), t_317)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_317, 4bv8)), t_317)), 2bv8)), (XOR_8((RSHIFT_8(t_317, 4bv8)), t_317)))))[1:0]));
SF := t_317[8:7];
ZF := bool2bv(0bv8 == t_317);

label_0x220f:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2216;
}

label_0x2211:
t_321 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_321, 55bv8));
OF := AND_8((XOR_8(t_321, 55bv8)), (XOR_8(t_321, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_321)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2214:
goto label_0x2218;

label_0x2216:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_65;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2218:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x221b:
t_325 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_325)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_325, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_325, 4bv8)), t_325)), 2bv8)), (XOR_8((RSHIFT_8(t_325, 4bv8)), t_325)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_325, 4bv8)), t_325)), 2bv8)), (XOR_8((RSHIFT_8(t_325, 4bv8)), t_325)))))[1:0]));
SF := t_325[8:7];
ZF := bool2bv(0bv8 == t_325);

label_0x221d:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2224;
}

label_0x221f:
t_329 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_329, 48bv8));
OF := AND_8((XOR_8(t_329, 48bv8)), (XOR_8(t_329, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_329)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2222:
goto label_0x2232;

label_0x2224:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2227:
t_333 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_333)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_333, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_333, 4bv8)), t_333)), 2bv8)), (XOR_8((RSHIFT_8(t_333, 4bv8)), t_333)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_333, 4bv8)), t_333)), 2bv8)), (XOR_8((RSHIFT_8(t_333, 4bv8)), t_333)))))[1:0]));
SF := t_333[8:7];
ZF := bool2bv(0bv8 == t_333);

label_0x2229:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2230;
}

label_0x222b:
t_337 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_337, 55bv8));
OF := AND_8((XOR_8(t_337, 55bv8)), (XOR_8(t_337, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_337)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x222e:
goto label_0x2232;

label_0x2230:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_66;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2232:
origDEST_341 := RCX[32:0][8:0];
origCOUNT_342 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), CF, RSHIFT_8(origDEST_341, (MINUS_8(8bv8, origCOUNT_342)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_342 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv8)), AF, unconstrained_68);

label_0x2235:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2237:
t_349 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_349)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_349, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_349, 4bv8)), t_349)), 2bv8)), (XOR_8((RSHIFT_8(t_349, 4bv8)), t_349)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_349, 4bv8)), t_349)), 2bv8)), (XOR_8((RSHIFT_8(t_349, 4bv8)), t_349)))))[1:0]));
SF := t_349[8:7];
ZF := bool2bv(0bv8 == t_349);

label_0x223a:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2247;
}

label_0x223c:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x223f:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_70;
SF := unconstrained_71;
AF := unconstrained_72;
PF := unconstrained_73;

label_0x2243:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2247;
}

label_0x2245:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x2247:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19954bv64, 8781bv64)), 0bv64), RCX[32:0][8:0]);

label_0x224d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 19bv64))));

label_0x2252:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 20bv64))));

label_0x2257:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x225a:
t_353 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_353)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_353, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_353, 4bv8)), t_353)), 2bv8)), (XOR_8((RSHIFT_8(t_353, 4bv8)), t_353)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_353, 4bv8)), t_353)), 2bv8)), (XOR_8((RSHIFT_8(t_353, 4bv8)), t_353)))))[1:0]));
SF := t_353[8:7];
ZF := bool2bv(0bv8 == t_353);

label_0x225c:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2263;
}

label_0x225e:
t_357 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_357, 48bv8));
OF := AND_8((XOR_8(t_357, 48bv8)), (XOR_8(t_357, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_357)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2261:
goto label_0x2271;

label_0x2263:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2266:
t_361 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_361)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_361, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_361, 4bv8)), t_361)), 2bv8)), (XOR_8((RSHIFT_8(t_361, 4bv8)), t_361)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_361, 4bv8)), t_361)), 2bv8)), (XOR_8((RSHIFT_8(t_361, 4bv8)), t_361)))))[1:0]));
SF := t_361[8:7];
ZF := bool2bv(0bv8 == t_361);

label_0x2268:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x226f;
}

label_0x226a:
t_365 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_365, 55bv8));
OF := AND_8((XOR_8(t_365, 55bv8)), (XOR_8(t_365, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_365)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x226d:
goto label_0x2271;

label_0x226f:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_74;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2271:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2274:
t_369 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_369)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_369, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_369, 4bv8)), t_369)), 2bv8)), (XOR_8((RSHIFT_8(t_369, 4bv8)), t_369)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_369, 4bv8)), t_369)), 2bv8)), (XOR_8((RSHIFT_8(t_369, 4bv8)), t_369)))))[1:0]));
SF := t_369[8:7];
ZF := bool2bv(0bv8 == t_369);

label_0x2276:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x227d;
}

label_0x2278:
t_373 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_373, 48bv8));
OF := AND_8((XOR_8(t_373, 48bv8)), (XOR_8(t_373, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_373)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x227b:
goto label_0x228b;

label_0x227d:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2280:
t_377 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_377)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_377, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_377, 4bv8)), t_377)), 2bv8)), (XOR_8((RSHIFT_8(t_377, 4bv8)), t_377)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_377, 4bv8)), t_377)), 2bv8)), (XOR_8((RSHIFT_8(t_377, 4bv8)), t_377)))))[1:0]));
SF := t_377[8:7];
ZF := bool2bv(0bv8 == t_377);

label_0x2282:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2289;
}

label_0x2284:
t_381 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_381, 55bv8));
OF := AND_8((XOR_8(t_381, 55bv8)), (XOR_8(t_381, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_381)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2287:
goto label_0x228b;

label_0x2289:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_75;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x228b:
origDEST_385 := RCX[32:0][8:0];
origCOUNT_386 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), CF, RSHIFT_8(origDEST_385, (MINUS_8(8bv8, origCOUNT_386)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_386 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_386 == 0bv8)), AF, unconstrained_77);

label_0x228e:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2290:
t_393 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_393)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_393, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_393, 4bv8)), t_393)), 2bv8)), (XOR_8((RSHIFT_8(t_393, 4bv8)), t_393)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_393, 4bv8)), t_393)), 2bv8)), (XOR_8((RSHIFT_8(t_393, 4bv8)), t_393)))))[1:0]));
SF := t_393[8:7];
ZF := bool2bv(0bv8 == t_393);

label_0x2293:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22a0;
}

label_0x2295:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2298:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_79;
SF := unconstrained_80;
AF := unconstrained_81;
PF := unconstrained_82;

label_0x229c:
if (bv2bool(NOT_1(CF))) {
  goto label_0x22a0;
}

label_0x229e:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x22a0:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19866bv64, 8870bv64)), 0bv64), RCX[32:0][8:0]);

label_0x22a6:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 21bv64))));

label_0x22ab:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 22bv64))));

label_0x22b0:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x22b3:
t_397 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_397)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_397, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_397, 4bv8)), t_397)), 2bv8)), (XOR_8((RSHIFT_8(t_397, 4bv8)), t_397)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_397, 4bv8)), t_397)), 2bv8)), (XOR_8((RSHIFT_8(t_397, 4bv8)), t_397)))))[1:0]));
SF := t_397[8:7];
ZF := bool2bv(0bv8 == t_397);

label_0x22b5:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22bc;
}

label_0x22b7:
t_401 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_401, 48bv8));
OF := AND_8((XOR_8(t_401, 48bv8)), (XOR_8(t_401, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_401)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x22ba:
goto label_0x22ca;

label_0x22bc:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x22bf:
t_405 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_405)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_405, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_405, 4bv8)), t_405)), 2bv8)), (XOR_8((RSHIFT_8(t_405, 4bv8)), t_405)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_405, 4bv8)), t_405)), 2bv8)), (XOR_8((RSHIFT_8(t_405, 4bv8)), t_405)))))[1:0]));
SF := t_405[8:7];
ZF := bool2bv(0bv8 == t_405);

label_0x22c1:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22c8;
}

label_0x22c3:
t_409 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_409, 55bv8));
OF := AND_8((XOR_8(t_409, 55bv8)), (XOR_8(t_409, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_409)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x22c6:
goto label_0x22ca;

label_0x22c8:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_83;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x22ca:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x22cd:
t_413 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_413)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_413, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_413, 4bv8)), t_413)), 2bv8)), (XOR_8((RSHIFT_8(t_413, 4bv8)), t_413)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_413, 4bv8)), t_413)), 2bv8)), (XOR_8((RSHIFT_8(t_413, 4bv8)), t_413)))))[1:0]));
SF := t_413[8:7];
ZF := bool2bv(0bv8 == t_413);

label_0x22cf:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22d6;
}

label_0x22d1:
t_417 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_417, 48bv8));
OF := AND_8((XOR_8(t_417, 48bv8)), (XOR_8(t_417, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_417)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x22d4:
goto label_0x22e4;

label_0x22d6:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x22d9:
t_421 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_421)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_421, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_421, 4bv8)), t_421)), 2bv8)), (XOR_8((RSHIFT_8(t_421, 4bv8)), t_421)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_421, 4bv8)), t_421)), 2bv8)), (XOR_8((RSHIFT_8(t_421, 4bv8)), t_421)))))[1:0]));
SF := t_421[8:7];
ZF := bool2bv(0bv8 == t_421);

label_0x22db:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22e2;
}

label_0x22dd:
t_425 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_425, 55bv8));
OF := AND_8((XOR_8(t_425, 55bv8)), (XOR_8(t_425, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_425)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x22e0:
goto label_0x22e4;

label_0x22e2:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_84;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x22e4:
origDEST_429 := RCX[32:0][8:0];
origCOUNT_430 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), CF, RSHIFT_8(origDEST_429, (MINUS_8(8bv8, origCOUNT_430)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_430 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv8)), AF, unconstrained_86);

label_0x22e7:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x22e9:
t_437 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_437)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_437, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_437, 4bv8)), t_437)), 2bv8)), (XOR_8((RSHIFT_8(t_437, 4bv8)), t_437)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_437, 4bv8)), t_437)), 2bv8)), (XOR_8((RSHIFT_8(t_437, 4bv8)), t_437)))))[1:0]));
SF := t_437[8:7];
ZF := bool2bv(0bv8 == t_437);

label_0x22ec:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x22f9;
}

label_0x22ee:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x22f1:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_88;
SF := unconstrained_89;
AF := unconstrained_90;
PF := unconstrained_91;

label_0x22f5:
if (bv2bool(NOT_1(CF))) {
  goto label_0x22f9;
}

label_0x22f7:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x22f9:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19778bv64, 8959bv64)), 0bv64), RCX[32:0][8:0]);

label_0x22ff:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 24bv64))));

label_0x2304:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 25bv64))));

label_0x2309:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x230c:
t_441 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_441)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_441, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_441, 4bv8)), t_441)), 2bv8)), (XOR_8((RSHIFT_8(t_441, 4bv8)), t_441)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_441, 4bv8)), t_441)), 2bv8)), (XOR_8((RSHIFT_8(t_441, 4bv8)), t_441)))))[1:0]));
SF := t_441[8:7];
ZF := bool2bv(0bv8 == t_441);

label_0x230e:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2315;
}

label_0x2310:
t_445 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_445, 48bv8));
OF := AND_8((XOR_8(t_445, 48bv8)), (XOR_8(t_445, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_445)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2313:
goto label_0x2323;

label_0x2315:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2318:
t_449 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_449)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_449, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_449, 4bv8)), t_449)), 2bv8)), (XOR_8((RSHIFT_8(t_449, 4bv8)), t_449)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_449, 4bv8)), t_449)), 2bv8)), (XOR_8((RSHIFT_8(t_449, 4bv8)), t_449)))))[1:0]));
SF := t_449[8:7];
ZF := bool2bv(0bv8 == t_449);

label_0x231a:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2321;
}

label_0x231c:
t_453 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_453, 55bv8));
OF := AND_8((XOR_8(t_453, 55bv8)), (XOR_8(t_453, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_453)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x231f:
goto label_0x2323;

label_0x2321:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_92;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2323:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2326:
t_457 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_457)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_457, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_457, 4bv8)), t_457)), 2bv8)), (XOR_8((RSHIFT_8(t_457, 4bv8)), t_457)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_457, 4bv8)), t_457)), 2bv8)), (XOR_8((RSHIFT_8(t_457, 4bv8)), t_457)))))[1:0]));
SF := t_457[8:7];
ZF := bool2bv(0bv8 == t_457);

label_0x2328:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x232f;
}

label_0x232a:
t_461 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_461, 48bv8));
OF := AND_8((XOR_8(t_461, 48bv8)), (XOR_8(t_461, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_461)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x232d:
goto label_0x233d;

label_0x232f:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2332:
t_465 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_465)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_465, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_465, 4bv8)), t_465)), 2bv8)), (XOR_8((RSHIFT_8(t_465, 4bv8)), t_465)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_465, 4bv8)), t_465)), 2bv8)), (XOR_8((RSHIFT_8(t_465, 4bv8)), t_465)))))[1:0]));
SF := t_465[8:7];
ZF := bool2bv(0bv8 == t_465);

label_0x2334:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x233b;
}

label_0x2336:
t_469 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_469, 55bv8));
OF := AND_8((XOR_8(t_469, 55bv8)), (XOR_8(t_469, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_469)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2339:
goto label_0x233d;

label_0x233b:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_93;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x233d:
origDEST_473 := RCX[32:0][8:0];
origCOUNT_474 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), CF, RSHIFT_8(origDEST_473, (MINUS_8(8bv8, origCOUNT_474)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_474 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_474 == 0bv8)), AF, unconstrained_95);

label_0x2340:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2342:
t_481 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_481)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_481, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_481, 4bv8)), t_481)), 2bv8)), (XOR_8((RSHIFT_8(t_481, 4bv8)), t_481)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_481, 4bv8)), t_481)), 2bv8)), (XOR_8((RSHIFT_8(t_481, 4bv8)), t_481)))))[1:0]));
SF := t_481[8:7];
ZF := bool2bv(0bv8 == t_481);

label_0x2345:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2352;
}

label_0x2347:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x234a:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x234e:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2352;
}

label_0x2350:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x2352:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19690bv64, 9048bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2358:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 26bv64))));

label_0x235d:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 27bv64))));

label_0x2362:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2365:
t_485 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_485)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_485, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_485, 4bv8)), t_485)), 2bv8)), (XOR_8((RSHIFT_8(t_485, 4bv8)), t_485)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_485, 4bv8)), t_485)), 2bv8)), (XOR_8((RSHIFT_8(t_485, 4bv8)), t_485)))))[1:0]));
SF := t_485[8:7];
ZF := bool2bv(0bv8 == t_485);

label_0x2367:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x236e;
}

label_0x2369:
t_489 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_489, 48bv8));
OF := AND_8((XOR_8(t_489, 48bv8)), (XOR_8(t_489, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_489)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x236c:
goto label_0x237c;

label_0x236e:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2371:
t_493 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_493)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_493, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_493, 4bv8)), t_493)), 2bv8)), (XOR_8((RSHIFT_8(t_493, 4bv8)), t_493)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_493, 4bv8)), t_493)), 2bv8)), (XOR_8((RSHIFT_8(t_493, 4bv8)), t_493)))))[1:0]));
SF := t_493[8:7];
ZF := bool2bv(0bv8 == t_493);

label_0x2373:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x237a;
}

label_0x2375:
t_497 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_497, 55bv8));
OF := AND_8((XOR_8(t_497, 55bv8)), (XOR_8(t_497, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_497)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2378:
goto label_0x237c;

label_0x237a:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_101;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x237c:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x237f:
t_501 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_501)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_501, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_501, 4bv8)), t_501)), 2bv8)), (XOR_8((RSHIFT_8(t_501, 4bv8)), t_501)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_501, 4bv8)), t_501)), 2bv8)), (XOR_8((RSHIFT_8(t_501, 4bv8)), t_501)))))[1:0]));
SF := t_501[8:7];
ZF := bool2bv(0bv8 == t_501);

label_0x2381:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2388;
}

label_0x2383:
t_505 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_505, 48bv8));
OF := AND_8((XOR_8(t_505, 48bv8)), (XOR_8(t_505, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_505)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2386:
goto label_0x2396;

label_0x2388:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x238b:
t_509 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_509)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_509, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_509, 4bv8)), t_509)), 2bv8)), (XOR_8((RSHIFT_8(t_509, 4bv8)), t_509)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_509, 4bv8)), t_509)), 2bv8)), (XOR_8((RSHIFT_8(t_509, 4bv8)), t_509)))))[1:0]));
SF := t_509[8:7];
ZF := bool2bv(0bv8 == t_509);

label_0x238d:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2394;
}

label_0x238f:
t_513 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_513, 55bv8));
OF := AND_8((XOR_8(t_513, 55bv8)), (XOR_8(t_513, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_513)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2392:
goto label_0x2396;

label_0x2394:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_102;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2396:
origDEST_517 := RCX[32:0][8:0];
origCOUNT_518 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), CF, RSHIFT_8(origDEST_517, (MINUS_8(8bv8, origCOUNT_518)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_518 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv8)), AF, unconstrained_104);

label_0x2399:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x239b:
t_525 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_525)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_525, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_525, 4bv8)), t_525)), 2bv8)), (XOR_8((RSHIFT_8(t_525, 4bv8)), t_525)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_525, 4bv8)), t_525)), 2bv8)), (XOR_8((RSHIFT_8(t_525, 4bv8)), t_525)))))[1:0]));
SF := t_525[8:7];
ZF := bool2bv(0bv8 == t_525);

label_0x239e:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x23ab;
}

label_0x23a0:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x23a3:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_106;
SF := unconstrained_107;
AF := unconstrained_108;
PF := unconstrained_109;

label_0x23a7:
if (bv2bool(NOT_1(CF))) {
  goto label_0x23ab;
}

label_0x23a9:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x23ab:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19602bv64, 9137bv64)), 0bv64), RCX[32:0][8:0]);

label_0x23b1:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 28bv64))));

label_0x23b6:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 29bv64))));

label_0x23bb:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x23be:
t_529 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_529)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_529, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_529, 4bv8)), t_529)), 2bv8)), (XOR_8((RSHIFT_8(t_529, 4bv8)), t_529)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_529, 4bv8)), t_529)), 2bv8)), (XOR_8((RSHIFT_8(t_529, 4bv8)), t_529)))))[1:0]));
SF := t_529[8:7];
ZF := bool2bv(0bv8 == t_529);

label_0x23c0:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x23c7;
}

label_0x23c2:
t_533 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_533, 48bv8));
OF := AND_8((XOR_8(t_533, 48bv8)), (XOR_8(t_533, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_533)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x23c5:
goto label_0x23d5;

label_0x23c7:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x23ca:
t_537 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_537)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_537, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_537, 4bv8)), t_537)), 2bv8)), (XOR_8((RSHIFT_8(t_537, 4bv8)), t_537)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_537, 4bv8)), t_537)), 2bv8)), (XOR_8((RSHIFT_8(t_537, 4bv8)), t_537)))))[1:0]));
SF := t_537[8:7];
ZF := bool2bv(0bv8 == t_537);

label_0x23cc:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x23d3;
}

label_0x23ce:
t_541 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_541, 55bv8));
OF := AND_8((XOR_8(t_541, 55bv8)), (XOR_8(t_541, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_541)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x23d1:
goto label_0x23d5;

label_0x23d3:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_110;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x23d5:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x23d8:
t_545 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_545)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_545, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_545, 4bv8)), t_545)), 2bv8)), (XOR_8((RSHIFT_8(t_545, 4bv8)), t_545)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_545, 4bv8)), t_545)), 2bv8)), (XOR_8((RSHIFT_8(t_545, 4bv8)), t_545)))))[1:0]));
SF := t_545[8:7];
ZF := bool2bv(0bv8 == t_545);

label_0x23da:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x23e1;
}

label_0x23dc:
t_549 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_549, 48bv8));
OF := AND_8((XOR_8(t_549, 48bv8)), (XOR_8(t_549, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_549)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x23df:
goto label_0x23ef;

label_0x23e1:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x23e4:
t_553 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_553)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_553, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_553, 4bv8)), t_553)), 2bv8)), (XOR_8((RSHIFT_8(t_553, 4bv8)), t_553)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_553, 4bv8)), t_553)), 2bv8)), (XOR_8((RSHIFT_8(t_553, 4bv8)), t_553)))))[1:0]));
SF := t_553[8:7];
ZF := bool2bv(0bv8 == t_553);

label_0x23e6:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x23ed;
}

label_0x23e8:
t_557 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_557, 55bv8));
OF := AND_8((XOR_8(t_557, 55bv8)), (XOR_8(t_557, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_557)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x23eb:
goto label_0x23ef;

label_0x23ed:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_111;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x23ef:
origDEST_561 := RCX[32:0][8:0];
origCOUNT_562 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), CF, RSHIFT_8(origDEST_561, (MINUS_8(8bv8, origCOUNT_562)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_562 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv8)), AF, unconstrained_113);

label_0x23f2:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_114;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x23f4:
t_569 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_569)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_569, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_569, 4bv8)), t_569)), 2bv8)), (XOR_8((RSHIFT_8(t_569, 4bv8)), t_569)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_569, 4bv8)), t_569)), 2bv8)), (XOR_8((RSHIFT_8(t_569, 4bv8)), t_569)))))[1:0]));
SF := t_569[8:7];
ZF := bool2bv(0bv8 == t_569);

label_0x23f7:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2404;
}

label_0x23f9:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x23fc:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_115;
SF := unconstrained_116;
AF := unconstrained_117;
PF := unconstrained_118;

label_0x2400:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2404;
}

label_0x2402:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x2404:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19514bv64, 9226bv64)), 0bv64), RCX[32:0][8:0]);

label_0x240a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 30bv64))));

label_0x240f:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 31bv64))));

label_0x2414:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2417:
t_573 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_573)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_573, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_573, 4bv8)), t_573)), 2bv8)), (XOR_8((RSHIFT_8(t_573, 4bv8)), t_573)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_573, 4bv8)), t_573)), 2bv8)), (XOR_8((RSHIFT_8(t_573, 4bv8)), t_573)))))[1:0]));
SF := t_573[8:7];
ZF := bool2bv(0bv8 == t_573);

label_0x2419:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2420;
}

label_0x241b:
t_577 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_577, 48bv8));
OF := AND_8((XOR_8(t_577, 48bv8)), (XOR_8(t_577, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_577)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x241e:
goto label_0x242e;

label_0x2420:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2423:
t_581 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_581)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_581, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_581, 4bv8)), t_581)), 2bv8)), (XOR_8((RSHIFT_8(t_581, 4bv8)), t_581)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_581, 4bv8)), t_581)), 2bv8)), (XOR_8((RSHIFT_8(t_581, 4bv8)), t_581)))))[1:0]));
SF := t_581[8:7];
ZF := bool2bv(0bv8 == t_581);

label_0x2425:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x242c;
}

label_0x2427:
t_585 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_585, 55bv8));
OF := AND_8((XOR_8(t_585, 55bv8)), (XOR_8(t_585, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_585)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x242a:
goto label_0x242e;

label_0x242c:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_119;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x242e:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2431:
t_589 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_589)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_589, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_589, 4bv8)), t_589)), 2bv8)), (XOR_8((RSHIFT_8(t_589, 4bv8)), t_589)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_589, 4bv8)), t_589)), 2bv8)), (XOR_8((RSHIFT_8(t_589, 4bv8)), t_589)))))[1:0]));
SF := t_589[8:7];
ZF := bool2bv(0bv8 == t_589);

label_0x2433:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x243a;
}

label_0x2435:
t_593 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_593, 48bv8));
OF := AND_8((XOR_8(t_593, 48bv8)), (XOR_8(t_593, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_593)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2438:
goto label_0x2448;

label_0x243a:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x243d:
t_597 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_597)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_597, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_597, 4bv8)), t_597)), 2bv8)), (XOR_8((RSHIFT_8(t_597, 4bv8)), t_597)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_597, 4bv8)), t_597)), 2bv8)), (XOR_8((RSHIFT_8(t_597, 4bv8)), t_597)))))[1:0]));
SF := t_597[8:7];
ZF := bool2bv(0bv8 == t_597);

label_0x243f:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2446;
}

label_0x2441:
t_601 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_601, 55bv8));
OF := AND_8((XOR_8(t_601, 55bv8)), (XOR_8(t_601, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_601)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2444:
goto label_0x2448;

label_0x2446:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_120;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2448:
origDEST_605 := RCX[32:0][8:0];
origCOUNT_606 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), CF, RSHIFT_8(origDEST_605, (MINUS_8(8bv8, origCOUNT_606)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_606 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_606 == 0bv8)), AF, unconstrained_122);

label_0x244b:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_123;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x244d:
t_613 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_613)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_613, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_613, 4bv8)), t_613)), 2bv8)), (XOR_8((RSHIFT_8(t_613, 4bv8)), t_613)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_613, 4bv8)), t_613)), 2bv8)), (XOR_8((RSHIFT_8(t_613, 4bv8)), t_613)))))[1:0]));
SF := t_613[8:7];
ZF := bool2bv(0bv8 == t_613);

label_0x2450:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x245d;
}

label_0x2452:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2455:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_124;
SF := unconstrained_125;
AF := unconstrained_126;
PF := unconstrained_127;

label_0x2459:
if (bv2bool(NOT_1(CF))) {
  goto label_0x245d;
}

label_0x245b:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x245d:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19426bv64, 9315bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2463:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 32bv64))));

label_0x2468:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 33bv64))));

label_0x246d:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x2470:
t_617 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_617)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_617, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_617, 4bv8)), t_617)), 2bv8)), (XOR_8((RSHIFT_8(t_617, 4bv8)), t_617)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_617, 4bv8)), t_617)), 2bv8)), (XOR_8((RSHIFT_8(t_617, 4bv8)), t_617)))))[1:0]));
SF := t_617[8:7];
ZF := bool2bv(0bv8 == t_617);

label_0x2472:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2479;
}

label_0x2474:
t_621 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_621, 48bv8));
OF := AND_8((XOR_8(t_621, 48bv8)), (XOR_8(t_621, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_621)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2477:
goto label_0x2487;

label_0x2479:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x247c:
t_625 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_625)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_625, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_625, 4bv8)), t_625)), 2bv8)), (XOR_8((RSHIFT_8(t_625, 4bv8)), t_625)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_625, 4bv8)), t_625)), 2bv8)), (XOR_8((RSHIFT_8(t_625, 4bv8)), t_625)))))[1:0]));
SF := t_625[8:7];
ZF := bool2bv(0bv8 == t_625);

label_0x247e:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2485;
}

label_0x2480:
t_629 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_629, 55bv8));
OF := AND_8((XOR_8(t_629, 55bv8)), (XOR_8(t_629, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_629)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x2483:
goto label_0x2487;

label_0x2485:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_128;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2487:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x248a:
t_633 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_633)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_633, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_633, 4bv8)), t_633)), 2bv8)), (XOR_8((RSHIFT_8(t_633, 4bv8)), t_633)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_633, 4bv8)), t_633)), 2bv8)), (XOR_8((RSHIFT_8(t_633, 4bv8)), t_633)))))[1:0]));
SF := t_633[8:7];
ZF := bool2bv(0bv8 == t_633);

label_0x248c:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x2493;
}

label_0x248e:
t_637 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_637, 48bv8));
OF := AND_8((XOR_8(t_637, 48bv8)), (XOR_8(t_637, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_637)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x2491:
goto label_0x24a1;

label_0x2493:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x2496:
t_641 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_641)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_641, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_641, 4bv8)), t_641)), 2bv8)), (XOR_8((RSHIFT_8(t_641, 4bv8)), t_641)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_641, 4bv8)), t_641)), 2bv8)), (XOR_8((RSHIFT_8(t_641, 4bv8)), t_641)))))[1:0]));
SF := t_641[8:7];
ZF := bool2bv(0bv8 == t_641);

label_0x2498:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x249f;
}

label_0x249a:
t_645 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_645, 55bv8));
OF := AND_8((XOR_8(t_645, 55bv8)), (XOR_8(t_645, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_645)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x249d:
goto label_0x24a1;

label_0x249f:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_129;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x24a1:
origDEST_649 := RCX[32:0][8:0];
origCOUNT_650 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), CF, RSHIFT_8(origDEST_649, (MINUS_8(8bv8, origCOUNT_650)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_650 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_130));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv8)), AF, unconstrained_131);

label_0x24a4:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x24a6:
t_657 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_657)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_657, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_657, 4bv8)), t_657)), 2bv8)), (XOR_8((RSHIFT_8(t_657, 4bv8)), t_657)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_657, 4bv8)), t_657)), 2bv8)), (XOR_8((RSHIFT_8(t_657, 4bv8)), t_657)))))[1:0]));
SF := t_657[8:7];
ZF := bool2bv(0bv8 == t_657);

label_0x24a9:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x24b6;
}

label_0x24ab:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x24ae:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_133;
SF := unconstrained_134;
AF := unconstrained_135;
PF := unconstrained_136;

label_0x24b2:
if (bv2bool(NOT_1(CF))) {
  goto label_0x24b6;
}

label_0x24b4:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x24b6:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19338bv64, 9404bv64)), 0bv64), RCX[32:0][8:0]);

label_0x24bc:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 34bv64))));

label_0x24c1:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R9, 35bv64))));

label_0x24c6:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x24c9:
t_661 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_661)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_661, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_661, 4bv8)), t_661)), 2bv8)), (XOR_8((RSHIFT_8(t_661, 4bv8)), t_661)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_661, 4bv8)), t_661)), 2bv8)), (XOR_8((RSHIFT_8(t_661, 4bv8)), t_661)))))[1:0]));
SF := t_661[8:7];
ZF := bool2bv(0bv8 == t_661);

label_0x24cb:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x24d2;
}

label_0x24cd:
t_665 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_665, 48bv8));
OF := AND_8((XOR_8(t_665, 48bv8)), (XOR_8(t_665, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_665)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x24d0:
goto label_0x24e0;

label_0x24d2:
RAX := (0bv32 ++ PLUS_64(RCX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x24d5:
t_669 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_669)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_669, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_669, 4bv8)), t_669)), 2bv8)), (XOR_8((RSHIFT_8(t_669, 4bv8)), t_669)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_669, 4bv8)), t_669)), 2bv8)), (XOR_8((RSHIFT_8(t_669, 4bv8)), t_669)))))[1:0]));
SF := t_669[8:7];
ZF := bool2bv(0bv8 == t_669);

label_0x24d7:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x24de;
}

label_0x24d9:
t_673 := RCX[32:0][8:0];
RCX := (RCX[64:8]) ++ (MINUS_8((RCX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_673, 55bv8));
OF := AND_8((XOR_8(t_673, 55bv8)), (XOR_8(t_673, (RCX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RCX[32:0][8:0]), t_673)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x24dc:
goto label_0x24e0;

label_0x24de:
RCX := (RCX[64:8]) ++ 0bv8;
AF := unconstrained_137;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x24e0:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967248bv32)[32:0]);

label_0x24e3:
t_677 := MINUS_8((RAX[32:0][8:0]), 9bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 9bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 9bv8)), (XOR_8((RAX[32:0][8:0]), t_677)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_677, (RAX[32:0][8:0]))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_677, 4bv8)), t_677)), 2bv8)), (XOR_8((RSHIFT_8(t_677, 4bv8)), t_677)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_677, 4bv8)), t_677)), 2bv8)), (XOR_8((RSHIFT_8(t_677, 4bv8)), t_677)))))[1:0]));
SF := t_677[8:7];
ZF := bool2bv(0bv8 == t_677);

label_0x24e5:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x24ec;
}

label_0x24e7:
t_681 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 48bv8));
CF := bool2bv(LT_8(t_681, 48bv8));
OF := AND_8((XOR_8(t_681, 48bv8)), (XOR_8(t_681, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_681)), 48bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x24ea:
goto label_0x24fa;

label_0x24ec:
RAX := (0bv32 ++ PLUS_64(RDX, 4294967295bv32 ++ 4294967231bv32)[32:0]);

label_0x24ef:
t_685 := MINUS_8((RAX[32:0][8:0]), 5bv8);
CF := bool2bv(LT_8((RAX[32:0][8:0]), 5bv8));
OF := AND_8((XOR_8((RAX[32:0][8:0]), 5bv8)), (XOR_8((RAX[32:0][8:0]), t_685)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_685, (RAX[32:0][8:0]))), 5bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_685, 4bv8)), t_685)), 2bv8)), (XOR_8((RSHIFT_8(t_685, 4bv8)), t_685)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_685, 4bv8)), t_685)), 2bv8)), (XOR_8((RSHIFT_8(t_685, 4bv8)), t_685)))))[1:0]));
SF := t_685[8:7];
ZF := bool2bv(0bv8 == t_685);

label_0x24f1:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x24f8;
}

label_0x24f3:
t_689 := RDX[32:0][8:0];
RDX := (RDX[64:8]) ++ (MINUS_8((RDX[32:0][8:0]), 55bv8));
CF := bool2bv(LT_8(t_689, 55bv8));
OF := AND_8((XOR_8(t_689, 55bv8)), (XOR_8(t_689, (RDX[32:0][8:0]))))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((RDX[32:0][8:0]), t_689)), 55bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RDX[32:0][8:0]), 4bv8)), (RDX[32:0][8:0]))))))[1:0]));
SF := RDX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RDX[32:0][8:0]));

label_0x24f6:
goto label_0x24fa;

label_0x24f8:
RDX := (RDX[64:8]) ++ 0bv8;
AF := unconstrained_138;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x24fa:
origDEST_693 := RCX[32:0][8:0];
origCOUNT_694 := AND_8(4bv8, (MINUS_8(8bv8, 1bv8)));
RCX := (RCX[64:8]) ++ (LSHIFT_8((RCX[32:0][8:0]), (AND_8(4bv8, (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), CF, RSHIFT_8(origDEST_693, (MINUS_8(8bv8, origCOUNT_694)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_694 == 1bv8)), XOR_1((RCX[32:0][8:0][8:7]), CF), unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), SF, RCX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), ZF, bool2bv(0bv8 == (RCX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv8)), AF, unconstrained_140);

label_0x24fd:
RCX := (RCX[64:8]) ++ (OR_8((RCX[32:0][8:0]), (RDX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_141;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RCX[32:0][8:0]), 4bv8)), (RCX[32:0][8:0]))))))[1:0]));
SF := RCX[32:0][8:0][8:7];
ZF := bool2bv(0bv8 == (RCX[32:0][8:0]));

label_0x24ff:
t_701 := MINUS_8((RCX[32:0][8:0]), 44bv8);
CF := bool2bv(LT_8((RCX[32:0][8:0]), 44bv8));
OF := AND_8((XOR_8((RCX[32:0][8:0]), 44bv8)), (XOR_8((RCX[32:0][8:0]), t_701)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_701, (RCX[32:0][8:0]))), 44bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_701, 4bv8)), t_701)), 2bv8)), (XOR_8((RSHIFT_8(t_701, 4bv8)), t_701)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_701, 4bv8)), t_701)), 2bv8)), (XOR_8((RSHIFT_8(t_701, 4bv8)), t_701)))))[1:0]));
SF := t_701[8:7];
ZF := bool2bv(0bv8 == t_701);

label_0x2502:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x250f;
}

label_0x2504:
RAX := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x2507:
CF := RSHIFT_64(R8, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_142;
SF := unconstrained_143;
AF := unconstrained_144;
PF := unconstrained_145;

label_0x250b:
if (bv2bool(NOT_1(CF))) {
  goto label_0x250f;
}

label_0x250d:
RCX := (RCX[64:8]) ++ 88bv8;

label_0x250f:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(19250bv64, 9493bv64)), 0bv64), RCX[32:0][8:0]);

label_0x2515:
RAX := PLUS_64((PLUS_64(19228bv64, 9500bv64)), 0bv64)[64:0];

label_0x251c:

ra_705 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_122,origCOUNT_166,origCOUNT_210,origCOUNT_254,origCOUNT_298,origCOUNT_34,origCOUNT_342,origCOUNT_386,origCOUNT_430,origCOUNT_474,origCOUNT_518,origCOUNT_562,origCOUNT_606,origCOUNT_650,origCOUNT_694,origCOUNT_78,origDEST_121,origDEST_165,origDEST_209,origDEST_253,origDEST_297,origDEST_33,origDEST_341,origDEST_385,origDEST_429,origDEST_473,origDEST_517,origDEST_561,origDEST_605,origDEST_649,origDEST_693,origDEST_77,ra_705,t_1,t_101,t_105,t_109,t_113,t_117,t_129,t_13,t_133,t_137,t_141,t_145,t_149,t_153,t_157,t_161,t_17,t_173,t_177,t_181,t_185,t_189,t_193,t_197,t_201,t_205,t_21,t_217,t_221,t_225,t_229,t_233,t_237,t_241,t_245,t_249,t_25,t_261,t_265,t_269,t_273,t_277,t_281,t_285,t_289,t_29,t_293,t_305,t_309,t_313,t_317,t_321,t_325,t_329,t_333,t_337,t_349,t_353,t_357,t_361,t_365,t_369,t_373,t_377,t_381,t_393,t_397,t_401,t_405,t_409,t_41,t_413,t_417,t_421,t_425,t_437,t_441,t_445,t_449,t_45,t_453,t_457,t_461,t_465,t_469,t_481,t_485,t_489,t_49,t_493,t_497,t_5,t_501,t_505,t_509,t_513,t_525,t_529,t_53,t_533,t_537,t_541,t_545,t_549,t_553,t_557,t_569,t_57,t_573,t_577,t_581,t_585,t_589,t_593,t_597,t_601,t_61,t_613,t_617,t_621,t_625,t_629,t_633,t_637,t_641,t_645,t_65,t_657,t_661,t_665,t_669,t_673,t_677,t_681,t_685,t_689,t_69,t_701,t_73,t_85,t_89,t_9,t_93,t_97;

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
var R10: bv64;
var R11: bv64;
var RBX: bv64;
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
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_122: bv8;
var origCOUNT_166: bv8;
var origCOUNT_210: bv8;
var origCOUNT_254: bv8;
var origCOUNT_298: bv8;
var origCOUNT_34: bv8;
var origCOUNT_342: bv8;
var origCOUNT_386: bv8;
var origCOUNT_430: bv8;
var origCOUNT_474: bv8;
var origCOUNT_518: bv8;
var origCOUNT_562: bv8;
var origCOUNT_606: bv8;
var origCOUNT_650: bv8;
var origCOUNT_694: bv8;
var origCOUNT_78: bv8;
var origDEST_121: bv8;
var origDEST_165: bv8;
var origDEST_209: bv8;
var origDEST_253: bv8;
var origDEST_297: bv8;
var origDEST_33: bv8;
var origDEST_341: bv8;
var origDEST_385: bv8;
var origDEST_429: bv8;
var origDEST_473: bv8;
var origDEST_517: bv8;
var origDEST_561: bv8;
var origDEST_605: bv8;
var origDEST_649: bv8;
var origDEST_693: bv8;
var origDEST_77: bv8;
var ra_705: bv64;
var t_1: bv8;
var t_101: bv8;
var t_105: bv8;
var t_109: bv8;
var t_113: bv8;
var t_117: bv8;
var t_129: bv8;
var t_13: bv8;
var t_133: bv8;
var t_137: bv8;
var t_141: bv8;
var t_145: bv8;
var t_149: bv8;
var t_153: bv8;
var t_157: bv8;
var t_161: bv8;
var t_17: bv8;
var t_173: bv8;
var t_177: bv8;
var t_181: bv8;
var t_185: bv8;
var t_189: bv8;
var t_193: bv8;
var t_197: bv8;
var t_201: bv8;
var t_205: bv8;
var t_21: bv8;
var t_217: bv8;
var t_221: bv8;
var t_225: bv8;
var t_229: bv8;
var t_233: bv8;
var t_237: bv8;
var t_241: bv8;
var t_245: bv8;
var t_249: bv8;
var t_25: bv8;
var t_261: bv8;
var t_265: bv8;
var t_269: bv8;
var t_273: bv8;
var t_277: bv8;
var t_281: bv8;
var t_285: bv8;
var t_289: bv8;
var t_29: bv8;
var t_293: bv8;
var t_305: bv8;
var t_309: bv8;
var t_313: bv8;
var t_317: bv8;
var t_321: bv8;
var t_325: bv8;
var t_329: bv8;
var t_333: bv8;
var t_337: bv8;
var t_349: bv8;
var t_353: bv8;
var t_357: bv8;
var t_361: bv8;
var t_365: bv8;
var t_369: bv8;
var t_373: bv8;
var t_377: bv8;
var t_381: bv8;
var t_393: bv8;
var t_397: bv8;
var t_401: bv8;
var t_405: bv8;
var t_409: bv8;
var t_41: bv8;
var t_413: bv8;
var t_417: bv8;
var t_421: bv8;
var t_425: bv8;
var t_437: bv8;
var t_441: bv8;
var t_445: bv8;
var t_449: bv8;
var t_45: bv8;
var t_453: bv8;
var t_457: bv8;
var t_461: bv8;
var t_465: bv8;
var t_469: bv8;
var t_481: bv8;
var t_485: bv8;
var t_489: bv8;
var t_49: bv8;
var t_493: bv8;
var t_497: bv8;
var t_5: bv8;
var t_501: bv8;
var t_505: bv8;
var t_509: bv8;
var t_513: bv8;
var t_525: bv8;
var t_529: bv8;
var t_53: bv8;
var t_533: bv8;
var t_537: bv8;
var t_541: bv8;
var t_545: bv8;
var t_549: bv8;
var t_553: bv8;
var t_557: bv8;
var t_569: bv8;
var t_57: bv8;
var t_573: bv8;
var t_577: bv8;
var t_581: bv8;
var t_585: bv8;
var t_589: bv8;
var t_593: bv8;
var t_597: bv8;
var t_601: bv8;
var t_61: bv8;
var t_613: bv8;
var t_617: bv8;
var t_621: bv8;
var t_625: bv8;
var t_629: bv8;
var t_633: bv8;
var t_637: bv8;
var t_641: bv8;
var t_645: bv8;
var t_65: bv8;
var t_657: bv8;
var t_661: bv8;
var t_665: bv8;
var t_669: bv8;
var t_673: bv8;
var t_677: bv8;
var t_681: bv8;
var t_685: bv8;
var t_689: bv8;
var t_69: bv8;
var t_701: bv8;
var t_73: bv8;
var t_85: bv8;
var t_89: bv8;
var t_9: bv8;
var t_93: bv8;
var t_97: bv8;


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
