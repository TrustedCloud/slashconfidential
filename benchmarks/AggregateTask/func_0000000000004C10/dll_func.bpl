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
axiom _function_addr_low == 19472bv64;
axiom _function_addr_high == 19834bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x4c10:
t_1 := AND_32((RDX[32:0]), (RDX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1, 4bv32)), t_1)), 2bv32)), (XOR_32((RSHIFT_32(t_1, 4bv32)), t_1)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1, 4bv32)), t_1)), 2bv32)), (XOR_32((RSHIFT_32(t_1, 4bv32)), t_1)))))[1:0]));
SF := t_1[32:31];
ZF := bool2bv(0bv32 == t_1);

label_0x4c12:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4d79;
}

label_0x4c18:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RBX);

label_0x4c1d:
t_5 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x4c1e:
t_7 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_7);

label_0x4c1f:
t_9 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_9);

label_0x4c21:
t_11 := RSP;
RSP := MINUS_64(RSP, 32bv64);
CF := bool2bv(LT_64(t_11, 32bv64));
OF := AND_64((XOR_64(t_11, 32bv64)), (XOR_64(t_11, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_11)), 32bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4c25:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RSI);

label_0x4c2a:
RBX := R9;

label_0x4c2d:
RSI := LOAD_LE_64(mem, PLUS_64((PLUS_64(10380bv64, 19508bv64)), 0bv64));

label_0x4c34:
RDI := R8;

label_0x4c37:
RBP := (0bv32 ++ RDX[32:0]);

label_0x4c39:
R14 := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x4c3d:


label_0x4c40:
t_15 := RBP[32:0];
RBP := (0bv32 ++ MINUS_32((RBP[32:0]), 1bv32));
OF := AND_32((XOR_32(t_15, 1bv32)), (XOR_32(t_15, (RBP[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RBP[32:0]), t_15)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))))[1:0]));
SF := RBP[32:0][32:31];
ZF := bool2bv(0bv32 == (RBP[32:0]));

label_0x4c42:
t_19 := AND_8((LOAD_LE_8(mem, PLUS_64(RDI, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_19, 4bv8)), t_19)), 2bv8)), (XOR_8((RSHIFT_8(t_19, 4bv8)), t_19)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_19, 4bv8)), t_19)), 2bv8)), (XOR_8((RSHIFT_8(t_19, 4bv8)), t_19)))))[1:0]));
SF := t_19[8:7];
ZF := bool2bv(0bv8 == t_19);

label_0x4c46:
if (bv2bool(ZF)) {
  goto label_0x4c53;
}

label_0x4c48:
t_23 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), t_23)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_23, (LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))))[1:0]));
SF := t_23[64:63];
ZF := bool2bv(0bv64 == t_23);

label_0x4c4d:
if (bv2bool(ZF)) {
  goto label_0x4cf8;
}

label_0x4c53:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4c57:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c5d:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c63:
if (bv2bool(ZF)) {
  goto label_0x4c66;
}

label_0x4c65:
assume false;

label_0x4c66:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4c6a:
origDEST_31 := RAX;
origCOUNT_32 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), CF, LSHIFT_64(origDEST_31, (MINUS_64(64bv64, origCOUNT_32)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_32 == 1bv64)), origDEST_31[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), AF, unconstrained_6);

label_0x4c6e:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4c72:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4c76:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_8);

label_0x4c7a:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_9;
SF := unconstrained_10;
AF := unconstrained_11;
PF := unconstrained_12;

label_0x4c7e:
if (bv2bool(CF)) {
  goto label_0x4c81;
}

label_0x4c80:
assume false;

label_0x4c81:
t_43 := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDI, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_43, 1bv32));
OF := AND_32((XOR_32(t_43, 1bv32)), (XOR_32(t_43, (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), t_43)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))));

label_0x4c85:
if (bv2bool(SF)) {
  goto label_0x4cec;
}

label_0x4c87:
RDX := LOAD_LE_64(mem, RDI);

label_0x4c8a:
RAX := RDX;

label_0x4c8d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c93:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c99:
if (bv2bool(ZF)) {
  goto label_0x4c9c;
}

label_0x4c9b:
assume false;

label_0x4c9c:
RAX := RDX;

label_0x4c9f:
origDEST_51 := RAX;
origCOUNT_52 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), CF, LSHIFT_64(origDEST_51, (MINUS_64(64bv64, origCOUNT_52)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_52 == 1bv64)), origDEST_51[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), AF, unconstrained_16);

label_0x4ca3:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4ca7:
RAX := RDX;

label_0x4caa:
origDEST_57 := RAX;
origCOUNT_58 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_18);

label_0x4cae:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_19;
SF := unconstrained_20;
AF := unconstrained_21;
PF := unconstrained_22;

label_0x4cb2:
if (bv2bool(CF)) {
  goto label_0x4cb5;
}

label_0x4cb4:
assume false;

label_0x4cb5:
RAX := RDI;

label_0x4cb8:
mem := STORE_LE_8(mem, RDX, R14[32:0][8:0]);

label_0x4cbb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4cc1:
RDX := (0bv32 ++ (0bv24 ++ R14[32:0][8:0]));

label_0x4cc5:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ccb:
if (bv2bool(ZF)) {
  goto label_0x4cce;
}

label_0x4ccd:
assume false;

label_0x4cce:
RAX := RDI;

label_0x4cd1:
origDEST_67 := RAX;
origCOUNT_68 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_26);

label_0x4cd5:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4cd9:
RAX := RDI;

label_0x4cdc:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_28);

label_0x4ce0:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_29;
SF := unconstrained_30;
AF := unconstrained_31;
PF := unconstrained_32;

label_0x4ce4:
if (bv2bool(CF)) {
  goto label_0x4ce7;
}

label_0x4ce6:
assume false;

label_0x4ce7:
t_79 := LOAD_LE_64(mem, RDI);
mem := STORE_LE_64(mem, RDI, PLUS_64((LOAD_LE_64(mem, RDI)), 1bv64));
OF := AND_1((bool2bv((t_79[64:63]) == (1bv64[64:63]))), (XOR_1((t_79[64:63]), (LOAD_LE_64(mem, RDI)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDI)), t_79)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))))[1:0]));
SF := LOAD_LE_64(mem, RDI)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDI)));

label_0x4cea:
goto label_0x4cf3;

label_0x4cec:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 19697bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x39f0"} true;
call arbitrary_func();

label_0x4cf1:
RDX := (0bv32 ++ RAX[32:0]);

label_0x4cf3:
t_83 := MINUS_32((RDX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RDX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RDX[32:0]), 4294967295bv32)), (XOR_32((RDX[32:0]), t_83)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_83, (RDX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))))[1:0]));
SF := t_83[32:31];
ZF := bool2bv(0bv32 == t_83);

label_0x4cf6:
if (bv2bool(ZF)) {
  goto label_0x4d36;
}

label_0x4cf8:
RAX := RBX;

label_0x4cfb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d01:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d07:
if (bv2bool(ZF)) {
  goto label_0x4d0a;
}

label_0x4d09:
assume false;

label_0x4d0a:
RAX := RBX;

label_0x4d0d:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_36);

label_0x4d11:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4d15:
RAX := RBX;

label_0x4d18:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_38);

label_0x4d1c:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x4d20:
if (bv2bool(CF)) {
  goto label_0x4d23;
}

label_0x4d22:
assume false;

label_0x4d23:
t_103 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_103[32:31]) == (1bv32[32:31]))), (XOR_1((t_103[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_103)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x4d25:
RAX := (0bv32 ++ LOAD_LE_32(mem, RBX));

label_0x4d27:
t_107 := MINUS_32((RAX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RAX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RAX[32:0]), 4294967295bv32)), (XOR_32((RAX[32:0]), t_107)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_107, (RAX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))))[1:0]));
SF := t_107[32:31];
ZF := bool2bv(0bv32 == t_107);

label_0x4d2a:
if (bv2bool(ZF)) {
  goto label_0x4d67;
}

label_0x4d2c:
t_111 := AND_32((RBP[32:0]), (RBP[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)), 2bv32)), (XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)), 2bv32)), (XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)))))[1:0]));
SF := t_111[32:31];
ZF := bool2bv(0bv32 == t_111);

label_0x4d2e:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x4c40;
}

label_0x4d34:
goto label_0x4d67;

label_0x4d36:
RAX := RBX;

label_0x4d39:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d3f:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d45:
if (bv2bool(ZF)) {
  goto label_0x4d48;
}

label_0x4d47:
assume false;

label_0x4d48:
RAX := RBX;

label_0x4d4b:
origDEST_119 := RAX;
origCOUNT_120 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), CF, LSHIFT_64(origDEST_119, (MINUS_64(64bv64, origCOUNT_120)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_120 == 1bv64)), origDEST_119[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), AF, unconstrained_47);

label_0x4d4f:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4d53:
RAX := RBX;

label_0x4d56:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_49);

label_0x4d5a:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_50;
SF := unconstrained_51;
AF := unconstrained_52;
PF := unconstrained_53;

label_0x4d5e:
if (bv2bool(CF)) {
  goto label_0x4d61;
}

label_0x4d60:
assume false;

label_0x4d61:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x4d67:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x4d6c:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x4d71:
t1_131 := RSP;
t2_132 := 32bv64;
RSP := PLUS_64(RSP, t2_132);
CF := bool2bv(LT_64(RSP, t1_131));
OF := AND_1((bool2bv((t1_131[64:63]) == (t2_132[64:63]))), (XOR_1((t1_131[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_131)), t2_132)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4d75:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4d77:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4d78:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4d79:

ra_137 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R14,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_120,origCOUNT_126,origCOUNT_32,origCOUNT_38,origCOUNT_52,origCOUNT_58,origCOUNT_68,origCOUNT_74,origCOUNT_92,origCOUNT_98,origDEST_119,origDEST_125,origDEST_31,origDEST_37,origDEST_51,origDEST_57,origDEST_67,origDEST_73,origDEST_91,origDEST_97,ra_137,t1_131,t2_132,t_1,t_103,t_107,t_11,t_111,t_15,t_19,t_23,t_43,t_5,t_7,t_79,t_83,t_9;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R10: bv64;
var R11: bv64;
var R12: bv64;
var R13: bv64;
var R15: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
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
var origCOUNT_120: bv64;
var origCOUNT_126: bv64;
var origCOUNT_32: bv64;
var origCOUNT_38: bv64;
var origCOUNT_52: bv64;
var origCOUNT_58: bv64;
var origCOUNT_68: bv64;
var origCOUNT_74: bv64;
var origCOUNT_92: bv64;
var origCOUNT_98: bv64;
var origDEST_119: bv64;
var origDEST_125: bv64;
var origDEST_31: bv64;
var origDEST_37: bv64;
var origDEST_51: bv64;
var origDEST_57: bv64;
var origDEST_67: bv64;
var origDEST_73: bv64;
var origDEST_91: bv64;
var origDEST_97: bv64;
var ra_137: bv64;
var t1_131: bv64;
var t2_132: bv64;
var t_1: bv32;
var t_103: bv32;
var t_107: bv32;
var t_11: bv64;
var t_111: bv32;
var t_15: bv32;
var t_19: bv8;
var t_23: bv64;
var t_43: bv32;
var t_5: bv64;
var t_7: bv64;
var t_79: bv64;
var t_83: bv32;
var t_9: bv64;


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
