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
axiom _function_addr_low == 19520bv64;
axiom _function_addr_high == 20384bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x4c40:
t_1 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x4c42:
t_3 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x4c43:
t_5 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x4c44:
t_7 := R12;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_7);

label_0x4c46:
t_9 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_9);

label_0x4c48:
t_11 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_11);

label_0x4c4a:
t_13 := RSP;
RSP := MINUS_64(RSP, 40bv64);
CF := bool2bv(LT_64(t_13, 40bv64));
OF := AND_64((XOR_64(t_13, 40bv64)), (XOR_64(t_13, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_13)), 40bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4c4e:
t_17 := AND_8((LOAD_LE_8(mem, PLUS_64(R8, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))))[1:0]));
SF := t_17[8:7];
ZF := bool2bv(0bv8 == t_17);

label_0x4c53:
RBX := R9;

label_0x4c56:
R14 := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4c5e:
RDI := R8;

label_0x4c61:
RBP := (0bv32 ++ RDX[32:0]);

label_0x4c63:
R15 := RCX;

label_0x4c66:
R12 := (0bv32 ++ LOAD_LE_32(mem, R14));

label_0x4c69:
if (bv2bool(ZF)) {
  goto label_0x4cb5;
}

label_0x4c6b:
t_21 := MINUS_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), t_21)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_21, (LOAD_LE_64(mem, PLUS_64(R8, 16bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))))[1:0]));
SF := t_21[64:63];
ZF := bool2bv(0bv64 == t_21);

label_0x4c70:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4cb5;
}

label_0x4c72:
RAX := RBX;

label_0x4c75:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c7b:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c81:
if (bv2bool(ZF)) {
  goto label_0x4c84;
}

label_0x4c83:
assume false;

label_0x4c84:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(9541bv64, 19595bv64)), 0bv64));

label_0x4c8b:
RCX := RBX;

label_0x4c8e:
origDEST_29 := RCX;
origCOUNT_30 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_5);

label_0x4c92:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, (LSHIFT_64(RCX, 3bv64))));

label_0x4c96:
RAX := RBX;

label_0x4c99:
origDEST_35 := RAX;
origCOUNT_36 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_7);

label_0x4c9d:
CF := RSHIFT_64(RDX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x4ca1:
if (bv2bool(CF)) {
  goto label_0x4ca4;
}

label_0x4ca3:
assume false;

label_0x4ca4:
t1_41 := LOAD_LE_32(mem, R9);
t2_42 := RBP[32:0];
mem := STORE_LE_32(mem, R9, PLUS_32((LOAD_LE_32(mem, R9)), t2_42));
CF := bool2bv(LT_32((LOAD_LE_32(mem, R9)), t1_41));
OF := AND_1((bool2bv((t1_41[32:31]) == (t2_42[32:31]))), (XOR_1((t1_41[32:31]), (LOAD_LE_32(mem, R9)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, R9)), t1_41)), t2_42)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))))))[1:0]));
SF := LOAD_LE_32(mem, R9)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, R9)));

label_0x4ca7:
t1_47 := RSP;
t2_48 := 40bv64;
RSP := PLUS_64(RSP, t2_48);
CF := bool2bv(LT_64(RSP, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4cab:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4cad:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4caf:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4cb1:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4cb2:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4cb3:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4cb4:

ra_53 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x4cb5:
RAX := R14;

label_0x4cb8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RSI);

label_0x4cbd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4cc3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R13);

label_0x4cc8:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4cce:
if (bv2bool(ZF)) {
  goto label_0x4cd1;
}

label_0x4cd0:
assume false;

label_0x4cd1:
RSI := LOAD_LE_64(mem, PLUS_64((PLUS_64(9464bv64, 19672bv64)), 0bv64));

label_0x4cd8:
RCX := R14;

label_0x4cdb:
origDEST_59 := RCX;
origCOUNT_60 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_15);

label_0x4cdf:
RAX := R14;

label_0x4ce2:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_17);

label_0x4ce6:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RCX, 3bv64))));

label_0x4cea:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x4cee:
if (bv2bool(CF)) {
  goto label_0x4cf1;
}

label_0x4cf0:
assume false;

label_0x4cf1:
R13 := (0bv32 ++ 0bv32);
AF := unconstrained_22;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4cf4:
mem := STORE_LE_32(mem, R14, R13[32:0]);

label_0x4cf7:
t_71 := AND_32((RDX[32:0]), (RDX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))))[1:0]));
SF := t_71[32:31];
ZF := bool2bv(0bv32 == t_71);

label_0x4cf9:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4f16;
}

label_0x4cff:


label_0x4d00:
R8 := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, R15)));

label_0x4d04:
t_75 := RBP[32:0];
RBP := (0bv32 ++ MINUS_32((RBP[32:0]), 1bv32));
OF := AND_32((XOR_32(t_75, 1bv32)), (XOR_32(t_75, (RBP[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RBP[32:0]), t_75)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))))[1:0]));
SF := RBP[32:0][32:31];
ZF := bool2bv(0bv32 == (RBP[32:0]));

label_0x4d06:
t_79 := AND_8((LOAD_LE_8(mem, PLUS_64(RDI, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)), 2bv8)), (XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)), 2bv8)), (XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)))))[1:0]));
SF := t_79[8:7];
ZF := bool2bv(0bv8 == t_79);

label_0x4d0a:
if (bv2bool(ZF)) {
  goto label_0x4d16;
}

label_0x4d0c:
t_83 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), t_83)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_83, (LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))))), R13)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0x4d10:
if (bv2bool(ZF)) {
  goto label_0x4dee;
}

label_0x4d16:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4d1a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d20:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d26:
if (bv2bool(ZF)) {
  goto label_0x4d29;
}

label_0x4d28:
assume false;

label_0x4d29:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4d2d:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_28);

label_0x4d31:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4d35:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4d39:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_30);

label_0x4d3d:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x4d41:
if (bv2bool(CF)) {
  goto label_0x4d44;
}

label_0x4d43:
assume false;

label_0x4d44:
t_103 := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDI, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_103, 1bv32));
OF := AND_32((XOR_32(t_103, 1bv32)), (XOR_32(t_103, (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), t_103)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))));

label_0x4d48:
if (bv2bool(SF)) {
  goto label_0x4daf;
}

label_0x4d4a:
RDX := LOAD_LE_64(mem, RDI);

label_0x4d4d:
RAX := RDX;

label_0x4d50:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d56:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d5c:
if (bv2bool(ZF)) {
  goto label_0x4d5f;
}

label_0x4d5e:
assume false;

label_0x4d5f:
RAX := RDX;

label_0x4d62:
origDEST_111 := RAX;
origCOUNT_112 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_38);

label_0x4d66:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4d6a:
RAX := RDX;

label_0x4d6d:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_40);

label_0x4d71:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x4d75:
if (bv2bool(CF)) {
  goto label_0x4d78;
}

label_0x4d77:
assume false;

label_0x4d78:
RAX := RDI;

label_0x4d7b:
mem := STORE_LE_8(mem, RDX, R8[32:0][8:0]);

label_0x4d7e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d84:
RDX := (0bv32 ++ (0bv24 ++ R8[32:0][8:0]));

label_0x4d88:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d8e:
if (bv2bool(ZF)) {
  goto label_0x4d91;
}

label_0x4d90:
assume false;

label_0x4d91:
RAX := RDI;

label_0x4d94:
origDEST_127 := RAX;
origCOUNT_128 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_48);

label_0x4d98:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4d9c:
RAX := RDI;

label_0x4d9f:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_50);

label_0x4da3:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_51;
SF := unconstrained_52;
AF := unconstrained_53;
PF := unconstrained_54;

label_0x4da7:
if (bv2bool(CF)) {
  goto label_0x4daa;
}

label_0x4da9:
assume false;

label_0x4daa:
t_139 := LOAD_LE_64(mem, RDI);
mem := STORE_LE_64(mem, RDI, PLUS_64((LOAD_LE_64(mem, RDI)), 1bv64));
OF := AND_1((bool2bv((t_139[64:63]) == (1bv64[64:63]))), (XOR_1((t_139[64:63]), (LOAD_LE_64(mem, RDI)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDI)), t_139)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))))[1:0]));
SF := LOAD_LE_64(mem, RDI)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDI)));

label_0x4dad:
goto label_0x4db6;

label_0x4daf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 19892bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38b0"} true;
call arbitrary_func();

label_0x4db4:
RDX := (0bv32 ++ RAX[32:0]);

label_0x4db6:
t_143 := MINUS_32((RDX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RDX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RDX[32:0]), 4294967295bv32)), (XOR_32((RDX[32:0]), t_143)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_143, (RDX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))))[1:0]));
SF := t_143[32:31];
ZF := bool2bv(0bv32 == t_143);

label_0x4db9:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4dee;
}

label_0x4dbb:
RAX := RBX;

label_0x4dbe:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4dc4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4dca:
if (bv2bool(ZF)) {
  goto label_0x4dcd;
}

label_0x4dcc:
assume false;

label_0x4dcd:
RAX := RBX;

label_0x4dd0:
origDEST_151 := RAX;
origCOUNT_152 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), CF, LSHIFT_64(origDEST_151, (MINUS_64(64bv64, origCOUNT_152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_152 == 1bv64)), origDEST_151[64:63], unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), AF, unconstrained_58);

label_0x4dd4:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4dd8:
RAX := RBX;

label_0x4ddb:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_60);

label_0x4ddf:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_61;
SF := unconstrained_62;
AF := unconstrained_63;
PF := unconstrained_64;

label_0x4de3:
if (bv2bool(CF)) {
  goto label_0x4de6;
}

label_0x4de5:
assume false;

label_0x4de6:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x4dec:
goto label_0x4e1b;

label_0x4dee:
RAX := RBX;

label_0x4df1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4df7:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4dfd:
if (bv2bool(ZF)) {
  goto label_0x4e00;
}

label_0x4dff:
assume false;

label_0x4e00:
RAX := RBX;

label_0x4e03:
origDEST_167 := RAX;
origCOUNT_168 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_68);

label_0x4e07:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4e0b:
RAX := RBX;

label_0x4e0e:
origDEST_173 := RAX;
origCOUNT_174 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), CF, LSHIFT_64(origDEST_173, (MINUS_64(64bv64, origCOUNT_174)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv64)), origDEST_173[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), AF, unconstrained_70);

label_0x4e12:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_71;
SF := unconstrained_72;
AF := unconstrained_73;
PF := unconstrained_74;

label_0x4e16:
if (bv2bool(CF)) {
  goto label_0x4e19;
}

label_0x4e18:
assume false;

label_0x4e19:
t_179 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_179[32:31]) == (1bv32[32:31]))), (XOR_1((t_179[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_179)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x4e1b:
t_183 := R15;
R15 := PLUS_64(R15, 1bv64);
OF := AND_1((bool2bv((t_183[64:63]) == (1bv64[64:63]))), (XOR_1((t_183[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t_183)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x4e1e:
t_187 := MINUS_32((LOAD_LE_32(mem, RBX)), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RBX)), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RBX)), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, RBX)), t_187)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_187, (LOAD_LE_32(mem, RBX)))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))))[1:0]));
SF := t_187[32:31];
ZF := bool2bv(0bv32 == t_187);

label_0x4e21:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4f09;
}

label_0x4e27:
t_191 := MINUS_32((LOAD_LE_32(mem, R14)), 42bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, R14)), 42bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, R14)), 42bv32)), (XOR_32((LOAD_LE_32(mem, R14)), t_191)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_191, (LOAD_LE_32(mem, R14)))), 42bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))))[1:0]));
SF := t_191[32:31];
ZF := bool2bv(0bv32 == t_191);

label_0x4e2b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4f11;
}

label_0x4e31:
t_195 := AND_8((LOAD_LE_8(mem, PLUS_64(RDI, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)), 2bv8)), (XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)), 2bv8)), (XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)))))[1:0]));
SF := t_195[8:7];
ZF := bool2bv(0bv8 == t_195);

label_0x4e35:
if (bv2bool(ZF)) {
  goto label_0x4e45;
}

label_0x4e37:
t_199 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), t_199)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_199, (LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))))), R13)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x4e3b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4e45;
}

label_0x4e3d:
mem := STORE_LE_32(mem, RBX, R13[32:0]);

label_0x4e40:
goto label_0x4f09;

label_0x4e45:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4e49:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_76;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e4f:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e55:
if (bv2bool(ZF)) {
  goto label_0x4e58;
}

label_0x4e57:
assume false;

label_0x4e58:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4e5c:
origDEST_207 := RAX;
origCOUNT_208 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, LSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), origDEST_207[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_79);

label_0x4e60:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4e64:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4e68:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_81);

label_0x4e6c:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_82;
SF := unconstrained_83;
AF := unconstrained_84;
PF := unconstrained_85;

label_0x4e70:
if (bv2bool(CF)) {
  goto label_0x4e73;
}

label_0x4e72:
assume false;

label_0x4e73:
t_219 := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDI, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_219, 1bv32));
OF := AND_32((XOR_32(t_219, 1bv32)), (XOR_32(t_219, (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), t_219)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))));

label_0x4e77:
if (bv2bool(SF)) {
  goto label_0x4f5c;
}

label_0x4e7d:
RDX := LOAD_LE_64(mem, RDI);

label_0x4e80:
RAX := RDX;

label_0x4e83:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e89:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e8f:
if (bv2bool(ZF)) {
  goto label_0x4e92;
}

label_0x4e91:
assume false;

label_0x4e92:
RAX := RDX;

label_0x4e95:
origDEST_227 := RAX;
origCOUNT_228 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_89);

label_0x4e99:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4e9d:
RAX := RDX;

label_0x4ea0:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_91);

label_0x4ea4:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_92;
SF := unconstrained_93;
AF := unconstrained_94;
PF := unconstrained_95;

label_0x4ea8:
if (bv2bool(CF)) {
  goto label_0x4eab;
}

label_0x4eaa:
assume false;

label_0x4eab:
RAX := RDI;

label_0x4eae:
mem := STORE_LE_8(mem, RDX, 63bv8);

label_0x4eb1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4eb7:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_97;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ebd:
if (bv2bool(ZF)) {
  goto label_0x4ec0;
}

label_0x4ebf:
assume false;

label_0x4ec0:
RAX := RDI;

label_0x4ec3:
origDEST_243 := RAX;
origCOUNT_244 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_99);

label_0x4ec7:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4ecb:
RAX := RDI;

label_0x4ece:
origDEST_249 := RAX;
origCOUNT_250 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), CF, LSHIFT_64(origDEST_249, (MINUS_64(64bv64, origCOUNT_250)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_250 == 1bv64)), origDEST_249[64:63], unconstrained_100));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), AF, unconstrained_101);

label_0x4ed2:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_102;
SF := unconstrained_103;
AF := unconstrained_104;
PF := unconstrained_105;

label_0x4ed6:
if (bv2bool(CF)) {
  goto label_0x4ed9;
}

label_0x4ed8:
assume false;

label_0x4ed9:
t_255 := LOAD_LE_64(mem, RDI);
mem := STORE_LE_64(mem, RDI, PLUS_64((LOAD_LE_64(mem, RDI)), 1bv64));
OF := AND_1((bool2bv((t_255[64:63]) == (1bv64[64:63]))), (XOR_1((t_255[64:63]), (LOAD_LE_64(mem, RDI)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDI)), t_255)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))))[1:0]));
SF := LOAD_LE_64(mem, RDI)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDI)));

label_0x4edc:
RAX := RBX;

label_0x4edf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ee5:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4eeb:
if (bv2bool(ZF)) {
  goto label_0x4eee;
}

label_0x4eed:
assume false;

label_0x4eee:
RAX := RBX;

label_0x4ef1:
origDEST_263 := RAX;
origCOUNT_264 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_109);

label_0x4ef5:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4ef9:
RAX := RBX;

label_0x4efc:
origDEST_269 := RAX;
origCOUNT_270 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_111);

label_0x4f00:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_112;
SF := unconstrained_113;
AF := unconstrained_114;
PF := unconstrained_115;

label_0x4f04:
if (bv2bool(CF)) {
  goto label_0x4f07;
}

label_0x4f06:
assume false;

label_0x4f07:
t_275 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_275[32:31]) == (1bv32[32:31]))), (XOR_1((t_275[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_275)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x4f09:
t_279 := AND_32((RBP[32:0]), (RBP[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))))[1:0]));
SF := t_279[32:31];
ZF := bool2bv(0bv32 == t_279);

label_0x4f0b:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x4d00;
}

label_0x4f11:
t_283 := MINUS_32((LOAD_LE_32(mem, R14)), (R13[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, R14)), (R13[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, R14)), (R13[32:0]))), (XOR_32((LOAD_LE_32(mem, R14)), t_283)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_283, (LOAD_LE_32(mem, R14)))), (R13[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))))[1:0]));
SF := t_283[32:31];
ZF := bool2bv(0bv32 == t_283);

label_0x4f14:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4f44;
}

label_0x4f16:
RAX := R14;

label_0x4f19:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f1f:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f25:
if (bv2bool(ZF)) {
  goto label_0x4f28;
}

label_0x4f27:
assume false;

label_0x4f28:
RAX := R14;

label_0x4f2b:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_120);

label_0x4f2f:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4f33:
RAX := R14;

label_0x4f36:
origDEST_297 := RAX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_122);

label_0x4f3a:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_123;
SF := unconstrained_124;
AF := unconstrained_125;
PF := unconstrained_126;

label_0x4f3e:
if (bv2bool(CF)) {
  goto label_0x4f41;
}

label_0x4f40:
assume false;

label_0x4f41:
mem := STORE_LE_32(mem, R14, R12[32:0]);

label_0x4f44:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4f49:
R13 := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4f4e:
t1_303 := RSP;
t2_304 := 40bv64;
RSP := PLUS_64(RSP, t2_304);
CF := bool2bv(LT_64(RSP, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4f52:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f54:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f56:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f58:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f59:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f5a:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4f5b:

ra_309 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x4f5c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 20321bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38b0"} true;
call arbitrary_func();

label_0x4f61:
t_311 := MINUS_32((RAX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RAX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RAX[32:0]), 4294967295bv32)), (XOR_32((RAX[32:0]), t_311)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_311, (RAX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))))[1:0]));
SF := t_311[32:31];
ZF := bool2bv(0bv32 == t_311);

label_0x4f64:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4edc;
}

label_0x4f6a:
RAX := RBX;

label_0x4f6d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f73:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_128;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f79:
if (bv2bool(ZF)) {
  goto label_0x4f7c;
}

label_0x4f7b:
assume false;

label_0x4f7c:
RAX := RBX;

label_0x4f7f:
origDEST_319 := RAX;
origCOUNT_320 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), CF, LSHIFT_64(origDEST_319, (MINUS_64(64bv64, origCOUNT_320)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_320 == 1bv64)), origDEST_319[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), AF, unconstrained_130);

label_0x4f83:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4f87:
RAX := RBX;

label_0x4f8a:
origDEST_325 := RAX;
origCOUNT_326 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_132);

label_0x4f8e:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_133;
SF := unconstrained_134;
AF := unconstrained_135;
PF := unconstrained_136;

label_0x4f92:
if (bv2bool(CF)) {
  goto label_0x4f95;
}

label_0x4f94:
assume false;

label_0x4f95:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x4f9b:
goto label_0x4f09;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R12,R13,R14,R15,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_112,origCOUNT_118,origCOUNT_128,origCOUNT_134,origCOUNT_152,origCOUNT_158,origCOUNT_168,origCOUNT_174,origCOUNT_208,origCOUNT_214,origCOUNT_228,origCOUNT_234,origCOUNT_244,origCOUNT_250,origCOUNT_264,origCOUNT_270,origCOUNT_292,origCOUNT_298,origCOUNT_30,origCOUNT_320,origCOUNT_326,origCOUNT_36,origCOUNT_60,origCOUNT_66,origCOUNT_92,origCOUNT_98,origDEST_111,origDEST_117,origDEST_127,origDEST_133,origDEST_151,origDEST_157,origDEST_167,origDEST_173,origDEST_207,origDEST_213,origDEST_227,origDEST_233,origDEST_243,origDEST_249,origDEST_263,origDEST_269,origDEST_29,origDEST_291,origDEST_297,origDEST_319,origDEST_325,origDEST_35,origDEST_59,origDEST_65,origDEST_91,origDEST_97,ra_309,ra_53,t1_303,t1_41,t1_47,t2_304,t2_42,t2_48,t_1,t_103,t_11,t_13,t_139,t_143,t_17,t_179,t_183,t_187,t_191,t_195,t_199,t_21,t_219,t_255,t_275,t_279,t_283,t_3,t_311,t_5,t_7,t_71,t_75,t_79,t_83,t_9;

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
var R10: bv64;
var R11: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
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
var origCOUNT_112: bv64;
var origCOUNT_118: bv64;
var origCOUNT_128: bv64;
var origCOUNT_134: bv64;
var origCOUNT_152: bv64;
var origCOUNT_158: bv64;
var origCOUNT_168: bv64;
var origCOUNT_174: bv64;
var origCOUNT_208: bv64;
var origCOUNT_214: bv64;
var origCOUNT_228: bv64;
var origCOUNT_234: bv64;
var origCOUNT_244: bv64;
var origCOUNT_250: bv64;
var origCOUNT_264: bv64;
var origCOUNT_270: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_30: bv64;
var origCOUNT_320: bv64;
var origCOUNT_326: bv64;
var origCOUNT_36: bv64;
var origCOUNT_60: bv64;
var origCOUNT_66: bv64;
var origCOUNT_92: bv64;
var origCOUNT_98: bv64;
var origDEST_111: bv64;
var origDEST_117: bv64;
var origDEST_127: bv64;
var origDEST_133: bv64;
var origDEST_151: bv64;
var origDEST_157: bv64;
var origDEST_167: bv64;
var origDEST_173: bv64;
var origDEST_207: bv64;
var origDEST_213: bv64;
var origDEST_227: bv64;
var origDEST_233: bv64;
var origDEST_243: bv64;
var origDEST_249: bv64;
var origDEST_263: bv64;
var origDEST_269: bv64;
var origDEST_29: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_319: bv64;
var origDEST_325: bv64;
var origDEST_35: bv64;
var origDEST_59: bv64;
var origDEST_65: bv64;
var origDEST_91: bv64;
var origDEST_97: bv64;
var ra_309: bv64;
var ra_53: bv64;
var t1_303: bv64;
var t1_41: bv32;
var t1_47: bv64;
var t2_304: bv64;
var t2_42: bv32;
var t2_48: bv64;
var t_1: bv64;
var t_103: bv32;
var t_11: bv64;
var t_13: bv64;
var t_139: bv64;
var t_143: bv32;
var t_17: bv8;
var t_179: bv32;
var t_183: bv64;
var t_187: bv32;
var t_191: bv32;
var t_195: bv8;
var t_199: bv64;
var t_21: bv64;
var t_219: bv32;
var t_255: bv64;
var t_275: bv32;
var t_279: bv32;
var t_283: bv32;
var t_3: bv64;
var t_311: bv32;
var t_5: bv64;
var t_7: bv64;
var t_71: bv32;
var t_75: bv32;
var t_79: bv8;
var t_83: bv64;
var t_9: bv64;


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
