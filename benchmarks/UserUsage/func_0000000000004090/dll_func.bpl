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
axiom _function_addr_low == 16528bv64;
axiom _function_addr_high == 17392bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x4090:
t_1 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x4092:
t_3 := RBP;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x4093:
t_5 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x4094:
t_7 := R12;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_7);

label_0x4096:
t_9 := R14;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_9);

label_0x4098:
t_11 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_11);

label_0x409a:
t_13 := RSP;
RSP := MINUS_64(RSP, 40bv64);
CF := bool2bv(LT_64(t_13, 40bv64));
OF := AND_64((XOR_64(t_13, 40bv64)), (XOR_64(t_13, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_13)), 40bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x409e:
t_17 := AND_8((LOAD_LE_8(mem, PLUS_64(R8, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)), 2bv8)), (XOR_8((RSHIFT_8(t_17, 4bv8)), t_17)))))[1:0]));
SF := t_17[8:7];
ZF := bool2bv(0bv8 == t_17);

label_0x40a3:
RBX := R9;

label_0x40a6:
R14 := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x40ae:
RDI := R8;

label_0x40b1:
RBP := (0bv32 ++ RDX[32:0]);

label_0x40b3:
R15 := RCX;

label_0x40b6:
R12 := (0bv32 ++ LOAD_LE_32(mem, R14));

label_0x40b9:
if (bv2bool(ZF)) {
  goto label_0x4105;
}

label_0x40bb:
t_21 := MINUS_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(R8, 16bv64))), t_21)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_21, (LOAD_LE_64(mem, PLUS_64(R8, 16bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))))[1:0]));
SF := t_21[64:63];
ZF := bool2bv(0bv64 == t_21);

label_0x40c0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4105;
}

label_0x40c2:
RAX := RBX;

label_0x40c5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x40cb:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x40d1:
if (bv2bool(ZF)) {
  goto label_0x40d4;
}

label_0x40d3:
assume false;

label_0x40d4:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(8389bv64, 16603bv64)), 0bv64));

label_0x40db:
RCX := RBX;

label_0x40de:
origDEST_29 := RCX;
origCOUNT_30 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_5);

label_0x40e2:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, (LSHIFT_64(RCX, 3bv64))));

label_0x40e6:
RAX := RBX;

label_0x40e9:
origDEST_35 := RAX;
origCOUNT_36 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_7);

label_0x40ed:
CF := RSHIFT_64(RDX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x40f1:
if (bv2bool(CF)) {
  goto label_0x40f4;
}

label_0x40f3:
assume false;

label_0x40f4:
t1_41 := LOAD_LE_32(mem, R9);
t2_42 := RBP[32:0];
mem := STORE_LE_32(mem, R9, PLUS_32((LOAD_LE_32(mem, R9)), t2_42));
CF := bool2bv(LT_32((LOAD_LE_32(mem, R9)), t1_41));
OF := AND_1((bool2bv((t1_41[32:31]) == (t2_42[32:31]))), (XOR_1((t1_41[32:31]), (LOAD_LE_32(mem, R9)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, R9)), t1_41)), t2_42)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R9)), 4bv32)), (LOAD_LE_32(mem, R9)))))))[1:0]));
SF := LOAD_LE_32(mem, R9)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, R9)));

label_0x40f7:
t1_47 := RSP;
t2_48 := 40bv64;
RSP := PLUS_64(RSP, t2_48);
CF := bool2bv(LT_64(RSP, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x40fb:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x40fd:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x40ff:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4101:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4102:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4103:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4104:

ra_53 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x4105:
RAX := R14;

label_0x4108:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RSI);

label_0x410d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4113:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R13);

label_0x4118:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x411e:
if (bv2bool(ZF)) {
  goto label_0x4121;
}

label_0x4120:
assume false;

label_0x4121:
RSI := LOAD_LE_64(mem, PLUS_64((PLUS_64(8312bv64, 16680bv64)), 0bv64));

label_0x4128:
RCX := R14;

label_0x412b:
origDEST_59 := RCX;
origCOUNT_60 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_15);

label_0x412f:
RAX := R14;

label_0x4132:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_17);

label_0x4136:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RCX, 3bv64))));

label_0x413a:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x413e:
if (bv2bool(CF)) {
  goto label_0x4141;
}

label_0x4140:
assume false;

label_0x4141:
R13 := (0bv32 ++ 0bv32);
AF := unconstrained_22;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4144:
mem := STORE_LE_32(mem, R14, R13[32:0]);

label_0x4147:
t_71 := AND_32((RDX[32:0]), (RDX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))))[1:0]));
SF := t_71[32:31];
ZF := bool2bv(0bv32 == t_71);

label_0x4149:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x4366;
}

label_0x414f:


label_0x4150:
R8 := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, R15)));

label_0x4154:
t_75 := RBP[32:0];
RBP := (0bv32 ++ MINUS_32((RBP[32:0]), 1bv32));
OF := AND_32((XOR_32(t_75, 1bv32)), (XOR_32(t_75, (RBP[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RBP[32:0]), t_75)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBP[32:0]), 4bv32)), (RBP[32:0]))))))[1:0]));
SF := RBP[32:0][32:31];
ZF := bool2bv(0bv32 == (RBP[32:0]));

label_0x4156:
t_79 := AND_8((LOAD_LE_8(mem, PLUS_64(RDI, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)), 2bv8)), (XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)), 2bv8)), (XOR_8((RSHIFT_8(t_79, 4bv8)), t_79)))))[1:0]));
SF := t_79[8:7];
ZF := bool2bv(0bv8 == t_79);

label_0x415a:
if (bv2bool(ZF)) {
  goto label_0x4166;
}

label_0x415c:
t_83 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), t_83)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_83, (LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))))), R13)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0x4160:
if (bv2bool(ZF)) {
  goto label_0x423e;
}

label_0x4166:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x416a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4170:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4176:
if (bv2bool(ZF)) {
  goto label_0x4179;
}

label_0x4178:
assume false;

label_0x4179:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x417d:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_28);

label_0x4181:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4185:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4189:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_30);

label_0x418d:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x4191:
if (bv2bool(CF)) {
  goto label_0x4194;
}

label_0x4193:
assume false;

label_0x4194:
t_103 := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDI, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_103, 1bv32));
OF := AND_32((XOR_32(t_103, 1bv32)), (XOR_32(t_103, (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), t_103)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))));

label_0x4198:
if (bv2bool(SF)) {
  goto label_0x41ff;
}

label_0x419a:
RDX := LOAD_LE_64(mem, RDI);

label_0x419d:
RAX := RDX;

label_0x41a0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41a6:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41ac:
if (bv2bool(ZF)) {
  goto label_0x41af;
}

label_0x41ae:
assume false;

label_0x41af:
RAX := RDX;

label_0x41b2:
origDEST_111 := RAX;
origCOUNT_112 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_38);

label_0x41b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x41ba:
RAX := RDX;

label_0x41bd:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_40);

label_0x41c1:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x41c5:
if (bv2bool(CF)) {
  goto label_0x41c8;
}

label_0x41c7:
assume false;

label_0x41c8:
RAX := RDI;

label_0x41cb:
mem := STORE_LE_8(mem, RDX, R8[32:0][8:0]);

label_0x41ce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41d4:
RDX := (0bv32 ++ (0bv24 ++ R8[32:0][8:0]));

label_0x41d8:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41de:
if (bv2bool(ZF)) {
  goto label_0x41e1;
}

label_0x41e0:
assume false;

label_0x41e1:
RAX := RDI;

label_0x41e4:
origDEST_127 := RAX;
origCOUNT_128 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_48);

label_0x41e8:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x41ec:
RAX := RDI;

label_0x41ef:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_50);

label_0x41f3:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_51;
SF := unconstrained_52;
AF := unconstrained_53;
PF := unconstrained_54;

label_0x41f7:
if (bv2bool(CF)) {
  goto label_0x41fa;
}

label_0x41f9:
assume false;

label_0x41fa:
t_139 := LOAD_LE_64(mem, RDI);
mem := STORE_LE_64(mem, RDI, PLUS_64((LOAD_LE_64(mem, RDI)), 1bv64));
OF := AND_1((bool2bv((t_139[64:63]) == (1bv64[64:63]))), (XOR_1((t_139[64:63]), (LOAD_LE_64(mem, RDI)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDI)), t_139)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))))[1:0]));
SF := LOAD_LE_64(mem, RDI)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDI)));

label_0x41fd:
goto label_0x4206;

label_0x41ff:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 16900bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2d00"} true;
call arbitrary_func();

label_0x4204:
RDX := (0bv32 ++ RAX[32:0]);

label_0x4206:
t_143 := MINUS_32((RDX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RDX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RDX[32:0]), 4294967295bv32)), (XOR_32((RDX[32:0]), t_143)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_143, (RDX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)), 2bv32)), (XOR_32((RSHIFT_32(t_143, 4bv32)), t_143)))))[1:0]));
SF := t_143[32:31];
ZF := bool2bv(0bv32 == t_143);

label_0x4209:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x423e;
}

label_0x420b:
RAX := RBX;

label_0x420e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4214:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x421a:
if (bv2bool(ZF)) {
  goto label_0x421d;
}

label_0x421c:
assume false;

label_0x421d:
RAX := RBX;

label_0x4220:
origDEST_151 := RAX;
origCOUNT_152 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), CF, LSHIFT_64(origDEST_151, (MINUS_64(64bv64, origCOUNT_152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_152 == 1bv64)), origDEST_151[64:63], unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), AF, unconstrained_58);

label_0x4224:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4228:
RAX := RBX;

label_0x422b:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_60);

label_0x422f:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_61;
SF := unconstrained_62;
AF := unconstrained_63;
PF := unconstrained_64;

label_0x4233:
if (bv2bool(CF)) {
  goto label_0x4236;
}

label_0x4235:
assume false;

label_0x4236:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x423c:
goto label_0x426b;

label_0x423e:
RAX := RBX;

label_0x4241:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4247:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x424d:
if (bv2bool(ZF)) {
  goto label_0x4250;
}

label_0x424f:
assume false;

label_0x4250:
RAX := RBX;

label_0x4253:
origDEST_167 := RAX;
origCOUNT_168 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_68);

label_0x4257:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x425b:
RAX := RBX;

label_0x425e:
origDEST_173 := RAX;
origCOUNT_174 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), CF, LSHIFT_64(origDEST_173, (MINUS_64(64bv64, origCOUNT_174)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv64)), origDEST_173[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), AF, unconstrained_70);

label_0x4262:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_71;
SF := unconstrained_72;
AF := unconstrained_73;
PF := unconstrained_74;

label_0x4266:
if (bv2bool(CF)) {
  goto label_0x4269;
}

label_0x4268:
assume false;

label_0x4269:
t_179 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_179[32:31]) == (1bv32[32:31]))), (XOR_1((t_179[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_179)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x426b:
t_183 := R15;
R15 := PLUS_64(R15, 1bv64);
OF := AND_1((bool2bv((t_183[64:63]) == (1bv64[64:63]))), (XOR_1((t_183[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t_183)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x426e:
t_187 := MINUS_32((LOAD_LE_32(mem, RBX)), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RBX)), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RBX)), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, RBX)), t_187)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_187, (LOAD_LE_32(mem, RBX)))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)), 2bv32)), (XOR_32((RSHIFT_32(t_187, 4bv32)), t_187)))))[1:0]));
SF := t_187[32:31];
ZF := bool2bv(0bv32 == t_187);

label_0x4271:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4359;
}

label_0x4277:
t_191 := MINUS_32((LOAD_LE_32(mem, R14)), 42bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, R14)), 42bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, R14)), 42bv32)), (XOR_32((LOAD_LE_32(mem, R14)), t_191)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_191, (LOAD_LE_32(mem, R14)))), 42bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)), 2bv32)), (XOR_32((RSHIFT_32(t_191, 4bv32)), t_191)))))[1:0]));
SF := t_191[32:31];
ZF := bool2bv(0bv32 == t_191);

label_0x427b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4361;
}

label_0x4281:
t_195 := AND_8((LOAD_LE_8(mem, PLUS_64(RDI, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)), 2bv8)), (XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)), 2bv8)), (XOR_8((RSHIFT_8(t_195, 4bv8)), t_195)))))[1:0]));
SF := t_195[8:7];
ZF := bool2bv(0bv8 == t_195);

label_0x4285:
if (bv2bool(ZF)) {
  goto label_0x4295;
}

label_0x4287:
t_199 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), R13)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))), t_199)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_199, (LOAD_LE_64(mem, PLUS_64(RDI, 16bv64))))), R13)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x428b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4295;
}

label_0x428d:
mem := STORE_LE_32(mem, RBX, R13[32:0]);

label_0x4290:
goto label_0x4359;

label_0x4295:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x4299:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_76;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x429f:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x42a5:
if (bv2bool(ZF)) {
  goto label_0x42a8;
}

label_0x42a7:
assume false;

label_0x42a8:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x42ac:
origDEST_207 := RAX;
origCOUNT_208 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, LSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), origDEST_207[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_79);

label_0x42b0:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x42b4:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x42b8:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_81);

label_0x42bc:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_82;
SF := unconstrained_83;
AF := unconstrained_84;
PF := unconstrained_85;

label_0x42c0:
if (bv2bool(CF)) {
  goto label_0x42c3;
}

label_0x42c2:
assume false;

label_0x42c3:
t_219 := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDI, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_219, 1bv32));
OF := AND_32((XOR_32(t_219, 1bv32)), (XOR_32(t_219, (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), t_219)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDI, 8bv64))));

label_0x42c7:
if (bv2bool(SF)) {
  goto label_0x43ac;
}

label_0x42cd:
RDX := LOAD_LE_64(mem, RDI);

label_0x42d0:
RAX := RDX;

label_0x42d3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x42d9:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x42df:
if (bv2bool(ZF)) {
  goto label_0x42e2;
}

label_0x42e1:
assume false;

label_0x42e2:
RAX := RDX;

label_0x42e5:
origDEST_227 := RAX;
origCOUNT_228 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_89);

label_0x42e9:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x42ed:
RAX := RDX;

label_0x42f0:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_91);

label_0x42f4:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_92;
SF := unconstrained_93;
AF := unconstrained_94;
PF := unconstrained_95;

label_0x42f8:
if (bv2bool(CF)) {
  goto label_0x42fb;
}

label_0x42fa:
assume false;

label_0x42fb:
RAX := RDI;

label_0x42fe:
mem := STORE_LE_8(mem, RDX, 63bv8);

label_0x4301:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4307:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_97;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x430d:
if (bv2bool(ZF)) {
  goto label_0x4310;
}

label_0x430f:
assume false;

label_0x4310:
RAX := RDI;

label_0x4313:
origDEST_243 := RAX;
origCOUNT_244 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_99);

label_0x4317:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x431b:
RAX := RDI;

label_0x431e:
origDEST_249 := RAX;
origCOUNT_250 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), CF, LSHIFT_64(origDEST_249, (MINUS_64(64bv64, origCOUNT_250)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_250 == 1bv64)), origDEST_249[64:63], unconstrained_100));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), AF, unconstrained_101);

label_0x4322:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_102;
SF := unconstrained_103;
AF := unconstrained_104;
PF := unconstrained_105;

label_0x4326:
if (bv2bool(CF)) {
  goto label_0x4329;
}

label_0x4328:
assume false;

label_0x4329:
t_255 := LOAD_LE_64(mem, RDI);
mem := STORE_LE_64(mem, RDI, PLUS_64((LOAD_LE_64(mem, RDI)), 1bv64));
OF := AND_1((bool2bv((t_255[64:63]) == (1bv64[64:63]))), (XOR_1((t_255[64:63]), (LOAD_LE_64(mem, RDI)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDI)), t_255)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDI)), 4bv64)), (LOAD_LE_64(mem, RDI)))))))[1:0]));
SF := LOAD_LE_64(mem, RDI)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDI)));

label_0x432c:
RAX := RBX;

label_0x432f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4335:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x433b:
if (bv2bool(ZF)) {
  goto label_0x433e;
}

label_0x433d:
assume false;

label_0x433e:
RAX := RBX;

label_0x4341:
origDEST_263 := RAX;
origCOUNT_264 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_109);

label_0x4345:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4349:
RAX := RBX;

label_0x434c:
origDEST_269 := RAX;
origCOUNT_270 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_111);

label_0x4350:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_112;
SF := unconstrained_113;
AF := unconstrained_114;
PF := unconstrained_115;

label_0x4354:
if (bv2bool(CF)) {
  goto label_0x4357;
}

label_0x4356:
assume false;

label_0x4357:
t_275 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_275[32:31]) == (1bv32[32:31]))), (XOR_1((t_275[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_275)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x4359:
t_279 := AND_32((RBP[32:0]), (RBP[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))))[1:0]));
SF := t_279[32:31];
ZF := bool2bv(0bv32 == t_279);

label_0x435b:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x4150;
}

label_0x4361:
t_283 := MINUS_32((LOAD_LE_32(mem, R14)), (R13[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, R14)), (R13[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, R14)), (R13[32:0]))), (XOR_32((LOAD_LE_32(mem, R14)), t_283)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_283, (LOAD_LE_32(mem, R14)))), (R13[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))))[1:0]));
SF := t_283[32:31];
ZF := bool2bv(0bv32 == t_283);

label_0x4364:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4394;
}

label_0x4366:
RAX := R14;

label_0x4369:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x436f:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4375:
if (bv2bool(ZF)) {
  goto label_0x4378;
}

label_0x4377:
assume false;

label_0x4378:
RAX := R14;

label_0x437b:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_120);

label_0x437f:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x4383:
RAX := R14;

label_0x4386:
origDEST_297 := RAX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_122);

label_0x438a:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_123;
SF := unconstrained_124;
AF := unconstrained_125;
PF := unconstrained_126;

label_0x438e:
if (bv2bool(CF)) {
  goto label_0x4391;
}

label_0x4390:
assume false;

label_0x4391:
mem := STORE_LE_32(mem, R14, R12[32:0]);

label_0x4394:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4399:
R13 := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x439e:
t1_303 := RSP;
t2_304 := 40bv64;
RSP := PLUS_64(RSP, t2_304);
CF := bool2bv(LT_64(RSP, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x43a2:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43a4:
R14 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43a6:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43a8:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43a9:
RBP := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43aa:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x43ab:

ra_309 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x43ac:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 17329bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2d00"} true;
call arbitrary_func();

label_0x43b1:
t_311 := MINUS_32((RAX[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((RAX[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((RAX[32:0]), 4294967295bv32)), (XOR_32((RAX[32:0]), t_311)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_311, (RAX[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))))[1:0]));
SF := t_311[32:31];
ZF := bool2bv(0bv32 == t_311);

label_0x43b4:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x432c;
}

label_0x43ba:
RAX := RBX;

label_0x43bd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x43c3:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_128;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x43c9:
if (bv2bool(ZF)) {
  goto label_0x43cc;
}

label_0x43cb:
assume false;

label_0x43cc:
RAX := RBX;

label_0x43cf:
origDEST_319 := RAX;
origCOUNT_320 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), CF, LSHIFT_64(origDEST_319, (MINUS_64(64bv64, origCOUNT_320)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_320 == 1bv64)), origDEST_319[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), AF, unconstrained_130);

label_0x43d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x43d7:
RAX := RBX;

label_0x43da:
origDEST_325 := RAX;
origCOUNT_326 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_132);

label_0x43de:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_133;
SF := unconstrained_134;
AF := unconstrained_135;
PF := unconstrained_136;

label_0x43e2:
if (bv2bool(CF)) {
  goto label_0x43e5;
}

label_0x43e4:
assume false;

label_0x43e5:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x43eb:
goto label_0x4359;

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
