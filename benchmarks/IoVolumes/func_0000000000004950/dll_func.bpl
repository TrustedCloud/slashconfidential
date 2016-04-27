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
axiom _function_addr_low == 18768bv64;
axiom _function_addr_high == 19139bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x4950:
t_1 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x4952:
t_3 := RSP;
RSP := MINUS_64(RSP, 32bv64);
CF := bool2bv(LT_64(t_3, 32bv64));
OF := AND_64((XOR_64(t_3, 32bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 32bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4956:
t_7 := AND_8((LOAD_LE_8(mem, PLUS_64(RDX, 24bv64))), 64bv8);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)), 2bv8)), (XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)), 2bv8)), (XOR_8((RSHIFT_8(t_7, 4bv8)), t_7)))))[1:0]));
SF := t_7[8:7];
ZF := bool2bv(0bv8 == t_7);

label_0x495a:
RBX := R8;

label_0x495d:
R9 := (0bv32 ++ (0bv24 ++ RCX[32:0][8:0]));

label_0x4961:
if (bv2bool(ZF)) {
  goto label_0x49a5;
}

label_0x4963:
t_11 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RDX, 16bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RDX, 16bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RDX, 16bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RDX, 16bv64))), t_11)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_11, (LOAD_LE_64(mem, PLUS_64(RDX, 16bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x4968:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x49a5;
}

label_0x496a:
RAX := RBX;

label_0x496d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4973:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4979:
if (bv2bool(ZF)) {
  goto label_0x497c;
}

label_0x497b:
assume false;

label_0x497c:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(10317bv64, 18819bv64)), 0bv64));

label_0x4983:
RCX := RBX;

label_0x4986:
origDEST_19 := RCX;
origCOUNT_20 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_5);

label_0x498a:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, (LSHIFT_64(RCX, 3bv64))));

label_0x498e:
RAX := RBX;

label_0x4991:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, LSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), origDEST_25[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_7);

label_0x4995:
CF := RSHIFT_64(RDX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x4999:
if (bv2bool(CF)) {
  goto label_0x499c;
}

label_0x499b:
assume false;

label_0x499c:
t_31 := LOAD_LE_32(mem, R8);
mem := STORE_LE_32(mem, R8, PLUS_32((LOAD_LE_32(mem, R8)), 1bv32));
OF := AND_1((bool2bv((t_31[32:31]) == (1bv32[32:31]))), (XOR_1((t_31[32:31]), (LOAD_LE_32(mem, R8)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, R8)), t_31)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R8)), 4bv32)), (LOAD_LE_32(mem, R8)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R8)), 4bv32)), (LOAD_LE_32(mem, R8)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, R8)), 4bv32)), (LOAD_LE_32(mem, R8)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, R8)), 4bv32)), (LOAD_LE_32(mem, R8)))))))[1:0]));
SF := LOAD_LE_32(mem, R8)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, R8)));

label_0x499f:
t1_35 := RSP;
t2_36 := 32bv64;
RSP := PLUS_64(RSP, t2_36);
CF := bool2bv(LT_64(RSP, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x49a3:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x49a4:

ra_41 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x49a5:
RAX := PLUS_64(RDX, 8bv64)[64:0];

label_0x49a9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RDI);

label_0x49ae:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49b4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49ba:
if (bv2bool(ZF)) {
  goto label_0x49bd;
}

label_0x49bc:
assume false;

label_0x49bd:
RDI := LOAD_LE_64(mem, PLUS_64((PLUS_64(10252bv64, 18884bv64)), 0bv64));

label_0x49c4:
RCX := PLUS_64(RDX, 8bv64)[64:0];

label_0x49c8:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_15);

label_0x49cc:
RAX := PLUS_64(RDX, 8bv64)[64:0];

label_0x49d0:
origDEST_53 := RAX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_17);

label_0x49d4:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, (LSHIFT_64(RCX, 3bv64))));

label_0x49d8:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x49dc:
if (bv2bool(CF)) {
  goto label_0x49df;
}

label_0x49de:
assume false;

label_0x49df:
t_59 := LOAD_LE_32(mem, PLUS_64(RDX, 8bv64));
mem := STORE_LE_32(mem, PLUS_64(RDX, 8bv64), MINUS_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), 1bv32));
CF := bool2bv(LT_32(t_59, 1bv32));
OF := AND_32((XOR_32(t_59, 1bv32)), (XOR_32(t_59, (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), t_59)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))), 4bv32)), (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))))))))[1:0]));
SF := LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, PLUS_64(RDX, 8bv64))));

label_0x49e3:
if (bv2bool(SF)) {
  goto label_0x4a4a;
}

label_0x49e5:
R8 := LOAD_LE_64(mem, RDX);

label_0x49e8:
RAX := R8;

label_0x49eb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49f1:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49f7:
if (bv2bool(ZF)) {
  goto label_0x49fa;
}

label_0x49f9:
assume false;

label_0x49fa:
RAX := R8;

label_0x49fd:
origDEST_67 := RAX;
origCOUNT_68 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_25);

label_0x4a01:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, (LSHIFT_64(RAX, 3bv64))));

label_0x4a05:
RAX := R8;

label_0x4a08:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_27);

label_0x4a0c:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0x4a10:
if (bv2bool(CF)) {
  goto label_0x4a13;
}

label_0x4a12:
assume false;

label_0x4a13:
RAX := RDX;

label_0x4a16:
mem := STORE_LE_8(mem, R8, R9[32:0][8:0]);

label_0x4a19:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a1f:
R8 := (0bv32 ++ (0bv24 ++ R9[32:0][8:0]));

label_0x4a23:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a29:
if (bv2bool(ZF)) {
  goto label_0x4a2c;
}

label_0x4a2b:
assume false;

label_0x4a2c:
RAX := RDX;

label_0x4a2f:
origDEST_83 := RAX;
origCOUNT_84 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_35);

label_0x4a33:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, (LSHIFT_64(RAX, 3bv64))));

label_0x4a37:
RAX := RDX;

label_0x4a3a:
origDEST_89 := RAX;
origCOUNT_90 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, LSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), origDEST_89[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_37);

label_0x4a3e:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0x4a42:
if (bv2bool(CF)) {
  goto label_0x4a45;
}

label_0x4a44:
assume false;

label_0x4a45:
t_95 := LOAD_LE_64(mem, RDX);
mem := STORE_LE_64(mem, RDX, PLUS_64((LOAD_LE_64(mem, RDX)), 1bv64));
OF := AND_1((bool2bv((t_95[64:63]) == (1bv64[64:63]))), (XOR_1((t_95[64:63]), (LOAD_LE_64(mem, RDX)[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64((LOAD_LE_64(mem, RDX)), t_95)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDX)), 4bv64)), (LOAD_LE_64(mem, RDX)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDX)), 4bv64)), (LOAD_LE_64(mem, RDX)))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDX)), 4bv64)), (LOAD_LE_64(mem, RDX)))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, RDX)), 4bv64)), (LOAD_LE_64(mem, RDX)))))))[1:0]));
SF := LOAD_LE_64(mem, RDX)[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, RDX)));

label_0x4a48:
goto label_0x4a52;

label_0x4a4a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 19023bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38b0"} true;
call arbitrary_func();

label_0x4a4f:
R8 := (0bv32 ++ RAX[32:0]);

label_0x4a52:
RAX := RBX;

label_0x4a55:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a5b:
t_101 := MINUS_32((R8[32:0]), 4294967295bv32);
CF := bool2bv(LT_32((R8[32:0]), 4294967295bv32));
OF := AND_32((XOR_32((R8[32:0]), 4294967295bv32)), (XOR_32((R8[32:0]), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (R8[32:0]))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x4a5f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4a94;
}

label_0x4a61:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a67:
if (bv2bool(ZF)) {
  goto label_0x4a6a;
}

label_0x4a69:
assume false;

label_0x4a6a:
RAX := RBX;

label_0x4a6d:
origDEST_107 := RAX;
origCOUNT_108 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_45);

label_0x4a71:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, (LSHIFT_64(RAX, 3bv64))));

label_0x4a75:
RAX := RBX;

label_0x4a78:
origDEST_113 := RAX;
origCOUNT_114 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_47);

label_0x4a7c:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0x4a80:
if (bv2bool(CF)) {
  goto label_0x4a83;
}

label_0x4a82:
assume false;

label_0x4a83:
mem := STORE_LE_32(mem, RBX, 4294967295bv32);

label_0x4a89:
RDI := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4a8e:
t1_119 := RSP;
t2_120 := 32bv64;
RSP := PLUS_64(RSP, t2_120);
CF := bool2bv(LT_64(RSP, t1_119));
OF := AND_1((bool2bv((t1_119[64:63]) == (t2_120[64:63]))), (XOR_1((t1_119[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_119)), t2_120)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4a92:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4a93:

ra_125 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

label_0x4a94:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a9a:
if (bv2bool(ZF)) {
  goto label_0x4a9d;
}

label_0x4a9c:
assume false;

label_0x4a9d:
RAX := RBX;

label_0x4aa0:
origDEST_129 := RAX;
origCOUNT_130 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), CF, LSHIFT_64(origDEST_129, (MINUS_64(64bv64, origCOUNT_130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_130 == 1bv64)), origDEST_129[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), AF, unconstrained_54);

label_0x4aa4:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, (LSHIFT_64(RAX, 3bv64))));

label_0x4aa8:
RAX := RBX;

label_0x4aab:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_56);

label_0x4aaf:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x4ab3:
if (bv2bool(CF)) {
  goto label_0x4ab6;
}

label_0x4ab5:
assume false;

label_0x4ab6:
t_141 := LOAD_LE_32(mem, RBX);
mem := STORE_LE_32(mem, RBX, PLUS_32((LOAD_LE_32(mem, RBX)), 1bv32));
OF := AND_1((bool2bv((t_141[32:31]) == (1bv32[32:31]))), (XOR_1((t_141[32:31]), (LOAD_LE_32(mem, RBX)[32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((LOAD_LE_32(mem, RBX)), t_141)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))), 2bv32)), (XOR_32((RSHIFT_32((LOAD_LE_32(mem, RBX)), 4bv32)), (LOAD_LE_32(mem, RBX)))))))[1:0]));
SF := LOAD_LE_32(mem, RBX)[32:31];
ZF := bool2bv(0bv32 == (LOAD_LE_32(mem, RBX)));

label_0x4ab8:
RDI := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4abd:
t1_145 := RSP;
t2_146 := 32bv64;
RSP := PLUS_64(RSP, t2_146);
CF := bool2bv(LT_64(RSP, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4ac1:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x4ac2:

ra_151 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RBX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_108,origCOUNT_114,origCOUNT_130,origCOUNT_136,origCOUNT_20,origCOUNT_26,origCOUNT_48,origCOUNT_54,origCOUNT_68,origCOUNT_74,origCOUNT_84,origCOUNT_90,origDEST_107,origDEST_113,origDEST_129,origDEST_135,origDEST_19,origDEST_25,origDEST_47,origDEST_53,origDEST_67,origDEST_73,origDEST_83,origDEST_89,ra_125,ra_151,ra_41,t1_119,t1_145,t1_35,t2_120,t2_146,t2_36,t_1,t_101,t_11,t_141,t_3,t_31,t_59,t_7,t_95;

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
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R10: bv64;
var R11: bv64;
var RBP: bv64;
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
var RBX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_108: bv64;
var origCOUNT_114: bv64;
var origCOUNT_130: bv64;
var origCOUNT_136: bv64;
var origCOUNT_20: bv64;
var origCOUNT_26: bv64;
var origCOUNT_48: bv64;
var origCOUNT_54: bv64;
var origCOUNT_68: bv64;
var origCOUNT_74: bv64;
var origCOUNT_84: bv64;
var origCOUNT_90: bv64;
var origDEST_107: bv64;
var origDEST_113: bv64;
var origDEST_129: bv64;
var origDEST_135: bv64;
var origDEST_19: bv64;
var origDEST_25: bv64;
var origDEST_47: bv64;
var origDEST_53: bv64;
var origDEST_67: bv64;
var origDEST_73: bv64;
var origDEST_83: bv64;
var origDEST_89: bv64;
var ra_125: bv64;
var ra_151: bv64;
var ra_41: bv64;
var t1_119: bv64;
var t1_145: bv64;
var t1_35: bv64;
var t2_120: bv64;
var t2_146: bv64;
var t2_36: bv64;
var t_1: bv64;
var t_101: bv32;
var t_11: bv64;
var t_141: bv32;
var t_3: bv64;
var t_31: bv32;
var t_59: bv32;
var t_7: bv8;
var t_95: bv64;


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
