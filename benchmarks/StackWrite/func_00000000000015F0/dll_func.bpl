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
axiom _guard_writeTable_ptr == 12352bv64;
axiom _guard_callTable_ptr == 12336bv64;
axiom _function_addr_low == 5616bv64;
axiom _function_addr_high == 6001bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x15f0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x15f5:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x15f9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), 0bv64);

label_0x1602:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), 0bv64);

label_0x160b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), 0bv64);

label_0x1614:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), 0bv64);

label_0x161d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(10733bv64, 5667bv64)), 0bv64)));

label_0x1623:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x1625:
if (bv2bool(ZF)) {
  goto label_0x162c;
}

label_0x1627:
goto label_0x176c;

label_0x162c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x1634:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x1639:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x16b3;
}

label_0x163b:
RAX := PLUS_64((PLUS_64(10710bv64, 5698bv64)), 0bv64)[64:0];

label_0x1642:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1647:
R9 := PLUS_64(RSP, 64bv64)[64:0];

label_0x164c:
R8 := PLUS_64(RSP, 48bv64)[64:0];

label_0x1651:
RDX := PLUS_64(RSP, 72bv64)[64:0];

label_0x1656:
RCX := PLUS_64(RSP, 56bv64)[64:0];

label_0x165b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5728bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x13d0"} true;
call arbitrary_func();

label_0x1660:
t_13 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x1662:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1670;
}

label_0x1664:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1666:
RCX := (0bv32 ++ 3221225794bv32);

label_0x166b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5744bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1780"} true;
call arbitrary_func();

label_0x1670:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1675:
mem := STORE_LE_64(mem, RAX, 3bv64);

label_0x167c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1681:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1686:
mem := STORE_LE_64(mem, PLUS_64(RAX, 8bv64), RCX);

label_0x168a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x168f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1694:
mem := STORE_LE_64(mem, PLUS_64(RAX, 16bv64), RCX);

label_0x1698:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x169d:
mem := STORE_LE_64(mem, PLUS_64(RAX, 40bv64), 0bv64);

label_0x16a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x16aa:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(10671bv64, 5809bv64)), 0bv64), RAX);

label_0x16b1:
goto label_0x16bf;

label_0x16b3:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x16b5:
RCX := (0bv32 ++ 3221225794bv32);

label_0x16ba:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5823bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1780"} true;
call arbitrary_func();

label_0x16bf:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16c4:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x16c9:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x16ce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x16d3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5848bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x17e0"} true;
call arbitrary_func();

label_0x16d8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x16dc:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x16e1:
if (bv2bool(ZF)) {
  goto label_0x16ee;
}

label_0x16e3:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_5;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x16e5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x16e9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5870bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1780"} true;
call arbitrary_func();

label_0x16ee:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5875bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x17a0"} true;
call arbitrary_func();

label_0x16f3:
t_21 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x16f5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1732;
}

label_0x16f7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x16fc:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5889bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2b00"} true;
call arbitrary_func();

label_0x1701:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(10496bv64, 5895bv64)), 1bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(10496bv64, 5895bv64)), 1bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(10496bv64, 5895bv64)), 1bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(10496bv64, 5895bv64)), 1bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64((PLUS_64(10496bv64, 5895bv64)), 1bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x1708:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1714;
}

label_0x170a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x170f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5908bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2b90"} true;
call arbitrary_func();

label_0x1714:
RAX := (0bv32 ++ 1bv32);

label_0x1719:
t_29 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_29[64:0];
OF := bool2bv(t_29 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_29 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_7;
SF := unconstrained_8;
ZF := unconstrained_9;
AF := unconstrained_10;

label_0x171d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1722:
mem := STORE_LE_8(mem, PLUS_64(RCX, RAX), 1bv8);

label_0x1726:
RCX := PLUS_64((PLUS_64(4294967295bv32 ++ 4294966979bv32, 5933bv64)), 0bv64)[64:0];

label_0x172d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5938bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x21b0"} true;
call arbitrary_func();

label_0x1732:
t_31 := MINUS_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10526bv64, 5945bv64)), 1bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10526bv64, 5945bv64)), 1bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10526bv64, 5945bv64)), 1bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10526bv64, 5945bv64)), 1bv64))), t_31)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_31, (LOAD_LE_64(mem, PLUS_64((PLUS_64(10526bv64, 5945bv64)), 1bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))))[1:0]));
SF := t_31[64:63];
ZF := bool2bv(0bv64 == t_31);

label_0x173a:
if (bv2bool(ZF)) {
  goto label_0x174c;
}

label_0x173c:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x173f:
RDX := (0bv32 ++ 2bv32);

label_0x1744:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_12;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1746:

target_35 := LOAD_LE_64(mem, PLUS_64((PLUS_64(10508bv64, 5964bv64)), 0bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5964bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_35"} true;
call arbitrary_func();

label_0x174c:
t_37 := MINUS_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10492bv64, 5971bv64)), 1bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10492bv64, 5971bv64)), 1bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10492bv64, 5971bv64)), 1bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(10492bv64, 5971bv64)), 1bv64))), t_37)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_37, (LOAD_LE_64(mem, PLUS_64((PLUS_64(10492bv64, 5971bv64)), 1bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x1754:
if (bv2bool(ZF)) {
  goto label_0x176c;
}

label_0x1756:

target_41 := LOAD_LE_64(mem, PLUS_64((PLUS_64(10484bv64, 5980bv64)), 0bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5980bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_41"} true;
call arbitrary_func();

label_0x175c:
t_43 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))))[1:0]));
SF := t_43[32:31];
ZF := bool2bv(0bv32 == t_43);

label_0x175e:
if (bv2bool(ZF)) {
  goto label_0x176c;
}

label_0x1760:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_14;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1762:
RCX := (0bv32 ++ 3221225794bv32);

label_0x1767:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5996bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1780"} true;
call arbitrary_func();

label_0x176c:
t1_47 := RSP;
t2_48 := 88bv64;
RSP := PLUS_64(RSP, t2_48);
CF := bool2bv(LT_64(RSP, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1770:

ra_53 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,ra_53,t1_47,t2_48,t_1,t_13,t_17,t_21,t_25,t_29,t_31,t_37,t_43,t_5,t_9,target_35,target_41;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_12: bv1;
const unconstrained_13: bv1;
const unconstrained_14: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var RDI: bv64;
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
var ra_53: bv64;
var t1_47: bv64;
var t2_48: bv64;
var t_1: bv64;
var t_13: bv32;
var t_17: bv32;
var t_21: bv32;
var t_25: bv32;
var t_29: bv128;
var t_31: bv64;
var t_37: bv64;
var t_43: bv32;
var t_5: bv32;
var t_9: bv32;
var target_35: bv64;
var target_41: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4672bv64);
axiom policy(4720bv64);
axiom policy(4768bv64);
axiom policy(4784bv64);
axiom policy(5072bv64);
axiom policy(5328bv64);
axiom policy(5616bv64);
axiom policy(6016bv64);
axiom policy(6048bv64);
axiom policy(6112bv64);
axiom policy(6512bv64);
axiom policy(6976bv64);
axiom policy(7040bv64);
axiom policy(7088bv64);
axiom policy(7152bv64);
axiom policy(7216bv64);
axiom policy(7280bv64);
axiom policy(7600bv64);
axiom policy(8304bv64);
axiom policy(8400bv64);
axiom policy(8480bv64);
axiom policy(8624bv64);
axiom policy(8832bv64);
axiom policy(8976bv64);
axiom policy(9136bv64);
axiom policy(9152bv64);
axiom policy(9264bv64);
axiom policy(9408bv64);
axiom policy(9552bv64);
axiom policy(10112bv64);
axiom policy(10192bv64);
axiom policy(10352bv64);
axiom policy(10400bv64);
axiom policy(10448bv64);
axiom policy(10528bv64);
axiom policy(10576bv64);
axiom policy(10624bv64);
axiom policy(10672bv64);
axiom policy(10704bv64);
axiom policy(10736bv64);
axiom policy(10784bv64);
axiom policy(10832bv64);
axiom policy(10880bv64);
axiom policy(10912bv64);
axiom policy(10928bv64);
axiom policy(10944bv64);
axiom policy(10960bv64);
axiom policy(10976bv64);
axiom policy(10992bv64);
axiom policy(11008bv64);
axiom policy(11152bv64);
axiom policy(11280bv64);
axiom policy(11424bv64);
