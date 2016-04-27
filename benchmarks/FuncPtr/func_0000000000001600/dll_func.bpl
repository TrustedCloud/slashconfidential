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
axiom _function_addr_low == 5632bv64;
axiom _function_addr_high == 6321bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1600:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1605:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x160c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), 0bv64);

label_0x1615:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 160bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 160bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 160bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 160bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 160bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x161e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1627;
}

label_0x1620:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1622:
goto label_0x18a9;

label_0x1627:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x162f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1634:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1639:
RAX := AND_64(RAX, 4294967295bv32 ++ 4294967288bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x163d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1642:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1647:
origDEST_11 := RAX;
origCOUNT_12 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), CF, LSHIFT_64(origDEST_11, (MINUS_64(64bv64, origCOUNT_12)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv64)), origDEST_11[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), AF, unconstrained_4);

label_0x164b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x1650:
t_17 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), t_17)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_17, (LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))))[1:0]));
SF := t_17[64:63];
ZF := bool2bv(0bv64 == t_17);

label_0x1656:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x166d;
}

label_0x1658:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x165d:
t_21 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_21, 1bv64)), (XOR_64(t_21, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_21)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1660:
RCX := RAX;

label_0x1663:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5736bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1fd0"} true;
call arbitrary_func();

label_0x1668:
t_25 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x166a:
if (bv2bool(ZF)) {
  goto label_0x166d;
}

label_0x166c:
assume false;

label_0x166d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1672:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_7);

label_0x1676:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x167b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1680:
origDEST_35 := RAX;
origCOUNT_36 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_9);

label_0x1684:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(6581bv64, 5771bv64)), 0bv64));

label_0x168b:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64)))[64:0];

label_0x168f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x1694:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1699:
t_41 := MINUS_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32)), (XOR_64((LOAD_LE_64(mem, RAX)), t_41)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_41, (LOAD_LE_64(mem, RAX)))), 4294967295bv32 ++ 4294967295bv32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x169d:
if (bv2bool(ZF)) {
  goto label_0x17c3;
}

label_0x16a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x16a8:
origDEST_45 := RAX;
origCOUNT_46 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), CF, LSHIFT_64(origDEST_45, (MINUS_64(64bv64, origCOUNT_46)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_46 == 1bv64)), origDEST_45[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), AF, unconstrained_11);

label_0x16ac:
RAX := AND_64(RAX, 63bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16b0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x16b4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x16b8:
RCX := 4294967295bv32 ++ 4294967295bv32;

label_0x16bf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RCX);

label_0x16c4:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x16c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x16cc:
origDEST_53 := RAX;
origCOUNT_54 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, RSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_14);

label_0x16cf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x16d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16d9:
RAX := NOT_64(RAX);

label_0x16dc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x16e1:
RCX := LOAD_LE_64(mem, RCX);

label_0x16e4:
RCX := OR_64(RCX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x16e7:
RAX := RCX;

label_0x16ea:
RAX := NOT_64(RAX);

label_0x16ed:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x16f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x16f7:
t_61 := bool2bv(RAX == 0bv64);
RAX := ITE_64(bv2bool(bool2bv((RAX[1:0]) == 1bv1)), 0bv64, ITE_64(bv2bool(bool2bv((RAX[2:1]) == 1bv1)), 1bv64, ITE_64(bv2bool(bool2bv((RAX[3:2]) == 1bv1)), 2bv64, ITE_64(bv2bool(bool2bv((RAX[4:3]) == 1bv1)), 3bv64, ITE_64(bv2bool(bool2bv((RAX[5:4]) == 1bv1)), 4bv64, ITE_64(bv2bool(bool2bv((RAX[6:5]) == 1bv1)), 5bv64, ITE_64(bv2bool(bool2bv((RAX[7:6]) == 1bv1)), 6bv64, ITE_64(bv2bool(bool2bv((RAX[8:7]) == 1bv1)), 7bv64, ITE_64(bv2bool(bool2bv((RAX[9:8]) == 1bv1)), 8bv64, ITE_64(bv2bool(bool2bv((RAX[10:9]) == 1bv1)), 9bv64, ITE_64(bv2bool(bool2bv((RAX[11:10]) == 1bv1)), 10bv64, ITE_64(bv2bool(bool2bv((RAX[12:11]) == 1bv1)), 11bv64, ITE_64(bv2bool(bool2bv((RAX[13:12]) == 1bv1)), 12bv64, ITE_64(bv2bool(bool2bv((RAX[14:13]) == 1bv1)), 13bv64, ITE_64(bv2bool(bool2bv((RAX[15:14]) == 1bv1)), 14bv64, ITE_64(bv2bool(bool2bv((RAX[16:15]) == 1bv1)), 15bv64, ITE_64(bv2bool(bool2bv((RAX[17:16]) == 1bv1)), 16bv64, ITE_64(bv2bool(bool2bv((RAX[18:17]) == 1bv1)), 17bv64, ITE_64(bv2bool(bool2bv((RAX[19:18]) == 1bv1)), 18bv64, ITE_64(bv2bool(bool2bv((RAX[20:19]) == 1bv1)), 19bv64, ITE_64(bv2bool(bool2bv((RAX[21:20]) == 1bv1)), 20bv64, ITE_64(bv2bool(bool2bv((RAX[22:21]) == 1bv1)), 21bv64, ITE_64(bv2bool(bool2bv((RAX[23:22]) == 1bv1)), 22bv64, ITE_64(bv2bool(bool2bv((RAX[24:23]) == 1bv1)), 23bv64, ITE_64(bv2bool(bool2bv((RAX[25:24]) == 1bv1)), 24bv64, ITE_64(bv2bool(bool2bv((RAX[26:25]) == 1bv1)), 25bv64, ITE_64(bv2bool(bool2bv((RAX[27:26]) == 1bv1)), 26bv64, ITE_64(bv2bool(bool2bv((RAX[28:27]) == 1bv1)), 27bv64, ITE_64(bv2bool(bool2bv((RAX[29:28]) == 1bv1)), 28bv64, ITE_64(bv2bool(bool2bv((RAX[30:29]) == 1bv1)), 29bv64, ITE_64(bv2bool(bool2bv((RAX[31:30]) == 1bv1)), 30bv64, ITE_64(bv2bool(bool2bv((RAX[32:31]) == 1bv1)), 31bv64, ITE_64(bv2bool(bool2bv((RAX[33:32]) == 1bv1)), 32bv64, ITE_64(bv2bool(bool2bv((RAX[34:33]) == 1bv1)), 33bv64, ITE_64(bv2bool(bool2bv((RAX[35:34]) == 1bv1)), 34bv64, ITE_64(bv2bool(bool2bv((RAX[36:35]) == 1bv1)), 35bv64, ITE_64(bv2bool(bool2bv((RAX[37:36]) == 1bv1)), 36bv64, ITE_64(bv2bool(bool2bv((RAX[38:37]) == 1bv1)), 37bv64, ITE_64(bv2bool(bool2bv((RAX[39:38]) == 1bv1)), 38bv64, ITE_64(bv2bool(bool2bv((RAX[40:39]) == 1bv1)), 39bv64, ITE_64(bv2bool(bool2bv((RAX[41:40]) == 1bv1)), 40bv64, ITE_64(bv2bool(bool2bv((RAX[42:41]) == 1bv1)), 41bv64, ITE_64(bv2bool(bool2bv((RAX[43:42]) == 1bv1)), 42bv64, ITE_64(bv2bool(bool2bv((RAX[44:43]) == 1bv1)), 43bv64, ITE_64(bv2bool(bool2bv((RAX[45:44]) == 1bv1)), 44bv64, ITE_64(bv2bool(bool2bv((RAX[46:45]) == 1bv1)), 45bv64, ITE_64(bv2bool(bool2bv((RAX[47:46]) == 1bv1)), 46bv64, ITE_64(bv2bool(bool2bv((RAX[48:47]) == 1bv1)), 47bv64, ITE_64(bv2bool(bool2bv((RAX[49:48]) == 1bv1)), 48bv64, ITE_64(bv2bool(bool2bv((RAX[50:49]) == 1bv1)), 49bv64, ITE_64(bv2bool(bool2bv((RAX[51:50]) == 1bv1)), 50bv64, ITE_64(bv2bool(bool2bv((RAX[52:51]) == 1bv1)), 51bv64, ITE_64(bv2bool(bool2bv((RAX[53:52]) == 1bv1)), 52bv64, ITE_64(bv2bool(bool2bv((RAX[54:53]) == 1bv1)), 53bv64, ITE_64(bv2bool(bool2bv((RAX[55:54]) == 1bv1)), 54bv64, ITE_64(bv2bool(bool2bv((RAX[56:55]) == 1bv1)), 55bv64, ITE_64(bv2bool(bool2bv((RAX[57:56]) == 1bv1)), 56bv64, ITE_64(bv2bool(bool2bv((RAX[58:57]) == 1bv1)), 57bv64, ITE_64(bv2bool(bool2bv((RAX[59:58]) == 1bv1)), 58bv64, ITE_64(bv2bool(bool2bv((RAX[60:59]) == 1bv1)), 59bv64, ITE_64(bv2bool(bool2bv((RAX[61:60]) == 1bv1)), 60bv64, ITE_64(bv2bool(bool2bv((RAX[62:61]) == 1bv1)), 61bv64, ITE_64(bv2bool(bool2bv((RAX[63:62]) == 1bv1)), 62bv64, ITE_64(bv2bool(bool2bv((RAX[64:63]) == 1bv1)), 63bv64, unconstrained_16))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
ZF := ITE_1(bv2bool(t_61), 1bv1, 0bv1);
CF := unconstrained_17;
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x16fb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x16ff:
RAX := (RAX[64:8]) ++ ((0bv7 ++ NOT_1(ZF)));

label_0x1702:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1705:
t_63 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x1707:
if (bv2bool(ZF)) {
  goto label_0x177e;
}

label_0x1709:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x170d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x1711:
t_67 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_67, (RAX[32:0])));
OF := AND_32((XOR_32(t_67, (RAX[32:0]))), (XOR_32(t_67, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_67)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1713:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1715:
RAX := (0bv32 ++ RAX[32:0]);

label_0x1717:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x171c:
t_71 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_71)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_71, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x1722:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1729;
}

label_0x1724:
goto label_0x18a4;

label_0x1729:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x172e:
RCX := 4294967295bv32 ++ 4294967295bv32;

label_0x1735:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RCX);

label_0x173a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x173d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1742:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, RSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_24);

label_0x1745:
RAX := NOT_64(RAX);

label_0x1748:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x174d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x1751:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1754:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1759:
origDEST_81 := RAX;
origCOUNT_82 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, RSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_26);

label_0x175c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1761:
R9 := (0bv32 ++ 1bv32);

label_0x1767:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_27;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x176a:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x176f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1774:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6009bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d10"} true;
call arbitrary_func();

label_0x1779:
goto label_0x18a4;

label_0x177e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x1782:
RCX := (0bv32 ++ 64bv32);

label_0x1787:
t_87 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_87, RAX));
OF := AND_64((XOR_64(t_87, RAX)), (XOR_64(t_87, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_87)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x178a:
RAX := RCX;

label_0x178d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1792:
t1_91 := RCX;
t2_92 := RAX;
RCX := PLUS_64(RCX, t2_92);
CF := bool2bv(LT_64(RCX, t1_91));
OF := AND_1((bool2bv((t1_91[64:63]) == (t2_92[64:63]))), (XOR_1((t1_91[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_91)), t2_92)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1795:
RAX := RCX;

label_0x1798:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x179d:
R9 := (0bv32 ++ 1bv32);

label_0x17a3:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_28;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x17a6:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x17ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x17b0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6069bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d10"} true;
call arbitrary_func();

label_0x17b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x17ba:
t1_97 := RAX;
t2_98 := 8bv64;
RAX := PLUS_64(RAX, t2_98);
CF := bool2bv(LT_64(RAX, t1_97));
OF := AND_1((bool2bv((t1_97[64:63]) == (t2_98[64:63]))), (XOR_1((t1_97[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_97)), t2_98)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x17c3:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(6254bv64, 6090bv64)), 0bv64));

label_0x17ca:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(6255bv64, 6097bv64)), 0bv64));

label_0x17d1:
t1_103 := RCX;
t2_104 := RAX;
RCX := PLUS_64(RCX, t2_104);
CF := bool2bv(LT_64(RCX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x17d4:
RAX := RCX;

label_0x17d7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x17dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x17e1:
t_109 := MINUS_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32)), (XOR_64((LOAD_LE_64(mem, RAX)), t_109)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_109, (LOAD_LE_64(mem, RAX)))), 4294967295bv32 ++ 4294967295bv32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))))[1:0]));
SF := t_109[64:63];
ZF := bool2bv(0bv64 == t_109);

label_0x17e5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x181e;
}

label_0x17e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x17ec:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x17f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x17f8:
t1_113 := RAX;
t2_114 := 8bv64;
RAX := PLUS_64(RAX, t2_114);
CF := bool2bv(LT_64(RAX, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17fc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x1801:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1806:
t1_119 := RAX;
t2_120 := 64bv64;
RAX := PLUS_64(RAX, t2_120);
CF := bool2bv(LT_64(RAX, t1_119));
OF := AND_1((bool2bv((t1_119[64:63]) == (t2_120[64:63]))), (XOR_1((t1_119[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_119)), t2_120)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x180a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x180f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1814:
t_125 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_125)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_125, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))))[1:0]));
SF := t_125[64:63];
ZF := bool2bv(0bv64 == t_125);

label_0x1819:
if (bv2bool(CF)) {
  goto label_0x181c;
}

label_0x181b:
assume false;

label_0x181c:
goto label_0x17dc;

label_0x181e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1823:
RAX := LOAD_LE_64(mem, RAX);

label_0x1826:
RAX := NOT_64(RAX);

label_0x1829:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x182e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1833:
t_129 := bool2bv(RAX == 0bv64);
RAX := ITE_64(bv2bool(bool2bv((RAX[1:0]) == 1bv1)), 0bv64, ITE_64(bv2bool(bool2bv((RAX[2:1]) == 1bv1)), 1bv64, ITE_64(bv2bool(bool2bv((RAX[3:2]) == 1bv1)), 2bv64, ITE_64(bv2bool(bool2bv((RAX[4:3]) == 1bv1)), 3bv64, ITE_64(bv2bool(bool2bv((RAX[5:4]) == 1bv1)), 4bv64, ITE_64(bv2bool(bool2bv((RAX[6:5]) == 1bv1)), 5bv64, ITE_64(bv2bool(bool2bv((RAX[7:6]) == 1bv1)), 6bv64, ITE_64(bv2bool(bool2bv((RAX[8:7]) == 1bv1)), 7bv64, ITE_64(bv2bool(bool2bv((RAX[9:8]) == 1bv1)), 8bv64, ITE_64(bv2bool(bool2bv((RAX[10:9]) == 1bv1)), 9bv64, ITE_64(bv2bool(bool2bv((RAX[11:10]) == 1bv1)), 10bv64, ITE_64(bv2bool(bool2bv((RAX[12:11]) == 1bv1)), 11bv64, ITE_64(bv2bool(bool2bv((RAX[13:12]) == 1bv1)), 12bv64, ITE_64(bv2bool(bool2bv((RAX[14:13]) == 1bv1)), 13bv64, ITE_64(bv2bool(bool2bv((RAX[15:14]) == 1bv1)), 14bv64, ITE_64(bv2bool(bool2bv((RAX[16:15]) == 1bv1)), 15bv64, ITE_64(bv2bool(bool2bv((RAX[17:16]) == 1bv1)), 16bv64, ITE_64(bv2bool(bool2bv((RAX[18:17]) == 1bv1)), 17bv64, ITE_64(bv2bool(bool2bv((RAX[19:18]) == 1bv1)), 18bv64, ITE_64(bv2bool(bool2bv((RAX[20:19]) == 1bv1)), 19bv64, ITE_64(bv2bool(bool2bv((RAX[21:20]) == 1bv1)), 20bv64, ITE_64(bv2bool(bool2bv((RAX[22:21]) == 1bv1)), 21bv64, ITE_64(bv2bool(bool2bv((RAX[23:22]) == 1bv1)), 22bv64, ITE_64(bv2bool(bool2bv((RAX[24:23]) == 1bv1)), 23bv64, ITE_64(bv2bool(bool2bv((RAX[25:24]) == 1bv1)), 24bv64, ITE_64(bv2bool(bool2bv((RAX[26:25]) == 1bv1)), 25bv64, ITE_64(bv2bool(bool2bv((RAX[27:26]) == 1bv1)), 26bv64, ITE_64(bv2bool(bool2bv((RAX[28:27]) == 1bv1)), 27bv64, ITE_64(bv2bool(bool2bv((RAX[29:28]) == 1bv1)), 28bv64, ITE_64(bv2bool(bool2bv((RAX[30:29]) == 1bv1)), 29bv64, ITE_64(bv2bool(bool2bv((RAX[31:30]) == 1bv1)), 30bv64, ITE_64(bv2bool(bool2bv((RAX[32:31]) == 1bv1)), 31bv64, ITE_64(bv2bool(bool2bv((RAX[33:32]) == 1bv1)), 32bv64, ITE_64(bv2bool(bool2bv((RAX[34:33]) == 1bv1)), 33bv64, ITE_64(bv2bool(bool2bv((RAX[35:34]) == 1bv1)), 34bv64, ITE_64(bv2bool(bool2bv((RAX[36:35]) == 1bv1)), 35bv64, ITE_64(bv2bool(bool2bv((RAX[37:36]) == 1bv1)), 36bv64, ITE_64(bv2bool(bool2bv((RAX[38:37]) == 1bv1)), 37bv64, ITE_64(bv2bool(bool2bv((RAX[39:38]) == 1bv1)), 38bv64, ITE_64(bv2bool(bool2bv((RAX[40:39]) == 1bv1)), 39bv64, ITE_64(bv2bool(bool2bv((RAX[41:40]) == 1bv1)), 40bv64, ITE_64(bv2bool(bool2bv((RAX[42:41]) == 1bv1)), 41bv64, ITE_64(bv2bool(bool2bv((RAX[43:42]) == 1bv1)), 42bv64, ITE_64(bv2bool(bool2bv((RAX[44:43]) == 1bv1)), 43bv64, ITE_64(bv2bool(bool2bv((RAX[45:44]) == 1bv1)), 44bv64, ITE_64(bv2bool(bool2bv((RAX[46:45]) == 1bv1)), 45bv64, ITE_64(bv2bool(bool2bv((RAX[47:46]) == 1bv1)), 46bv64, ITE_64(bv2bool(bool2bv((RAX[48:47]) == 1bv1)), 47bv64, ITE_64(bv2bool(bool2bv((RAX[49:48]) == 1bv1)), 48bv64, ITE_64(bv2bool(bool2bv((RAX[50:49]) == 1bv1)), 49bv64, ITE_64(bv2bool(bool2bv((RAX[51:50]) == 1bv1)), 50bv64, ITE_64(bv2bool(bool2bv((RAX[52:51]) == 1bv1)), 51bv64, ITE_64(bv2bool(bool2bv((RAX[53:52]) == 1bv1)), 52bv64, ITE_64(bv2bool(bool2bv((RAX[54:53]) == 1bv1)), 53bv64, ITE_64(bv2bool(bool2bv((RAX[55:54]) == 1bv1)), 54bv64, ITE_64(bv2bool(bool2bv((RAX[56:55]) == 1bv1)), 55bv64, ITE_64(bv2bool(bool2bv((RAX[57:56]) == 1bv1)), 56bv64, ITE_64(bv2bool(bool2bv((RAX[58:57]) == 1bv1)), 57bv64, ITE_64(bv2bool(bool2bv((RAX[59:58]) == 1bv1)), 58bv64, ITE_64(bv2bool(bool2bv((RAX[60:59]) == 1bv1)), 59bv64, ITE_64(bv2bool(bool2bv((RAX[61:60]) == 1bv1)), 60bv64, ITE_64(bv2bool(bool2bv((RAX[62:61]) == 1bv1)), 61bv64, ITE_64(bv2bool(bool2bv((RAX[63:62]) == 1bv1)), 62bv64, ITE_64(bv2bool(bool2bv((RAX[64:63]) == 1bv1)), 63bv64, unconstrained_29))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
ZF := ITE_1(bv2bool(t_129), 1bv1, 0bv1);
CF := unconstrained_30;
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x1837:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x183b:
RAX := (RAX[64:8]) ++ ((0bv7 ++ NOT_1(ZF)));

label_0x183e:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1841:
t_131 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)), 2bv32)), (XOR_32((RSHIFT_32(t_131, 4bv32)), t_131)))))[1:0]));
SF := t_131[32:31];
ZF := bool2bv(0bv32 == t_131);

label_0x1843:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1848;
}

label_0x1845:
assume false;

label_0x1846:
goto label_0x18a4;

label_0x1848:
t_135 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_135)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_135, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)), 2bv32)), (XOR_32((RSHIFT_32(t_135, 4bv32)), t_135)))))[1:0]));
SF := t_135[32:31];
ZF := bool2bv(0bv32 == t_135);

label_0x184d:
if (bv2bool(ZF)) {
  goto label_0x18a4;
}

label_0x184f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x1853:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1858:
t1_139 := RCX;
t2_140 := RAX;
RCX := PLUS_64(RCX, t2_140);
CF := bool2bv(LT_64(RCX, t1_139));
OF := AND_1((bool2bv((t1_139[64:63]) == (t2_140[64:63]))), (XOR_1((t1_139[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_139)), t2_140)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x185b:
RAX := RCX;

label_0x185e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1863:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x1867:
RCX := 4294967295bv32 ++ 4294967295bv32;

label_0x186e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RCX);

label_0x1876:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1879:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1881:
origDEST_145 := RAX;
origCOUNT_146 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), CF, RSHIFT_64(origDEST_145, (MINUS_64(64bv64, origCOUNT_146)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_146 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), AF, unconstrained_37);

label_0x1884:
RAX := NOT_64(RAX);

label_0x1887:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x188c:
R9 := (0bv32 ++ 1bv32);

label_0x1892:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_38;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1895:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x189a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x189f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6308bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d10"} true;
call arbitrary_func();

label_0x18a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x18a9:
t1_151 := RSP;
t2_152 := 152bv64;
RSP := PLUS_64(RSP, t2_152);
CF := bool2bv(LT_64(RSP, t1_151));
OF := AND_1((bool2bv((t1_151[64:63]) == (t2_152[64:63]))), (XOR_1((t1_151[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_151)), t2_152)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x18b0:

ra_157 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_12,origCOUNT_146,origCOUNT_30,origCOUNT_36,origCOUNT_46,origCOUNT_54,origCOUNT_76,origCOUNT_82,origDEST_11,origDEST_145,origDEST_29,origDEST_35,origDEST_45,origDEST_53,origDEST_75,origDEST_81,ra_157,t1_103,t1_113,t1_119,t1_139,t1_151,t1_91,t1_97,t2_104,t2_114,t2_120,t2_140,t2_152,t2_92,t2_98,t_1,t_109,t_125,t_129,t_131,t_135,t_17,t_21,t_25,t_41,t_5,t_61,t_63,t_67,t_71,t_87;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_12: bv1;
const unconstrained_13: bv1;
const unconstrained_14: bv1;
const unconstrained_15: bv1;
const unconstrained_16: bv64;
const unconstrained_17: bv64;
const unconstrained_18: bv64;
const unconstrained_19: bv64;
const unconstrained_2: bv1;
const unconstrained_20: bv64;
const unconstrained_21: bv64;
const unconstrained_22: bv1;
const unconstrained_23: bv1;
const unconstrained_24: bv1;
const unconstrained_25: bv1;
const unconstrained_26: bv1;
const unconstrained_27: bv1;
const unconstrained_28: bv1;
const unconstrained_29: bv64;
const unconstrained_3: bv1;
const unconstrained_30: bv64;
const unconstrained_31: bv64;
const unconstrained_32: bv64;
const unconstrained_33: bv64;
const unconstrained_34: bv64;
const unconstrained_35: bv1;
const unconstrained_36: bv1;
const unconstrained_37: bv1;
const unconstrained_38: bv1;
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
var origCOUNT_12: bv64;
var origCOUNT_146: bv64;
var origCOUNT_30: bv64;
var origCOUNT_36: bv64;
var origCOUNT_46: bv64;
var origCOUNT_54: bv64;
var origCOUNT_76: bv64;
var origCOUNT_82: bv64;
var origDEST_11: bv64;
var origDEST_145: bv64;
var origDEST_29: bv64;
var origDEST_35: bv64;
var origDEST_45: bv64;
var origDEST_53: bv64;
var origDEST_75: bv64;
var origDEST_81: bv64;
var ra_157: bv64;
var t1_103: bv64;
var t1_113: bv64;
var t1_119: bv64;
var t1_139: bv64;
var t1_151: bv64;
var t1_91: bv64;
var t1_97: bv64;
var t2_104: bv64;
var t2_114: bv64;
var t2_120: bv64;
var t2_140: bv64;
var t2_152: bv64;
var t2_92: bv64;
var t2_98: bv64;
var t_1: bv64;
var t_109: bv64;
var t_125: bv64;
var t_129: bv1;
var t_131: bv32;
var t_135: bv32;
var t_17: bv64;
var t_21: bv64;
var t_25: bv32;
var t_41: bv64;
var t_5: bv64;
var t_61: bv1;
var t_63: bv32;
var t_67: bv32;
var t_71: bv64;
var t_87: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4160bv64);
axiom policy(4224bv64);
axiom policy(4256bv64);
axiom policy(4416bv64);
axiom policy(4480bv64);
axiom policy(4528bv64);
axiom policy(4544bv64);
axiom policy(5008bv64);
axiom policy(5072bv64);
axiom policy(5120bv64);
axiom policy(5184bv64);
axiom policy(5248bv64);
axiom policy(5312bv64);
axiom policy(5632bv64);
axiom policy(6336bv64);
axiom policy(6432bv64);
axiom policy(6512bv64);
axiom policy(6656bv64);
axiom policy(6864bv64);
axiom policy(7008bv64);
axiom policy(7168bv64);
axiom policy(7184bv64);
axiom policy(7296bv64);
axiom policy(7440bv64);
axiom policy(7584bv64);
axiom policy(8144bv64);
axiom policy(8224bv64);
axiom policy(8384bv64);
axiom policy(8432bv64);
axiom policy(8480bv64);
axiom policy(8560bv64);
axiom policy(8608bv64);
axiom policy(8656bv64);
axiom policy(8704bv64);
axiom policy(8736bv64);
axiom policy(8768bv64);
axiom policy(8816bv64);
axiom policy(8864bv64);
axiom policy(8912bv64);
axiom policy(8944bv64);
axiom policy(8960bv64);
axiom policy(8976bv64);
axiom policy(8992bv64);
axiom policy(9008bv64);
axiom policy(9024bv64);
axiom policy(9040bv64);
axiom policy(9440bv64);
axiom policy(9472bv64);
axiom policy(9536bv64);
axiom policy(9936bv64);
axiom policy(10224bv64);
axiom policy(10480bv64);
axiom policy(10768bv64);
axiom policy(10912bv64);
axiom policy(11040bv64);
axiom policy(11184bv64);
