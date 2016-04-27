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
axiom _function_addr_low == 2400bv64;
axiom _function_addr_high == 2842bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x960:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x965:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0x969:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x96a:
t_3 := RSP;
RSP := MINUS_64(RSP, 160bv64);
CF := bool2bv(LT_64(t_3, 160bv64));
OF := AND_64((XOR_64(t_3, 160bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 160bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x971:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x974:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x97c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x983:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2440bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x988"} true;
call arbitrary_func();

label_0x988:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x98f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x994:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x999:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_3);

label_0x99d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x9a2:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x9a7:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_5);

label_0x9ab:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9af:
RCX := (0bv32 ++ 15bv32);

label_0x9b4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RCX);

label_0x9b9:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x9bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x9c1:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_8);

label_0x9c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x9c9:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x9ce:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x9d2:
R8 := PLUS_64(RSP, 48bv64)[64:0];

label_0x9d7:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x9df:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x9e6:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2539bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x9eb"} true;
call arbitrary_func();

label_0x9eb:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x9f0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2549bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x9f5"} true;
call arbitrary_func();

label_0x9f5:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x9fa:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2559bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x9ff"} true;
call arbitrary_func();

label_0x9ff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 1bv32);

label_0xa07:
goto label_0xa13;

label_0xa09:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xa0d:
t_29 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_29[32:31]) == (1bv32[32:31]))), (XOR_1((t_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_29)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa0f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0xa13:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0xa17:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0xa1b:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0xa7f;
}

label_0xa1d:
t_37 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), t_37)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_37, (LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))))[1:0]));
SF := t_37[32:31];
ZF := bool2bv(0bv32 == t_37);

label_0xa22:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa30;
}

label_0xa24:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 2603bv64)), 0bv64));

label_0xa2b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2608bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa30"} true;
call arbitrary_func();

label_0xa30:
RDX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 2615bv64)), 0bv64));

label_0xa37:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 2622bv64)), 0bv64));

label_0xa3e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2627bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa43"} true;
call arbitrary_func();

label_0xa43:
RDX := PLUS_64((PLUS_64(0bv64, 2634bv64)), 0bv64)[64:0];

label_0xa4a:
RCX := PLUS_64((PLUS_64(0bv64, 2641bv64)), 0bv64)[64:0];

label_0xa51:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2646bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa56"} true;
call arbitrary_func();

label_0xa56:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xa5a:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 63bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa5d:
t_43 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))))[1:0]));
SF := t_43[32:31];
ZF := bool2bv(0bv32 == t_43);

label_0xa5f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xa7d;
}

label_0xa61:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xa65:
RCX := PLUS_64((PLUS_64(0bv64, 2668bv64)), 0bv64)[64:0];

label_0xa6c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2673bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa71"} true;
call arbitrary_func();

label_0xa71:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(0bv64, 2680bv64)), 0bv64));

label_0xa78:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2685bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa7d"} true;
call arbitrary_func();

label_0xa7d:
goto label_0xa09;

label_0xa7f:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0xa84:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2697bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xa89"} true;
call arbitrary_func();

label_0xa89:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xa90:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0xa98:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0xa9d:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_13);

label_0xaa1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xaa9:
t1_53 := RCX;
t2_54 := RAX;
RCX := PLUS_64(RCX, t2_54);
CF := bool2bv(LT_64(RCX, t1_53));
OF := AND_1((bool2bv((t1_53[64:63]) == (t2_54[64:63]))), (XOR_1((t1_53[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_53)), t2_54)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xaac:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RCX);

label_0xab4:
RAX := PLUS_64(RSP, 80bv64)[64:0];

label_0xab9:
origDEST_59 := RAX;
origCOUNT_60 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_15);

label_0xabd:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xac1:
RCX := (RCX[64:8]) ++ 254bv8;

label_0xac3:
mem := STORE_LE_8(mem, PLUS_64(RSP, 144bv64), RCX[32:0][8:0]);

label_0xaca:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xacd:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 144bv64))));

label_0xad5:
origDEST_67 := RAX[32:0][8:0];
origCOUNT_68 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), CF, RSHIFT_8(origDEST_67, (MINUS_8(8bv8, origCOUNT_68)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv8)), AF, unconstrained_18);

label_0xad7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xadf:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0xae1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xae9:
t_75 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_75, 1bv64)), (XOR_64(t_75, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_75)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaec:
RDI := RAX;

label_0xaef:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_20;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xaf1:
RCX := (0bv32 ++ 1bv32);

label_0xaf6:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xaf8:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_21;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xafb:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xb03:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0xb0a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2831bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb0f"} true;
call arbitrary_func();

label_0xb0f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_22;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb11:
t1_79 := RSP;
t2_80 := 160bv64;
RSP := PLUS_64(RSP, t2_80);
CF := bool2bv(LT_64(RSP, t1_79));
OF := AND_1((bool2bv((t1_79[64:63]) == (t2_80[64:63]))), (XOR_1((t1_79[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_79)), t2_80)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xb18:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0xb19:

ra_85 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_14,origCOUNT_22,origCOUNT_48,origCOUNT_60,origCOUNT_68,origCOUNT_8,origDEST_13,origDEST_21,origDEST_47,origDEST_59,origDEST_67,origDEST_7,ra_85,t1_53,t1_79,t2_54,t2_80,t_1,t_29,t_3,t_33,t_37,t_43,t_75;

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
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R8: bv64;
var R9: bv64;
var R10: bv64;
var R11: bv64;
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
var RAX: bv64;
var RBX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_14: bv64;
var origCOUNT_22: bv64;
var origCOUNT_48: bv64;
var origCOUNT_60: bv64;
var origCOUNT_68: bv8;
var origCOUNT_8: bv64;
var origDEST_13: bv64;
var origDEST_21: bv64;
var origDEST_47: bv64;
var origDEST_59: bv64;
var origDEST_67: bv8;
var origDEST_7: bv64;
var ra_85: bv64;
var t1_53: bv64;
var t1_79: bv64;
var t2_54: bv64;
var t2_80: bv64;
var t_1: bv64;
var t_29: bv32;
var t_3: bv64;
var t_33: bv32;
var t_37: bv32;
var t_43: bv32;
var t_75: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1296bv64);
axiom policy(2000bv64);
axiom policy(2208bv64);
axiom policy(2352bv64);
axiom policy(2400bv64);
