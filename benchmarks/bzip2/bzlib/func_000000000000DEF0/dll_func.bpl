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
axiom _function_addr_low == 57072bv64;
axiom _function_addr_high == 58423bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xdef0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0xdef5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0xdefa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0xdefe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xdf03:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0xdf04:
RAX := (0bv32 ++ 5328bv32);

label_0xdf09:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57102bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xdf0e"} true;
call arbitrary_func();

label_0xdf0e:
t_3 := RSP;
RSP := MINUS_64(RSP, RAX);
CF := bool2bv(LT_64(t_3, RAX));
OF := AND_64((XOR_64(t_3, RAX)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xdf11:
RDX := (0bv32 ++ 5000bv32);

label_0xdf16:
RCX := PLUS_64(RSP, 112bv64)[64:0];

label_0xdf1b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57120bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xdf20"} true;
call arbitrary_func();

label_0xdf20:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xdf27:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5184bv64), RAX);

label_0xdf2f:
RAX := PLUS_64(RSP, 64bv64)[64:0];

label_0xdf34:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0xdf38:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5192bv64), RAX);

label_0xdf40:
RAX := PLUS_64(RSP, 64bv64)[64:0];

label_0xdf45:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0xdf49:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdf4d:
RCX := (0bv32 ++ 13bv32);

label_0xdf52:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5200bv64), RCX);

label_0xdf5a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xdf5d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5200bv64));

label_0xdf65:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0xdf68:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5184bv64));

label_0xdf70:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 5192bv64));

label_0xdf78:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0xdf7c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5360bv64));

label_0xdf84:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5176bv64), RAX);

label_0xdf8c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5136bv64), 9bv32);

label_0xdf97:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5140bv64), 0bv32);

label_0xdfa2:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64((PLUS_64(0bv64, 57257bv64)), 0bv64))));

label_0xdfa9:
mem := STORE_LE_8(mem, PLUS_64(RSP, 80bv64), RAX[32:0][8:0]);

label_0xdfad:
RAX := PLUS_64(RSP, 81bv64)[64:0];

label_0xdfb2:
RDI := RAX;

label_0xdfb5:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_9;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xdfb7:
RCX := (0bv32 ++ 9bv32);

label_0xdfbc:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xdfbe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5144bv64), 0bv32);

label_0xdfc9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5152bv64), 0bv64);

label_0xdfd5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5160bv64), 0bv32);

label_0xdfe0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5164bv64), 30bv32);

label_0xdfeb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5168bv64), 0bv32);

label_0xdff6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5172bv64), 0bv32);

label_0xe001:
t_29 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64))), t_29)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_29, (LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0xe00a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe089;
}

label_0xe00c:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xe013:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5208bv64), RAX);

label_0xe01b:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe023:
origDEST_33 := RAX;
origCOUNT_34 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, LSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), origDEST_33[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_11);

label_0xe027:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5208bv64));

label_0xe02f:
t1_39 := RCX;
t2_40 := RAX;
RCX := PLUS_64(RCX, t2_40);
CF := bool2bv(LT_64(RCX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe032:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5216bv64), RCX);

label_0xe03a:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe042:
origDEST_45 := RAX;
origCOUNT_46 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), CF, LSHIFT_64(origDEST_45, (MINUS_64(64bv64, origCOUNT_46)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_46 == 1bv64)), origDEST_45[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), AF, unconstrained_13);

label_0xe046:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe04a:
RCX := (RCX[64:8]) ++ 254bv8;

label_0xe04c:
mem := STORE_LE_8(mem, PLUS_64(RSP, 5224bv64), RCX[32:0][8:0]);

label_0xe053:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe056:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 5224bv64))));

label_0xe05e:
origDEST_53 := RAX[32:0][8:0];
origCOUNT_54 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), CF, RSHIFT_8(origDEST_53, (MINUS_8(8bv8, origCOUNT_54)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv8)), AF, unconstrained_16);

label_0xe060:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5216bv64));

label_0xe068:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0xe06a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5216bv64));

label_0xe072:
t_61 := RAX;
RAX := MINUS_64(RAX, 80bv64);
CF := bool2bv(LT_64(t_61, 80bv64));
OF := AND_64((XOR_64(t_61, 80bv64)), (XOR_64(t_61, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_61)), 80bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe076:
RDI := RAX;

label_0xe079:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_18;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe07b:
RCX := (0bv32 ++ 80bv32);

label_0xe080:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xe082:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_19;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe084:
goto label_0xe42e;

label_0xe089:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64));

label_0xe091:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_8(mem, RAX)[8:7]) ,(1bv24 ++ LOAD_LE_8(mem, RAX)) ,(0bv24 ++ LOAD_LE_8(mem, RAX)))));

label_0xe094:
t_65 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))))[1:0]));
SF := t_65[32:31];
ZF := bool2bv(0bv32 == t_65);

label_0xe096:
if (bv2bool(ZF)) {
  goto label_0xe138;
}

label_0xe09c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64));

label_0xe0a4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RAX)));

label_0xe0a7:
mem := STORE_LE_8(mem, PLUS_64(RSP, 5228bv64), RAX[32:0][8:0]);

label_0xe0ae:
t_69 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 114bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 114bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 114bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), t_69)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_69, (LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))))), 114bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)), 2bv8)), (XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)), 2bv8)), (XOR_8((RSHIFT_8(t_69, 4bv8)), t_69)))))[1:0]));
SF := t_69[8:7];
ZF := bool2bv(0bv8 == t_69);

label_0xe0b6:
if (bv2bool(ZF)) {
  goto label_0xe0ce;
}

label_0xe0b8:
t_73 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 115bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 115bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 115bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), t_73)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_73, (LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))))), 115bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_73, 4bv8)), t_73)), 2bv8)), (XOR_8((RSHIFT_8(t_73, 4bv8)), t_73)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_73, 4bv8)), t_73)), 2bv8)), (XOR_8((RSHIFT_8(t_73, 4bv8)), t_73)))))[1:0]));
SF := t_73[8:7];
ZF := bool2bv(0bv8 == t_73);

label_0xe0c0:
if (bv2bool(ZF)) {
  goto label_0xe0e8;
}

label_0xe0c2:
t_77 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 119bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 119bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), 119bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))), t_77)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_77, (LOAD_LE_8(mem, PLUS_64(RSP, 5228bv64))))), 119bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_77, 4bv8)), t_77)), 2bv8)), (XOR_8((RSHIFT_8(t_77, 4bv8)), t_77)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_77, 4bv8)), t_77)), 2bv8)), (XOR_8((RSHIFT_8(t_77, 4bv8)), t_77)))))[1:0]));
SF := t_77[8:7];
ZF := bool2bv(0bv8 == t_77);

label_0xe0ca:
if (bv2bool(ZF)) {
  goto label_0xe0db;
}

label_0xe0cc:
goto label_0xe0f5;

label_0xe0ce:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5140bv64), 0bv32);

label_0xe0d9:
goto label_0xe120;

label_0xe0db:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5140bv64), 1bv32);

label_0xe0e6:
goto label_0xe120;

label_0xe0e8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5168bv64), 1bv32);

label_0xe0f3:
goto label_0xe120;

label_0xe0f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64));

label_0xe0fd:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_8(mem, RAX)[8:7]) ,(1bv24 ++ LOAD_LE_8(mem, RAX)) ,(0bv24 ++ LOAD_LE_8(mem, RAX)))));

label_0xe100:
RCX := (0bv32 ++ RAX[32:0]);

label_0xe102:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57607bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe107"} true;
call arbitrary_func();

label_0xe107:
t_81 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))))[1:0]));
SF := t_81[32:31];
ZF := bool2bv(0bv32 == t_81);

label_0xe109:
if (bv2bool(ZF)) {
  goto label_0xe120;
}

label_0xe10b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64));

label_0xe113:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_8(mem, RAX)[8:7]) ,(1bv24 ++ LOAD_LE_8(mem, RAX)) ,(0bv24 ++ LOAD_LE_8(mem, RAX)))));

label_0xe116:
t_85 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 48bv32));
CF := bool2bv(LT_32(t_85, 48bv32));
OF := AND_32((XOR_32(t_85, 48bv32)), (XOR_32(t_85, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_85)), 48bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xe119:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5136bv64), RAX[32:0]);

label_0xe120:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5176bv64));

label_0xe128:
t_89 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_89[64:63]) == (1bv64[64:63]))), (XOR_1((t_89[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_89)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe12b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5176bv64), RAX);

label_0xe133:
goto label_0xe089;

label_0xe138:
t_93 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), t_93)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_93, (LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))))[1:0]));
SF := t_93[32:31];
ZF := bool2bv(0bv32 == t_93);

label_0xe140:
if (bv2bool(ZF)) {
  goto label_0xe153;
}

label_0xe142:
RAX := PLUS_64((PLUS_64(0bv64, 57673bv64)), 0bv64)[64:0];

label_0xe149:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5232bv64), RAX);

label_0xe151:
goto label_0xe162;

label_0xe153:
RAX := PLUS_64((PLUS_64(0bv64, 57690bv64)), 0bv64)[64:0];

label_0xe15a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5232bv64), RAX);

label_0xe162:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 5232bv64));

label_0xe16a:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xe16f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57716bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe174"} true;
call arbitrary_func();

label_0xe174:
RDX := PLUS_64((PLUS_64(0bv64, 57723bv64)), 0bv64)[64:0];

label_0xe17b:
RCX := PLUS_64(RSP, 80bv64)[64:0];

label_0xe180:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57733bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe185"} true;
call arbitrary_func();

label_0xe185:
t_97 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5368bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5368bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5368bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5368bv64))), t_97)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_97, (LOAD_LE_32(mem, PLUS_64(RSP, 5368bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))))[1:0]));
SF := t_97[32:31];
ZF := bool2bv(0bv32 == t_97);

label_0xe18d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe1f1;
}

label_0xe18f:
t_101 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64))), t_101)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_101, (LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0xe198:
if (bv2bool(ZF)) {
  goto label_0xe1b2;
}

label_0xe19a:
RDX := PLUS_64((PLUS_64(0bv64, 57761bv64)), 0bv64)[64:0];

label_0xe1a1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5344bv64));

label_0xe1a9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 57774bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe1ae"} true;
call arbitrary_func();

label_0xe1ae:
t_105 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))))[1:0]));
SF := t_105[32:31];
ZF := bool2bv(0bv32 == t_105);

label_0xe1b0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe1e4;
}

label_0xe1b2:
t_109 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), t_109)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_109, (LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))))[1:0]));
SF := t_109[32:31];
ZF := bool2bv(0bv32 == t_109);

label_0xe1ba:
if (bv2bool(ZF)) {
  goto label_0xe1c9;
}

label_0xe1bc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5240bv64), 1bv32);

label_0xe1c7:
goto label_0xe1d4;

label_0xe1c9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5240bv64), 0bv32);

label_0xe1d4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5240bv64)));

label_0xe1db:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5144bv64), RAX[32:0]);

label_0xe1e2:
goto label_0xe1ef;

label_0xe1e4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5144bv64), 0bv32);

label_0xe1ef:
goto label_0xe1fc;

label_0xe1f1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5144bv64), 0bv32);

label_0xe1fc:
t_113 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64))), t_113)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_113, (LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))))[1:0]));
SF := t_113[32:31];
ZF := bool2bv(0bv32 == t_113);

label_0xe204:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe283;
}

label_0xe206:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xe20d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5248bv64), RAX);

label_0xe215:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe21d:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_24);

label_0xe221:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5248bv64));

label_0xe229:
t1_123 := RCX;
t2_124 := RAX;
RCX := PLUS_64(RCX, t2_124);
CF := bool2bv(LT_64(RCX, t1_123));
OF := AND_1((bool2bv((t1_123[64:63]) == (t2_124[64:63]))), (XOR_1((t1_123[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_123)), t2_124)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe22c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5256bv64), RCX);

label_0xe234:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe23c:
origDEST_129 := RAX;
origCOUNT_130 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), CF, LSHIFT_64(origDEST_129, (MINUS_64(64bv64, origCOUNT_130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_130 == 1bv64)), origDEST_129[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), AF, unconstrained_26);

label_0xe240:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe244:
RCX := (RCX[64:8]) ++ 254bv8;

label_0xe246:
mem := STORE_LE_8(mem, PLUS_64(RSP, 5264bv64), RCX[32:0][8:0]);

label_0xe24d:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe250:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 5264bv64))));

label_0xe258:
origDEST_137 := RAX[32:0][8:0];
origCOUNT_138 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), CF, RSHIFT_8(origDEST_137, (MINUS_8(8bv8, origCOUNT_138)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv8)), AF, unconstrained_29);

label_0xe25a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5256bv64));

label_0xe262:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_30;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0xe264:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5256bv64));

label_0xe26c:
t_145 := RAX;
RAX := MINUS_64(RAX, 80bv64);
CF := bool2bv(LT_64(t_145, 80bv64));
OF := AND_64((XOR_64(t_145, 80bv64)), (XOR_64(t_145, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_145)), 80bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe270:
RDI := RAX;

label_0xe273:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_31;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe275:
RCX := (0bv32 ++ 80bv32);

label_0xe27a:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xe27c:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_32;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe27e:
goto label_0xe42e;

label_0xe283:
t_149 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))), t_149)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_149, (LOAD_LE_32(mem, PLUS_64(RSP, 5140bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))))[1:0]));
SF := t_149[32:31];
ZF := bool2bv(0bv32 == t_149);

label_0xe28b:
if (bv2bool(ZF)) {
  goto label_0xe2ed;
}

label_0xe28d:
t_153 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), t_153)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_153, (LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))))[1:0]));
SF := t_153[32:31];
ZF := bool2bv(0bv32 == t_153);

label_0xe295:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xe2a2;
}

label_0xe297:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5136bv64), 1bv32);

label_0xe2a2:
t_157 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 9bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 9bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), 9bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))), t_157)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_157, (LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64))))), 9bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)), 2bv32)), (XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)), 2bv32)), (XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)))))[1:0]));
SF := t_157[32:31];
ZF := bool2bv(0bv32 == t_157);

label_0xe2aa:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xe2b7;
}

label_0xe2ac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 5136bv64), 9bv32);

label_0xe2b7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5164bv64)));

label_0xe2be:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xe2c2:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5160bv64)));

label_0xe2ca:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5136bv64)));

label_0xe2d2:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64)));

label_0xe2d9:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xe2de:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 58083bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe2e3"} true;
call arbitrary_func();

label_0xe2e3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5152bv64), RAX);

label_0xe2eb:
goto label_0xe32b;

label_0xe2ed:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5172bv64)));

label_0xe2f4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0xe2f8:
RAX := PLUS_64(RSP, 112bv64)[64:0];

label_0xe2fd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0xe302:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5168bv64)));

label_0xe30a:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5160bv64)));

label_0xe312:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 5144bv64)));

label_0xe319:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0xe31e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 58147bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe323"} true;
call arbitrary_func();

label_0xe323:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5152bv64), RAX);

label_0xe32b:
t_161 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64))), t_161)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_161, (LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_161, 4bv64)), t_161)), 2bv64)), (XOR_64((RSHIFT_64(t_161, 4bv64)), t_161)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_161, 4bv64)), t_161)), 2bv64)), (XOR_64((RSHIFT_64(t_161, 4bv64)), t_161)))))[1:0]));
SF := t_161[64:63];
ZF := bool2bv(0bv64 == t_161);

label_0xe334:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe3b0;
}

label_0xe336:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xe33d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5272bv64), RAX);

label_0xe345:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe34d:
origDEST_165 := RAX;
origCOUNT_166 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_34);

label_0xe351:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5272bv64));

label_0xe359:
t1_171 := RCX;
t2_172 := RAX;
RCX := PLUS_64(RCX, t2_172);
CF := bool2bv(LT_64(RCX, t1_171));
OF := AND_1((bool2bv((t1_171[64:63]) == (t2_172[64:63]))), (XOR_1((t1_171[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_171)), t2_172)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe35c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5280bv64), RCX);

label_0xe364:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe36c:
origDEST_177 := RAX;
origCOUNT_178 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), CF, LSHIFT_64(origDEST_177, (MINUS_64(64bv64, origCOUNT_178)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_178 == 1bv64)), origDEST_177[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), AF, unconstrained_36);

label_0xe370:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe374:
RCX := (RCX[64:8]) ++ 254bv8;

label_0xe376:
mem := STORE_LE_8(mem, PLUS_64(RSP, 5288bv64), RCX[32:0][8:0]);

label_0xe37d:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe380:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 5288bv64))));

label_0xe388:
origDEST_185 := RAX[32:0][8:0];
origCOUNT_186 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), CF, RSHIFT_8(origDEST_185, (MINUS_8(8bv8, origCOUNT_186)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_38));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv8)), AF, unconstrained_39);

label_0xe38a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5280bv64));

label_0xe392:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_40;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0xe394:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5280bv64));

label_0xe39c:
t_193 := RAX;
RAX := MINUS_64(RAX, 80bv64);
CF := bool2bv(LT_64(t_193, 80bv64));
OF := AND_64((XOR_64(t_193, 80bv64)), (XOR_64(t_193, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_193)), 80bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe3a0:
RDI := RAX;

label_0xe3a3:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_41;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe3a5:
RCX := (0bv32 ++ 80bv32);

label_0xe3aa:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xe3ac:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe3ae:
goto label_0xe42e;

label_0xe3b0:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0xe3b7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5296bv64), RAX);

label_0xe3bf:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe3c7:
origDEST_197 := RAX;
origCOUNT_198 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), CF, LSHIFT_64(origDEST_197, (MINUS_64(64bv64, origCOUNT_198)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_198 == 1bv64)), origDEST_197[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), AF, unconstrained_44);

label_0xe3cb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5296bv64));

label_0xe3d3:
t1_203 := RCX;
t2_204 := RAX;
RCX := PLUS_64(RCX, t2_204);
CF := bool2bv(LT_64(RCX, t1_203));
OF := AND_1((bool2bv((t1_203[64:63]) == (t2_204[64:63]))), (XOR_1((t1_203[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_203)), t2_204)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe3d6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 5304bv64), RCX);

label_0xe3de:
RAX := PLUS_64(RSP, 5120bv64)[64:0];

label_0xe3e6:
origDEST_209 := RAX;
origCOUNT_210 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_46);

label_0xe3ea:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe3ee:
RCX := (RCX[64:8]) ++ 254bv8;

label_0xe3f0:
mem := STORE_LE_8(mem, PLUS_64(RSP, 5312bv64), RCX[32:0][8:0]);

label_0xe3f7:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe3fa:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 5312bv64))));

label_0xe402:
origDEST_217 := RAX[32:0][8:0];
origCOUNT_218 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), CF, RSHIFT_8(origDEST_217, (MINUS_8(8bv8, origCOUNT_218)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv8)), AF, unconstrained_49);

label_0xe404:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 5304bv64));

label_0xe40c:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_50;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0xe40e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5304bv64));

label_0xe416:
t_225 := RAX;
RAX := MINUS_64(RAX, 80bv64);
CF := bool2bv(LT_64(t_225, 80bv64));
OF := AND_64((XOR_64(t_225, 80bv64)), (XOR_64(t_225, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_225)), 80bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe41a:
RDI := RAX;

label_0xe41d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_51;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xe41f:
RCX := (0bv32 ++ 80bv32);

label_0xe424:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0xe426:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 5152bv64));

label_0xe42e:
t1_229 := RSP;
t2_230 := 5328bv64;
RSP := PLUS_64(RSP, t2_230);
CF := bool2bv(LT_64(RSP, t1_229));
OF := AND_1((bool2bv((t1_229[64:63]) == (t2_230[64:63]))), (XOR_1((t1_229[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_229)), t2_230)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xe435:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0xe436:

ra_235 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_118,origCOUNT_130,origCOUNT_138,origCOUNT_14,origCOUNT_166,origCOUNT_178,origCOUNT_186,origCOUNT_198,origCOUNT_210,origCOUNT_218,origCOUNT_22,origCOUNT_34,origCOUNT_46,origCOUNT_54,origCOUNT_8,origDEST_117,origDEST_129,origDEST_13,origDEST_137,origDEST_165,origDEST_177,origDEST_185,origDEST_197,origDEST_209,origDEST_21,origDEST_217,origDEST_33,origDEST_45,origDEST_53,origDEST_7,ra_235,t1_123,t1_171,t1_203,t1_229,t1_39,t2_124,t2_172,t2_204,t2_230,t2_40,t_1,t_101,t_105,t_109,t_113,t_145,t_149,t_153,t_157,t_161,t_193,t_225,t_29,t_3,t_61,t_65,t_69,t_73,t_77,t_81,t_85,t_89,t_93,t_97;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_118: bv64;
var origCOUNT_130: bv64;
var origCOUNT_138: bv8;
var origCOUNT_14: bv64;
var origCOUNT_166: bv64;
var origCOUNT_178: bv64;
var origCOUNT_186: bv8;
var origCOUNT_198: bv64;
var origCOUNT_210: bv64;
var origCOUNT_218: bv8;
var origCOUNT_22: bv64;
var origCOUNT_34: bv64;
var origCOUNT_46: bv64;
var origCOUNT_54: bv8;
var origCOUNT_8: bv64;
var origDEST_117: bv64;
var origDEST_129: bv64;
var origDEST_13: bv64;
var origDEST_137: bv8;
var origDEST_165: bv64;
var origDEST_177: bv64;
var origDEST_185: bv8;
var origDEST_197: bv64;
var origDEST_209: bv64;
var origDEST_21: bv64;
var origDEST_217: bv8;
var origDEST_33: bv64;
var origDEST_45: bv64;
var origDEST_53: bv8;
var origDEST_7: bv64;
var ra_235: bv64;
var t1_123: bv64;
var t1_171: bv64;
var t1_203: bv64;
var t1_229: bv64;
var t1_39: bv64;
var t2_124: bv64;
var t2_172: bv64;
var t2_204: bv64;
var t2_230: bv64;
var t2_40: bv64;
var t_1: bv64;
var t_101: bv64;
var t_105: bv32;
var t_109: bv32;
var t_113: bv32;
var t_145: bv64;
var t_149: bv32;
var t_153: bv32;
var t_157: bv32;
var t_161: bv64;
var t_193: bv64;
var t_225: bv64;
var t_29: bv64;
var t_3: bv64;
var t_61: bv64;
var t_65: bv32;
var t_69: bv8;
var t_73: bv8;
var t_77: bv8;
var t_81: bv32;
var t_85: bv32;
var t_89: bv64;
var t_93: bv32;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3456bv64);
axiom policy(4592bv64);
axiom policy(5008bv64);
axiom policy(6912bv64);
axiom policy(7904bv64);
axiom policy(8336bv64);
axiom policy(11024bv64);
axiom policy(11664bv64);
axiom policy(12624bv64);
axiom policy(15504bv64);
axiom policy(17728bv64);
axiom policy(19952bv64);
axiom policy(20048bv64);
axiom policy(22784bv64);
axiom policy(24016bv64);
axiom policy(25328bv64);
axiom policy(25344bv64);
axiom policy(25392bv64);
axiom policy(25440bv64);
axiom policy(25968bv64);
axiom policy(26352bv64);
axiom policy(26368bv64);
axiom policy(26736bv64);
axiom policy(26880bv64);
axiom policy(26992bv64);
axiom policy(27104bv64);
axiom policy(27152bv64);
axiom policy(27216bv64);
axiom policy(27264bv64);
axiom policy(27840bv64);
axiom policy(28032bv64);
axiom policy(28080bv64);
axiom policy(31088bv64);
axiom policy(31152bv64);
axiom policy(34640bv64);
axiom policy(35376bv64);
axiom policy(36064bv64);
axiom policy(45632bv64);
axiom policy(57008bv64);
axiom policy(57072bv64);
