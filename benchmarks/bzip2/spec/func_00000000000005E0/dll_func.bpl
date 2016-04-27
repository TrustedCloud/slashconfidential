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
axiom _function_addr_low == 1504bv64;
axiom _function_addr_high == 2576bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x5e0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x5e5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x5ea:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0x5ee:
t_1 := RSP;
RSP := MINUS_64(RSP, 120bv64);
CF := bool2bv(LT_64(t_1, 120bv64));
OF := AND_64((XOR_64(t_1, 120bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 120bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x5f2:
RDX := (0bv32 ++ 32768bv32);

label_0x5f7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x5ff:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1540bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x604"} true;
call arbitrary_func();

label_0x604:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x608:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x60d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x650;
}

label_0x60f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1556bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x614"} true;
call arbitrary_func();

label_0x614:
RCX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x616:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1563bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x61b"} true;
call arbitrary_func();

label_0x61b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x620:
RCX := (0bv32 ++ 2bv32);

label_0x625:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1578bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x62a"} true;
call arbitrary_func();

label_0x62a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x62f:
R9 := RCX;

label_0x632:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x63a:
RDX := PLUS_64((PLUS_64(0bv64, 1601bv64)), 0bv64)[64:0];

label_0x641:
RCX := RAX;

label_0x644:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1609bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x649"} true;
call arbitrary_func();

label_0x649:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x64b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1616bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x650"} true;
call arbitrary_func();

label_0x650:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x658:
t_9 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_9[64:0];
OF := bool2bv(t_9 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_9 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_2;
SF := unconstrained_3;
ZF := unconstrained_4;
AF := unconstrained_5;

label_0x65c:
RCX := PLUS_64((PLUS_64(0bv64, 1635bv64)), 0bv64)[64:0];

label_0x663:
t1_11 := RCX;
t2_12 := RAX;
RCX := PLUS_64(RCX, t2_12);
CF := bool2bv(LT_64(RCX, t1_11));
OF := AND_1((bool2bv((t1_11[64:63]) == (t2_12[64:63]))), (XOR_1((t1_11[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_11)), t2_12)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x666:
RAX := RCX;

label_0x669:
t1_17 := RAX;
t2_18 := 4bv64;
RAX := PLUS_64(RAX, t2_18);
CF := bool2bv(LT_64(RAX, t1_17));
OF := AND_1((bool2bv((t1_17[64:63]) == (t2_18[64:63]))), (XOR_1((t1_17[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_17)), t2_18)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x66d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x672:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x677:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x67d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x682:
t_25 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))))[1:0]));
SF := t_25[64:63];
ZF := bool2bv(0bv64 == t_25);

label_0x685:
if (bv2bool(ZF)) {
  goto label_0x688;
}

label_0x687:
assume false;

label_0x688:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x68d:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_9);

label_0x691:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x698:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x69c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x6a1:
origDEST_35 := RCX;
origCOUNT_36 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), CF, LSHIFT_64(origDEST_35, (MINUS_64(64bv64, origCOUNT_36)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_36 == 1bv64)), origDEST_35[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_36 == 0bv64)), AF, unconstrained_11);

label_0x6a5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_12;
SF := unconstrained_13;
AF := unconstrained_14;
PF := unconstrained_15;

label_0x6a9:
if (bv2bool(CF)) {
  goto label_0x6ac;
}

label_0x6ab:
assume false;

label_0x6ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x6b1:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x6b7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x6bf:
t_41 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_41[64:0];
OF := bool2bv(t_41 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_41 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_16;
SF := unconstrained_17;
ZF := unconstrained_18;
AF := unconstrained_19;

label_0x6c3:
RCX := PLUS_64((PLUS_64(0bv64, 1738bv64)), 0bv64)[64:0];

label_0x6ca:
t1_43 := RCX;
t2_44 := RAX;
RCX := PLUS_64(RCX, t2_44);
CF := bool2bv(LT_64(RCX, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6cd:
RAX := RCX;

label_0x6d0:
t1_49 := RAX;
t2_50 := 8bv64;
RAX := PLUS_64(RAX, t2_50);
CF := bool2bv(LT_64(RAX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6d4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x6d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x6de:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6e9:
t_57 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0x6ec:
if (bv2bool(ZF)) {
  goto label_0x6ef;
}

label_0x6ee:
assume false;

label_0x6ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x6f4:
origDEST_61 := RAX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_23);

label_0x6f8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6ff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x703:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x708:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_25);

label_0x70c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_26;
SF := unconstrained_27;
AF := unconstrained_28;
PF := unconstrained_29;

label_0x710:
if (bv2bool(CF)) {
  goto label_0x713;
}

label_0x712:
assume false;

label_0x713:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x718:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x71e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x726:
goto label_0x738;

label_0x728:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x72c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x730:
t1_73 := RCX[32:0];
t2_74 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_74));
CF := bool2bv(LT_32((RCX[32:0]), t1_73));
OF := AND_1((bool2bv((t1_73[32:31]) == (t2_74[32:31]))), (XOR_1((t1_73[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_73)), t2_74)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x732:
RAX := (0bv32 ++ RCX[32:0]);

label_0x734:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x738:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x73f:
t_79 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_79)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_79, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))))[1:0]));
SF := t_79[32:31];
ZF := bool2bv(0bv32 == t_79);

label_0x743:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x860;
}

label_0x749:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x751:
t_83 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_83[64:0];
OF := bool2bv(t_83 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_83 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_30;
SF := unconstrained_31;
ZF := unconstrained_32;
AF := unconstrained_33;

label_0x755:
RCX := PLUS_64((PLUS_64(0bv64, 1884bv64)), 0bv64)[64:0];

label_0x75c:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));

label_0x761:
t1_85 := RDX;
t2_86 := LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64));
RDX := PLUS_64(RDX, t2_86);
CF := bool2bv(LT_64(RDX, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x766:
RAX := RDX;

label_0x769:
R8 := (0bv32 ++ 131072bv32);

label_0x76f:
RDX := RAX;

label_0x772:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x776:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1915bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x77b"} true;
call arbitrary_func();

label_0x77b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x77f:
t_91 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_91)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_91, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))))[1:0]));
SF := t_91[32:31];
ZF := bool2bv(0bv32 == t_91);

label_0x784:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x78b;
}

label_0x786:
goto label_0x860;

label_0x78b:
t_95 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_95)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_95, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))))[1:0]));
SF := t_95[32:31];
ZF := bool2bv(0bv32 == t_95);

label_0x790:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x7d3;
}

label_0x792:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1943bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x797"} true;
call arbitrary_func();

label_0x797:
RCX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x799:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1950bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x79e"} true;
call arbitrary_func();

label_0x79e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x7a3:
RCX := (0bv32 ++ 2bv32);

label_0x7a8:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1965bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7ad"} true;
call arbitrary_func();

label_0x7ad:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7b2:
R9 := RCX;

label_0x7b5:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x7bd:
RDX := PLUS_64((PLUS_64(0bv64, 1988bv64)), 0bv64)[64:0];

label_0x7c4:
RCX := RAX;

label_0x7c7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1996bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7cc"} true;
call arbitrary_func();

label_0x7cc:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_34;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x7ce:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2003bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7d3"} true;
call arbitrary_func();

label_0x7d3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x7db:
t_99 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_99[64:0];
OF := bool2bv(t_99 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_99 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_35;
SF := unconstrained_36;
ZF := unconstrained_37;
AF := unconstrained_38;

label_0x7df:
RCX := PLUS_64((PLUS_64(0bv64, 2022bv64)), 0bv64)[64:0];

label_0x7e6:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x7ea:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x7ee:
t1_101 := RAX[32:0];
t2_102 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_102));
CF := bool2bv(LT_32((RAX[32:0]), t1_101));
OF := AND_1((bool2bv((t1_101[32:31]) == (t2_102[32:31]))), (XOR_1((t1_101[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_101)), t2_102)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7f0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x7f4:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x7fc:
t_107 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_107[64:0];
OF := bool2bv(t_107 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_107 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_39;
SF := unconstrained_40;
ZF := unconstrained_41;
AF := unconstrained_42;

label_0x800:
RCX := PLUS_64((PLUS_64(0bv64, 2055bv64)), 0bv64)[64:0];

label_0x807:
t1_109 := RCX;
t2_110 := RAX;
RCX := PLUS_64(RCX, t2_110);
CF := bool2bv(LT_64(RCX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x80a:
RAX := RCX;

label_0x80d:
t1_115 := RAX;
t2_116 := 4bv64;
RAX := PLUS_64(RAX, t2_116);
CF := bool2bv(LT_64(RAX, t1_115));
OF := AND_1((bool2bv((t1_115[64:63]) == (t2_116[64:63]))), (XOR_1((t1_115[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_115)), t2_116)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x811:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x816:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x81b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x821:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x826:
t_123 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))))[1:0]));
SF := t_123[64:63];
ZF := bool2bv(0bv64 == t_123);

label_0x829:
if (bv2bool(ZF)) {
  goto label_0x82c;
}

label_0x82b:
assume false;

label_0x82c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x831:
origDEST_127 := RAX;
origCOUNT_128 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_46);

label_0x835:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x83c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x840:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x845:
origDEST_133 := RCX;
origCOUNT_134 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_48);

label_0x849:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x84d:
if (bv2bool(CF)) {
  goto label_0x850;
}

label_0x84f:
assume false;

label_0x850:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x855:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0x859:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x85b:
goto label_0x728;

label_0x860:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x864:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2153bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x869"} true;
call arbitrary_func();

label_0x869:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x871:
t_139 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_139[64:0];
OF := bool2bv(t_139 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_139 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_53;
SF := unconstrained_54;
ZF := unconstrained_55;
AF := unconstrained_56;

label_0x875:
RCX := PLUS_64((PLUS_64(0bv64, 2172bv64)), 0bv64)[64:0];

label_0x87c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x883:
t_141 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64))), (RDX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64))), (RDX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64))), (RDX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64))), t_141)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_141, (LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64))))), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))))[1:0]));
SF := t_141[32:31];
ZF := bool2bv(0bv32 == t_141);

label_0x887:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x9f6;
}

label_0x88d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x895:
t_145 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_145[64:0];
OF := bool2bv(t_145 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_145 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_57;
SF := unconstrained_58;
ZF := unconstrained_59;
AF := unconstrained_60;

label_0x899:
RCX := PLUS_64((PLUS_64(0bv64, 2208bv64)), 0bv64)[64:0];

label_0x8a0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x8a4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x8ab:
t_147 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_147, (RAX[32:0])));
OF := AND_32((XOR_32(t_147, (RAX[32:0]))), (XOR_32(t_147, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_147)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x8ad:
RAX := (0bv32 ++ RCX[32:0]);

label_0x8af:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x8b3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x8bb:
t_151 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_151[64:0];
OF := bool2bv(t_151 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_151 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_61;
SF := unconstrained_62;
ZF := unconstrained_63;
AF := unconstrained_64;

label_0x8bf:
RCX := PLUS_64((PLUS_64(0bv64, 2246bv64)), 0bv64)[64:0];

label_0x8c6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x8ca:
t_153 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_153)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_153, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))))[1:0]));
SF := t_153[32:31];
ZF := bool2bv(0bv32 == t_153);

label_0x8ce:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x8eb;
}

label_0x8d0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x8d8:
t_157 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_157[64:0];
OF := bool2bv(t_157 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_157 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_65;
SF := unconstrained_66;
ZF := unconstrained_67;
AF := unconstrained_68;

label_0x8dc:
RCX := PLUS_64((PLUS_64(0bv64, 2275bv64)), 0bv64)[64:0];

label_0x8e3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x8e7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x8eb:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2289bv64)), 1bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2289bv64)), 1bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2289bv64)), 1bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2289bv64)), 1bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2289bv64)), 1bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x8f2:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x904;
}

label_0x8f4:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x8f8:
RCX := PLUS_64((PLUS_64(0bv64, 2303bv64)), 0bv64)[64:0];

label_0x8ff:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2308bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x904"} true;
call arbitrary_func();

label_0x904:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x909:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x911:
t_163 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RCX := t_163[64:0];
OF := bool2bv(t_163 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_163 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_69;
SF := unconstrained_70;
ZF := unconstrained_71;
AF := unconstrained_72;

label_0x915:
RDX := PLUS_64((PLUS_64(0bv64, 2332bv64)), 0bv64)[64:0];

label_0x91c:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x924:
t_165 := TIMES_128(((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
R8 := t_165[64:0];
OF := bool2bv(t_165 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
CF := bool2bv(t_165 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
PF := unconstrained_73;
SF := unconstrained_74;
ZF := unconstrained_75;
AF := unconstrained_76;

label_0x928:
R9 := PLUS_64((PLUS_64(0bv64, 2351bv64)), 0bv64)[64:0];

label_0x92f:
R10 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x937:
t_167 := TIMES_128(((ITE_128(bv2bool(R10[64:63]) ,(1bv64 ++ R10) ,(0bv64 ++ R10)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
R10 := t_167[64:0];
OF := bool2bv(t_167 != ((ITE_128(bv2bool(R10[64:63]) ,(1bv64 ++ R10) ,(0bv64 ++ R10)))));
CF := bool2bv(t_167 != ((ITE_128(bv2bool(R10[64:63]) ,(1bv64 ++ R10) ,(0bv64 ++ R10)))));
PF := unconstrained_77;
SF := unconstrained_78;
ZF := unconstrained_79;
AF := unconstrained_80;

label_0x93b:
R11 := PLUS_64((PLUS_64(0bv64, 2370bv64)), 0bv64)[64:0];

label_0x942:
R10 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64((PLUS_64(R11, R10)), 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R11, R10)), 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R11, R10)), 4bv64)))));

label_0x947:
t1_169 := R10;
t2_170 := LOAD_LE_64(mem, PLUS_64((PLUS_64(R9, R8)), 16bv64));
R10 := PLUS_64(R10, t2_170);
CF := bool2bv(LT_64(R10, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (R10[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R10, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R10, 4bv64)), R10)), 2bv64)), (XOR_64((RSHIFT_64(R10, 4bv64)), R10)))))[1:0]));
SF := R10[64:63];
ZF := bool2bv(0bv64 == R10);

label_0x94c:
R8 := R10;

label_0x94f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), R8);

label_0x954:
R8 := RAX;

label_0x957:
RDX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RDX, RCX)), 16bv64));

label_0x95c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x961:
RCX := RAX;

label_0x964:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2409bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x969"} true;
call arbitrary_func();

label_0x969:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x971:
t_175 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_175[64:0];
OF := bool2bv(t_175 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_175 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_81;
SF := unconstrained_82;
ZF := unconstrained_83;
AF := unconstrained_84;

label_0x975:
RCX := PLUS_64((PLUS_64(0bv64, 2428bv64)), 0bv64)[64:0];

label_0x97c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x980:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x984:
t1_177 := RAX[32:0];
t2_178 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_178));
CF := bool2bv(LT_32((RAX[32:0]), t1_177));
OF := AND_1((bool2bv((t1_177[32:31]) == (t2_178[32:31]))), (XOR_1((t1_177[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_177)), t2_178)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x986:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), RAX[32:0]);

label_0x98a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)))));

label_0x992:
t_183 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_183[64:0];
OF := bool2bv(t_183 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_183 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_85;
SF := unconstrained_86;
ZF := unconstrained_87;
AF := unconstrained_88;

label_0x996:
RCX := PLUS_64((PLUS_64(0bv64, 2461bv64)), 0bv64)[64:0];

label_0x99d:
t1_185 := RCX;
t2_186 := RAX;
RCX := PLUS_64(RCX, t2_186);
CF := bool2bv(LT_64(RCX, t1_185));
OF := AND_1((bool2bv((t1_185[64:63]) == (t2_186[64:63]))), (XOR_1((t1_185[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_185)), t2_186)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9a0:
RAX := RCX;

label_0x9a3:
t1_191 := RAX;
t2_192 := 4bv64;
RAX := PLUS_64(RAX, t2_192);
CF := bool2bv(LT_64(RAX, t1_191));
OF := AND_1((bool2bv((t1_191[64:63]) == (t2_192[64:63]))), (XOR_1((t1_191[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_191)), t2_192)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9a7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x9ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x9b1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_89;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9b7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9bc:
t_199 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x9bf:
if (bv2bool(ZF)) {
  goto label_0x9c2;
}

label_0x9c1:
assume false;

label_0x9c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x9c7:
origDEST_203 := RAX;
origCOUNT_204 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), CF, LSHIFT_64(origDEST_203, (MINUS_64(64bv64, origCOUNT_204)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv64)), origDEST_203[64:63], unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), AF, unconstrained_92);

label_0x9cb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9d2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9d6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x9db:
origDEST_209 := RCX;
origCOUNT_210 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_94);

label_0x9df:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_95;
SF := unconstrained_96;
AF := unconstrained_97;
PF := unconstrained_98;

label_0x9e3:
if (bv2bool(CF)) {
  goto label_0x9e6;
}

label_0x9e5:
assume false;

label_0x9e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x9eb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 84bv64)));

label_0x9ef:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9f1:
goto label_0x869;

label_0x9f6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_99;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x9f8:
t1_215 := RSP;
t2_216 := 120bv64;
RSP := PLUS_64(RSP, t2_216);
CF := bool2bv(LT_64(RSP, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x9fc:

ra_221 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R11,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_128,origCOUNT_134,origCOUNT_204,origCOUNT_210,origCOUNT_30,origCOUNT_36,origCOUNT_62,origCOUNT_68,origDEST_127,origDEST_133,origDEST_203,origDEST_209,origDEST_29,origDEST_35,origDEST_61,origDEST_67,ra_221,t1_101,t1_109,t1_11,t1_115,t1_169,t1_17,t1_177,t1_185,t1_191,t1_215,t1_43,t1_49,t1_73,t1_85,t2_102,t2_110,t2_116,t2_12,t2_170,t2_178,t2_18,t2_186,t2_192,t2_216,t2_44,t2_50,t2_74,t2_86,t_1,t_107,t_123,t_139,t_141,t_145,t_147,t_151,t_153,t_157,t_159,t_163,t_165,t_167,t_175,t_183,t_199,t_25,t_41,t_5,t_57,t_79,t_83,t_9,t_91,t_95,t_99;

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
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R11: bv64;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_128: bv64;
var origCOUNT_134: bv64;
var origCOUNT_204: bv64;
var origCOUNT_210: bv64;
var origCOUNT_30: bv64;
var origCOUNT_36: bv64;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origDEST_127: bv64;
var origDEST_133: bv64;
var origDEST_203: bv64;
var origDEST_209: bv64;
var origDEST_29: bv64;
var origDEST_35: bv64;
var origDEST_61: bv64;
var origDEST_67: bv64;
var ra_221: bv64;
var t1_101: bv32;
var t1_109: bv64;
var t1_11: bv64;
var t1_115: bv64;
var t1_169: bv64;
var t1_17: bv64;
var t1_177: bv32;
var t1_185: bv64;
var t1_191: bv64;
var t1_215: bv64;
var t1_43: bv64;
var t1_49: bv64;
var t1_73: bv32;
var t1_85: bv64;
var t2_102: bv32;
var t2_110: bv64;
var t2_116: bv64;
var t2_12: bv64;
var t2_170: bv64;
var t2_178: bv32;
var t2_18: bv64;
var t2_186: bv64;
var t2_192: bv64;
var t2_216: bv64;
var t2_44: bv64;
var t2_50: bv64;
var t2_74: bv32;
var t2_86: bv64;
var t_1: bv64;
var t_107: bv128;
var t_123: bv64;
var t_139: bv128;
var t_141: bv32;
var t_145: bv128;
var t_147: bv32;
var t_151: bv128;
var t_153: bv32;
var t_157: bv128;
var t_159: bv32;
var t_163: bv128;
var t_165: bv128;
var t_167: bv128;
var t_175: bv128;
var t_183: bv128;
var t_199: bv64;
var t_25: bv64;
var t_41: bv128;
var t_5: bv32;
var t_57: bv64;
var t_79: bv32;
var t_83: bv128;
var t_9: bv128;
var t_91: bv32;
var t_95: bv32;
var t_99: bv128;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(48bv64);
axiom policy(112bv64);
axiom policy(176bv64);
axiom policy(720bv64);
axiom policy(1504bv64);
axiom policy(2576bv64);
axiom policy(3104bv64);
axiom policy(3392bv64);
axiom policy(3856bv64);
axiom policy(4240bv64);
axiom policy(4672bv64);
axiom policy(5232bv64);
axiom policy(5728bv64);
axiom policy(5856bv64);
axiom policy(6336bv64);
axiom policy(6352bv64);
axiom policy(6480bv64);
