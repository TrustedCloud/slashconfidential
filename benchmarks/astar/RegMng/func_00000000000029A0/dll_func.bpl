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
axiom _function_addr_low == 10656bv64;
axiom _function_addr_high == 12272bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x29a0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x29a5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x29aa:
t_1 := RSP;
RSP := MINUS_64(RSP, 184bv64);
CF := bool2bv(LT_64(t_1, 184bv64));
OF := AND_64((XOR_64(t_1, 184bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 184bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x29b1:
RDX := (0bv32 ++ 32768bv32);

label_0x29b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x29be:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10691bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x29c3"} true;
call arbitrary_func();

label_0x29c3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x29c7:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 4294967295bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 4294967295bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x29cc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x29d5;
}

label_0x29ce:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x29d0:
goto label_0x2fdc;

label_0x29d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x29dd:
t1_9 := RAX;
t2_10 := 324bv64;
RAX := PLUS_64(RAX, t2_10);
CF := bool2bv(LT_64(RAX, t1_9));
OF := AND_1((bool2bv((t1_9[64:63]) == (t2_10[64:63]))), (XOR_1((t1_9[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_9)), t2_10)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29e3:
R8 := (0bv32 ++ 1bv32);

label_0x29e9:
RDX := RAX;

label_0x29ec:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x29f0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10741bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x29f5"} true;
call arbitrary_func();

label_0x29f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x29fd:
t1_15 := RAX;
t2_16 := 325bv64;
RAX := PLUS_64(RAX, t2_16);
CF := bool2bv(LT_64(RAX, t1_15));
OF := AND_1((bool2bv((t1_15[64:63]) == (t2_16[64:63]))), (XOR_1((t1_15[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_15)), t2_16)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a03:
R8 := (0bv32 ++ 1bv32);

label_0x2a09:
RDX := RAX;

label_0x2a0c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2a10:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10773bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a15"} true;
call arbitrary_func();

label_0x2a15:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a1d:
t1_21 := RAX;
t2_22 := 326bv64;
RAX := PLUS_64(RAX, t2_22);
CF := bool2bv(LT_64(RAX, t1_21));
OF := AND_1((bool2bv((t1_21[64:63]) == (t2_22[64:63]))), (XOR_1((t1_21[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_21)), t2_22)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a23:
R8 := (0bv32 ++ 1bv32);

label_0x2a29:
RDX := RAX;

label_0x2a2c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2a30:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10805bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a35"} true;
call arbitrary_func();

label_0x2a35:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a3d:
t1_27 := RAX;
t2_28 := 327bv64;
RAX := PLUS_64(RAX, t2_28);
CF := bool2bv(LT_64(RAX, t1_27));
OF := AND_1((bool2bv((t1_27[64:63]) == (t2_28[64:63]))), (XOR_1((t1_27[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_27)), t2_28)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a43:
R8 := (0bv32 ++ 1bv32);

label_0x2a49:
RDX := RAX;

label_0x2a4c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2a50:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10837bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a55"} true;
call arbitrary_func();

label_0x2a55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a5d:
t1_33 := RAX;
t2_34 := 328bv64;
RAX := PLUS_64(RAX, t2_34);
CF := bool2bv(LT_64(RAX, t1_33));
OF := AND_1((bool2bv((t1_33[64:63]) == (t2_34[64:63]))), (XOR_1((t1_33[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_33)), t2_34)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a63:
R8 := (0bv32 ++ 1bv32);

label_0x2a69:
RDX := RAX;

label_0x2a6c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2a70:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10869bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a75"} true;
call arbitrary_func();

label_0x2a75:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a7d:
t1_39 := RAX;
t2_40 := 329bv64;
RAX := PLUS_64(RAX, t2_40);
CF := bool2bv(LT_64(RAX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a83:
R8 := (0bv32 ++ 1bv32);

label_0x2a89:
RDX := RAX;

label_0x2a8c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2a90:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10901bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2a95"} true;
call arbitrary_func();

label_0x2a95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2a9d:
t1_45 := RAX;
t2_46 := 330bv64;
RAX := PLUS_64(RAX, t2_46);
CF := bool2bv(LT_64(RAX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2aa3:
R8 := (0bv32 ++ 1bv32);

label_0x2aa9:
RDX := RAX;

label_0x2aac:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2ab0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10933bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2ab5"} true;
call arbitrary_func();

label_0x2ab5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2abd:
t1_51 := RAX;
t2_52 := 331bv64;
RAX := PLUS_64(RAX, t2_52);
CF := bool2bv(LT_64(RAX, t1_51));
OF := AND_1((bool2bv((t1_51[64:63]) == (t2_52[64:63]))), (XOR_1((t1_51[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_51)), t2_52)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ac3:
R8 := (0bv32 ++ 1bv32);

label_0x2ac9:
RDX := RAX;

label_0x2acc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2ad0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10965bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2ad5"} true;
call arbitrary_func();

label_0x2ad5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2add:
t1_57 := RAX;
t2_58 := 324bv64;
RAX := PLUS_64(RAX, t2_58);
CF := bool2bv(LT_64(RAX, t1_57));
OF := AND_1((bool2bv((t1_57[64:63]) == (t2_58[64:63]))), (XOR_1((t1_57[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_57)), t2_58)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ae3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x2aeb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2af3:
t1_63 := RAX;
t2_64 := 332bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2af9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x2afe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2b03:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b09:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2b0e:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x2b11:
if (bv2bool(ZF)) {
  goto label_0x2b14;
}

label_0x2b13:
assume false;

label_0x2b14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2b19:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_5);

label_0x2b1d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2b24:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2b28:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2b2d:
origDEST_81 := RCX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_7);

label_0x2b31:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x2b35:
if (bv2bool(CF)) {
  goto label_0x2b38;
}

label_0x2b37:
assume false;

label_0x2b38:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2b3d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2b45:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x2b47:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2b49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2b51:
t1_87 := RAX;
t2_88 := 328bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b57:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x2b5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2b67:
t1_93 := RAX;
t2_94 := 336bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b6d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x2b72:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2b77:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b7d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2b82:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x2b85:
if (bv2bool(ZF)) {
  goto label_0x2b88;
}

label_0x2b87:
assume false;

label_0x2b88:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2b8d:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_15);

label_0x2b91:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2b98:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2b9c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2ba1:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_17);

label_0x2ba5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x2ba9:
if (bv2bool(CF)) {
  goto label_0x2bac;
}

label_0x2bab:
assume false;

label_0x2bac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2bb1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x2bb9:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x2bbb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2bbd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2bc5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2bcb:
t_117 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_117, 1bv32)), (XOR_32(t_117, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_117)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2bcd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x2bd1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2bd9:
t1_121 := RAX;
t2_122 := 316bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bdf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x2be4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x2be9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bef:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2bf4:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x2bf7:
if (bv2bool(ZF)) {
  goto label_0x2bfa;
}

label_0x2bf9:
assume false;

label_0x2bfa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x2bff:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_25);

label_0x2c03:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2c0a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2c0e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x2c13:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_27);

label_0x2c17:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0x2c1b:
if (bv2bool(CF)) {
  goto label_0x2c1e;
}

label_0x2c1d:
assume false;

label_0x2c1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x2c23:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x2c27:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2c29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2c31:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 336bv64)));

label_0x2c37:
t_145 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_145, 1bv32)), (XOR_32(t_145, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2c39:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x2c3d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2c45:
t1_149 := RAX;
t2_150 := 320bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2c4b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x2c50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2c55:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2c5b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2c60:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x2c63:
if (bv2bool(ZF)) {
  goto label_0x2c66;
}

label_0x2c65:
assume false;

label_0x2c66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2c6b:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_35);

label_0x2c6f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2c76:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2c7a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2c7f:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_37);

label_0x2c83:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0x2c87:
if (bv2bool(CF)) {
  goto label_0x2c8a;
}

label_0x2c89:
assume false;

label_0x2c8a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2c8f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 124bv64)));

label_0x2c93:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2c95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2c9d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2ca5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2cab:
t_173 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_173[32:0]);
OF := bool2bv(t_173 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_173 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_42;
SF := unconstrained_43;
ZF := unconstrained_44;
AF := unconstrained_45;

label_0x2cb2:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2cb4:
origDEST_175 := RAX;
origCOUNT_176 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, RSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_47);

label_0x2cb8:
RCX := RAX;

label_0x2cbb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11456bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2cc0"} true;
call arbitrary_func();

label_0x2cc0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x2cc8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2cd0:
t1_181 := RAX;
t2_182 := 32bv64;
RAX := PLUS_64(RAX, t2_182);
CF := bool2bv(LT_64(RAX, t1_181));
OF := AND_1((bool2bv((t1_181[64:63]) == (t2_182[64:63]))), (XOR_1((t1_181[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_181)), t2_182)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2cd4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x2cd9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2cde:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ce4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2ce9:
t_189 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))))[1:0]));
SF := t_189[64:63];
ZF := bool2bv(0bv64 == t_189);

label_0x2cec:
if (bv2bool(ZF)) {
  goto label_0x2cef;
}

label_0x2cee:
assume false;

label_0x2cef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2cf4:
origDEST_193 := RAX;
origCOUNT_194 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), CF, LSHIFT_64(origDEST_193, (MINUS_64(64bv64, origCOUNT_194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_194 == 1bv64)), origDEST_193[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), AF, unconstrained_51);

label_0x2cf8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2cff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2d03:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2d08:
origDEST_199 := RCX;
origCOUNT_200 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_53);

label_0x2d0c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x2d10:
if (bv2bool(CF)) {
  goto label_0x2d13;
}

label_0x2d12:
assume false;

label_0x2d13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2d18:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2d20:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2d23:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2d2b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2d33:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2d39:
t_205 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_205[32:0]);
OF := bool2bv(t_205 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_205 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_58;
SF := unconstrained_59;
ZF := unconstrained_60;
AF := unconstrained_61;

label_0x2d40:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2d42:
RCX := RAX;

label_0x2d45:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11594bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2d4a"} true;
call arbitrary_func();

label_0x2d4a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x2d52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2d5a:
t1_207 := RAX;
t2_208 := 40bv64;
RAX := PLUS_64(RAX, t2_208);
CF := bool2bv(LT_64(RAX, t1_207));
OF := AND_1((bool2bv((t1_207[64:63]) == (t2_208[64:63]))), (XOR_1((t1_207[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_207)), t2_208)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2d5e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x2d63:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2d68:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2d6e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2d73:
t_215 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)), 2bv64)), (XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)), 2bv64)), (XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)))))[1:0]));
SF := t_215[64:63];
ZF := bool2bv(0bv64 == t_215);

label_0x2d76:
if (bv2bool(ZF)) {
  goto label_0x2d79;
}

label_0x2d78:
assume false;

label_0x2d79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2d7e:
origDEST_219 := RAX;
origCOUNT_220 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), CF, LSHIFT_64(origDEST_219, (MINUS_64(64bv64, origCOUNT_220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv64)), origDEST_219[64:63], unconstrained_64));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), AF, unconstrained_65);

label_0x2d82:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2d89:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2d8d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2d92:
origDEST_225 := RCX;
origCOUNT_226 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), CF, LSHIFT_64(origDEST_225, (MINUS_64(64bv64, origCOUNT_226)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_226 == 1bv64)), origDEST_225[64:63], unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), AF, unconstrained_67);

label_0x2d96:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_68;
SF := unconstrained_69;
AF := unconstrained_70;
PF := unconstrained_71;

label_0x2d9a:
if (bv2bool(CF)) {
  goto label_0x2d9d;
}

label_0x2d9c:
assume false;

label_0x2d9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2da2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x2daa:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2dad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2db5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2dbd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2dc3:
t_231 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_231[32:0]);
OF := bool2bv(t_231 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_231 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_72;
SF := unconstrained_73;
ZF := unconstrained_74;
AF := unconstrained_75;

label_0x2dca:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2dcc:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, RSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_77);

label_0x2dcf:
RCX := RAX;

label_0x2dd2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11735bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2dd7"} true;
call arbitrary_func();

label_0x2dd7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x2ddf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2de7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x2dec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2df1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2df7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2dfc:
t_241 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))))[1:0]));
SF := t_241[64:63];
ZF := bool2bv(0bv64 == t_241);

label_0x2dff:
if (bv2bool(ZF)) {
  goto label_0x2e02;
}

label_0x2e01:
assume false;

label_0x2e02:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2e07:
origDEST_245 := RAX;
origCOUNT_246 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_81);

label_0x2e0b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2e12:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2e16:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2e1b:
origDEST_251 := RCX;
origCOUNT_252 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), CF, LSHIFT_64(origDEST_251, (MINUS_64(64bv64, origCOUNT_252)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv64)), origDEST_251[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), AF, unconstrained_83);

label_0x2e1f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_84;
SF := unconstrained_85;
AF := unconstrained_86;
PF := unconstrained_87;

label_0x2e23:
if (bv2bool(CF)) {
  goto label_0x2e26;
}

label_0x2e25:
assume false;

label_0x2e26:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2e2b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2e33:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2e36:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2e3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2e46:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2e4c:
t_257 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_257[32:0]);
OF := bool2bv(t_257 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_257 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_88;
SF := unconstrained_89;
ZF := unconstrained_90;
AF := unconstrained_91;

label_0x2e53:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2e55:
origDEST_259 := RAX;
origCOUNT_260 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), CF, RSHIFT_64(origDEST_259, (MINUS_64(64bv64, origCOUNT_260)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_260 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), AF, unconstrained_93);

label_0x2e58:
R8 := RAX;

label_0x2e5b:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_94;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2e5d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2e65:
RCX := LOAD_LE_64(mem, RAX);

label_0x2e68:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 11885bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2e6d"} true;
call arbitrary_func();

label_0x2e6d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2e75:
t1_265 := RAX;
t2_266 := 8bv64;
RAX := PLUS_64(RAX, t2_266);
CF := bool2bv(LT_64(RAX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e79:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x2e7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2e83:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e89:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2e8e:
t_273 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))))[1:0]));
SF := t_273[64:63];
ZF := bool2bv(0bv64 == t_273);

label_0x2e91:
if (bv2bool(ZF)) {
  goto label_0x2e94;
}

label_0x2e93:
assume false;

label_0x2e94:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2e99:
origDEST_277 := RAX;
origCOUNT_278 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), CF, LSHIFT_64(origDEST_277, (MINUS_64(64bv64, origCOUNT_278)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_278 == 1bv64)), origDEST_277[64:63], unconstrained_97));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), AF, unconstrained_98);

label_0x2e9d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2ea4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2ea8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2ead:
origDEST_283 := RCX;
origCOUNT_284 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), CF, LSHIFT_64(origDEST_283, (MINUS_64(64bv64, origCOUNT_284)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_284 == 1bv64)), origDEST_283[64:63], unconstrained_99));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), AF, unconstrained_100);

label_0x2eb1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_101;
SF := unconstrained_102;
AF := unconstrained_103;
PF := unconstrained_104;

label_0x2eb5:
if (bv2bool(CF)) {
  goto label_0x2eb8;
}

label_0x2eb7:
assume false;

label_0x2eb8:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_105;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2eba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2ebf:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x2ec2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2eca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2ed2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x2ed8:
t_289 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_289[32:0]);
OF := bool2bv(t_289 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_289 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_106;
SF := unconstrained_107;
ZF := unconstrained_108;
AF := unconstrained_109;

label_0x2edf:
R8 := (0bv32 ++ RAX[32:0]);

label_0x2ee2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2eea:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 40bv64));

label_0x2eee:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2ef2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12023bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2ef7"} true;
call arbitrary_func();

label_0x2ef7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x2eff:
goto label_0x2f0b;

label_0x2f01:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x2f05:
t_291 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_291[32:31]) == (1bv32[32:31]))), (XOR_1((t_291[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_291)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2f07:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x2f0b:
t_295 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_295)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_295, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_295, 4bv32)), t_295)), 2bv32)), (XOR_32((RSHIFT_32(t_295, 4bv32)), t_295)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_295, 4bv32)), t_295)), 2bv32)), (XOR_32((RSHIFT_32(t_295, 4bv32)), t_295)))))[1:0]));
SF := t_295[32:31];
ZF := bool2bv(0bv32 == t_295);

label_0x2f13:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x2f72;
}

label_0x2f15:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2f1d:
t1_299 := RAX;
t2_300 := 48bv64;
RAX := PLUS_64(RAX, t2_300);
CF := bool2bv(LT_64(RAX, t1_299));
OF := AND_1((bool2bv((t1_299[64:63]) == (t2_300[64:63]))), (XOR_1((t1_299[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_299)), t2_300)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f21:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));

label_0x2f26:
t1_305 := RAX;
t2_306 := RCX;
RAX := PLUS_64(RAX, t2_306);
CF := bool2bv(LT_64(RAX, t1_305));
OF := AND_1((bool2bv((t1_305[64:63]) == (t2_306[64:63]))), (XOR_1((t1_305[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_305)), t2_306)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f29:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x2f2e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2f33:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_110;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f39:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2f3e:
t_313 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_111;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)), 2bv64)), (XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)), 2bv64)), (XOR_64((RSHIFT_64(t_313, 4bv64)), t_313)))))[1:0]));
SF := t_313[64:63];
ZF := bool2bv(0bv64 == t_313);

label_0x2f41:
if (bv2bool(ZF)) {
  goto label_0x2f44;
}

label_0x2f43:
assume false;

label_0x2f44:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2f49:
origDEST_317 := RAX;
origCOUNT_318 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), CF, LSHIFT_64(origDEST_317, (MINUS_64(64bv64, origCOUNT_318)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_318 == 1bv64)), origDEST_317[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_318 == 0bv64)), AF, unconstrained_113);

label_0x2f4d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2f54:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2f58:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2f5d:
origDEST_323 := RCX;
origCOUNT_324 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), CF, LSHIFT_64(origDEST_323, (MINUS_64(64bv64, origCOUNT_324)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_324 == 1bv64)), origDEST_323[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv64)), AF, unconstrained_115);

label_0x2f61:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_116;
SF := unconstrained_117;
AF := unconstrained_118;
PF := unconstrained_119;

label_0x2f65:
if (bv2bool(CF)) {
  goto label_0x2f68;
}

label_0x2f67:
assume false;

label_0x2f68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2f6d:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x2f70:
goto label_0x2f01;

label_0x2f72:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2f7a:
t1_329 := RAX;
t2_330 := 48bv64;
RAX := PLUS_64(RAX, t2_330);
CF := bool2bv(LT_64(RAX, t1_329));
OF := AND_1((bool2bv((t1_329[64:63]) == (t2_330[64:63]))), (XOR_1((t1_329[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_329)), t2_330)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f7e:
RCX := (0bv32 ++ 1bv32);

label_0x2f83:
t_335 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RCX := t_335[64:0];
OF := bool2bv(t_335 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_335 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_120;
SF := unconstrained_121;
ZF := unconstrained_122;
AF := unconstrained_123;

label_0x2f87:
t1_337 := RAX;
t2_338 := RCX;
RAX := PLUS_64(RAX, t2_338);
CF := bool2bv(LT_64(RAX, t1_337));
OF := AND_1((bool2bv((t1_337[64:63]) == (t2_338[64:63]))), (XOR_1((t1_337[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_337)), t2_338)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f8a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x2f8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2f94:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_124;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f9a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2f9f:
t_345 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)), 2bv64)), (XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)), 2bv64)), (XOR_64((RSHIFT_64(t_345, 4bv64)), t_345)))))[1:0]));
SF := t_345[64:63];
ZF := bool2bv(0bv64 == t_345);

label_0x2fa2:
if (bv2bool(ZF)) {
  goto label_0x2fa5;
}

label_0x2fa4:
assume false;

label_0x2fa5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2faa:
origDEST_349 := RAX;
origCOUNT_350 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, LSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), origDEST_349[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_127);

label_0x2fae:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2fb5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2fb9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2fbe:
origDEST_355 := RCX;
origCOUNT_356 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), CF, LSHIFT_64(origDEST_355, (MINUS_64(64bv64, origCOUNT_356)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_356 == 1bv64)), origDEST_355[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), AF, unconstrained_129);

label_0x2fc2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_130;
SF := unconstrained_131;
AF := unconstrained_132;
PF := unconstrained_133;

label_0x2fc6:
if (bv2bool(CF)) {
  goto label_0x2fc9;
}

label_0x2fc8:
assume false;

label_0x2fc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2fce:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x2fd1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2fd5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12250bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2fda"} true;
call arbitrary_func();

label_0x2fda:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x2fdc:
t1_361 := RSP;
t2_362 := 184bv64;
RSP := PLUS_64(RSP, t2_362);
CF := bool2bv(LT_64(RSP, t1_361));
OF := AND_1((bool2bv((t1_361[64:63]) == (t2_362[64:63]))), (XOR_1((t1_361[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_361)), t2_362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2fe3:

ra_367 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_134,origCOUNT_140,origCOUNT_162,origCOUNT_168,origCOUNT_176,origCOUNT_194,origCOUNT_200,origCOUNT_220,origCOUNT_226,origCOUNT_234,origCOUNT_246,origCOUNT_252,origCOUNT_260,origCOUNT_278,origCOUNT_284,origCOUNT_318,origCOUNT_324,origCOUNT_350,origCOUNT_356,origCOUNT_76,origCOUNT_82,origDEST_105,origDEST_111,origDEST_133,origDEST_139,origDEST_161,origDEST_167,origDEST_175,origDEST_193,origDEST_199,origDEST_219,origDEST_225,origDEST_233,origDEST_245,origDEST_251,origDEST_259,origDEST_277,origDEST_283,origDEST_317,origDEST_323,origDEST_349,origDEST_355,origDEST_75,origDEST_81,ra_367,t1_121,t1_149,t1_15,t1_181,t1_207,t1_21,t1_265,t1_27,t1_299,t1_305,t1_329,t1_33,t1_337,t1_361,t1_39,t1_45,t1_51,t1_57,t1_63,t1_87,t1_9,t1_93,t2_10,t2_122,t2_150,t2_16,t2_182,t2_208,t2_22,t2_266,t2_28,t2_300,t2_306,t2_330,t2_338,t2_34,t2_362,t2_40,t2_46,t2_52,t2_58,t2_64,t2_88,t2_94,t_1,t_101,t_117,t_129,t_145,t_157,t_173,t_189,t_205,t_215,t_231,t_241,t_257,t_273,t_289,t_291,t_295,t_313,t_335,t_345,t_5,t_71;

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
var R8: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_106: bv64;
var origCOUNT_112: bv64;
var origCOUNT_134: bv64;
var origCOUNT_140: bv64;
var origCOUNT_162: bv64;
var origCOUNT_168: bv64;
var origCOUNT_176: bv64;
var origCOUNT_194: bv64;
var origCOUNT_200: bv64;
var origCOUNT_220: bv64;
var origCOUNT_226: bv64;
var origCOUNT_234: bv64;
var origCOUNT_246: bv64;
var origCOUNT_252: bv64;
var origCOUNT_260: bv64;
var origCOUNT_278: bv64;
var origCOUNT_284: bv64;
var origCOUNT_318: bv64;
var origCOUNT_324: bv64;
var origCOUNT_350: bv64;
var origCOUNT_356: bv64;
var origCOUNT_76: bv64;
var origCOUNT_82: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_161: bv64;
var origDEST_167: bv64;
var origDEST_175: bv64;
var origDEST_193: bv64;
var origDEST_199: bv64;
var origDEST_219: bv64;
var origDEST_225: bv64;
var origDEST_233: bv64;
var origDEST_245: bv64;
var origDEST_251: bv64;
var origDEST_259: bv64;
var origDEST_277: bv64;
var origDEST_283: bv64;
var origDEST_317: bv64;
var origDEST_323: bv64;
var origDEST_349: bv64;
var origDEST_355: bv64;
var origDEST_75: bv64;
var origDEST_81: bv64;
var ra_367: bv64;
var t1_121: bv64;
var t1_149: bv64;
var t1_15: bv64;
var t1_181: bv64;
var t1_207: bv64;
var t1_21: bv64;
var t1_265: bv64;
var t1_27: bv64;
var t1_299: bv64;
var t1_305: bv64;
var t1_329: bv64;
var t1_33: bv64;
var t1_337: bv64;
var t1_361: bv64;
var t1_39: bv64;
var t1_45: bv64;
var t1_51: bv64;
var t1_57: bv64;
var t1_63: bv64;
var t1_87: bv64;
var t1_9: bv64;
var t1_93: bv64;
var t2_10: bv64;
var t2_122: bv64;
var t2_150: bv64;
var t2_16: bv64;
var t2_182: bv64;
var t2_208: bv64;
var t2_22: bv64;
var t2_266: bv64;
var t2_28: bv64;
var t2_300: bv64;
var t2_306: bv64;
var t2_330: bv64;
var t2_338: bv64;
var t2_34: bv64;
var t2_362: bv64;
var t2_40: bv64;
var t2_46: bv64;
var t2_52: bv64;
var t2_58: bv64;
var t2_64: bv64;
var t2_88: bv64;
var t2_94: bv64;
var t_1: bv64;
var t_101: bv64;
var t_117: bv32;
var t_129: bv64;
var t_145: bv32;
var t_157: bv64;
var t_173: bv64;
var t_189: bv64;
var t_205: bv64;
var t_215: bv64;
var t_231: bv64;
var t_241: bv64;
var t_257: bv64;
var t_273: bv64;
var t_289: bv64;
var t_291: bv32;
var t_295: bv32;
var t_313: bv64;
var t_335: bv128;
var t_345: bv64;
var t_5: bv32;
var t_71: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(208bv64);
axiom policy(688bv64);
axiom policy(1184bv64);
axiom policy(3040bv64);
axiom policy(3232bv64);
axiom policy(3488bv64);
axiom policy(4240bv64);
axiom policy(4816bv64);
axiom policy(5840bv64);
axiom policy(6768bv64);
axiom policy(7760bv64);
axiom policy(8352bv64);
axiom policy(8720bv64);
axiom policy(10656bv64);
axiom policy(12272bv64);
axiom policy(13488bv64);
axiom policy(13872bv64);
