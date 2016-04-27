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
axiom _function_addr_low == 4240bv64;
axiom _function_addr_high == 4672bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1090:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x1094:
mem := STORE_LE_8(mem, PLUS_64(RSP, 8bv64), RCX[32:0][8:0]);

label_0x1098:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x109c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x10a4:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4266bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4266bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4266bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4266bv64)), 1bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4266bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x10ab:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x10bd;
}

label_0x10ad:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x10b1:
RCX := PLUS_64((PLUS_64(0bv64, 4280bv64)), 0bv64)[64:0];

label_0x10b8:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4285bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x10bd"} true;
call arbitrary_func();

label_0x10bd:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x10c2:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x10e9;
}

label_0x10c4:
RCX := (0bv32 ++ 2bv32);

label_0x10c9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4302bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x10ce"} true;
call arbitrary_func();

label_0x10ce:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x10d3:
RDX := PLUS_64((PLUS_64(0bv64, 4314bv64)), 0bv64)[64:0];

label_0x10da:
RCX := RAX;

label_0x10dd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4322bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x10e2"} true;
call arbitrary_func();

label_0x10e2:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x10e4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4329bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x10e9"} true;
call arbitrary_func();

label_0x10e9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x10ee:
t_13 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_13[64:0];
OF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_2;
SF := unconstrained_3;
ZF := unconstrained_4;
AF := unconstrained_5;

label_0x10f2:
RCX := PLUS_64((PLUS_64(0bv64, 4345bv64)), 0bv64)[64:0];

label_0x10f9:
t_15 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))), t_15)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_15, (LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)), 2bv32)), (XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)), 2bv32)), (XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)))))[1:0]));
SF := t_15[32:31];
ZF := bool2bv(0bv32 == t_15);

label_0x10fe:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x1149;
}

label_0x1100:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x1105:
t_19 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_19[64:0];
OF := bool2bv(t_19 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_19 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_6;
SF := unconstrained_7;
ZF := unconstrained_8;
AF := unconstrained_9;

label_0x1109:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x110e:
RCX := PLUS_64((PLUS_64(0bv64, 4373bv64)), 0bv64)[64:0];

label_0x1115:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RCX);

label_0x111a:
RCX := (0bv32 ++ 2bv32);

label_0x111f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4388bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1124"} true;
call arbitrary_func();

label_0x1124:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1129:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x112e:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RDX, RCX)), 8bv64)));

label_0x1133:
RDX := PLUS_64((PLUS_64(0bv64, 4410bv64)), 0bv64)[64:0];

label_0x113a:
RCX := RAX;

label_0x113d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4418bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1142"} true;
call arbitrary_func();

label_0x1142:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1144:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4425bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1149"} true;
call arbitrary_func();

label_0x1149:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x114e:
t_21 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_21[64:0];
OF := bool2bv(t_21 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_21 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_11;
SF := unconstrained_12;
ZF := unconstrained_13;
AF := unconstrained_14;

label_0x1152:
RCX := PLUS_64((PLUS_64(0bv64, 4441bv64)), 0bv64)[64:0];

label_0x1159:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64)));

label_0x115d:
t_23 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_23, 1bv32)), (XOR_32(t_23, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_23)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x115f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1163:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x1168:
t_27 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_27[64:0];
OF := bool2bv(t_27 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_27 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_15;
SF := unconstrained_16;
ZF := unconstrained_17;
AF := unconstrained_18;

label_0x116c:
RCX := PLUS_64((PLUS_64(0bv64, 4467bv64)), 0bv64)[64:0];

label_0x1173:
t1_29 := RCX;
t2_30 := RAX;
RCX := PLUS_64(RCX, t2_30);
CF := bool2bv(LT_64(RCX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1176:
RAX := RCX;

label_0x1179:
t1_35 := RAX;
t2_36 := 8bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x117d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1182:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1187:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x118d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1192:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x1195:
if (bv2bool(ZF)) {
  goto label_0x1198;
}

label_0x1197:
assume false;

label_0x1198:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x119d:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_22);

label_0x11a1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11a8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11ac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x11b1:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_24);

label_0x11b5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x11b9:
if (bv2bool(CF)) {
  goto label_0x11bc;
}

label_0x11bb:
assume false;

label_0x11bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x11c1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x11c5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x11c7:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 80bv64))));

label_0x11cc:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x11d1:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)))));

label_0x11d6:
t_59 := TIMES_128(((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RDX := t_59[64:0];
OF := bool2bv(t_59 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
CF := bool2bv(t_59 != ((ITE_128(bv2bool(RDX[64:63]) ,(1bv64 ++ RDX) ,(0bv64 ++ RDX)))));
PF := unconstrained_29;
SF := unconstrained_30;
ZF := unconstrained_31;
AF := unconstrained_32;

label_0x11da:
R8 := PLUS_64((PLUS_64(0bv64, 4577bv64)), 0bv64)[64:0];

label_0x11e1:
RDX := LOAD_LE_64(mem, PLUS_64((PLUS_64(R8, RDX)), 16bv64));

label_0x11e6:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0x11ea:
t_61 := MINUS_32((RCX[32:0]), (RAX[32:0]));
CF := bool2bv(LT_32((RCX[32:0]), (RAX[32:0])));
OF := AND_32((XOR_32((RCX[32:0]), (RAX[32:0]))), (XOR_32((RCX[32:0]), t_61)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_61, (RCX[32:0]))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))))[1:0]));
SF := t_61[32:31];
ZF := bool2bv(0bv32 == t_61);

label_0x11ec:
if (bv2bool(ZF)) {
  goto label_0x120e;
}

label_0x11ee:
RCX := (0bv32 ++ 2bv32);

label_0x11f3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4600bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x11f8"} true;
call arbitrary_func();

label_0x11f8:
RDX := PLUS_64((PLUS_64(0bv64, 4607bv64)), 0bv64)[64:0];

label_0x11ff:
RCX := RAX;

label_0x1202:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4615bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1207"} true;
call arbitrary_func();

label_0x1207:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_33;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1209:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4622bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x120e"} true;
call arbitrary_func();

label_0x120e:
t_65 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4628bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4628bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4628bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4628bv64)), 1bv64))), t_65)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_65, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 4628bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))))[1:0]));
SF := t_65[32:31];
ZF := bool2bv(0bv32 == t_65);

label_0x1215:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1227;
}

label_0x1217:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x121b:
RCX := PLUS_64((PLUS_64(0bv64, 4642bv64)), 0bv64)[64:0];

label_0x1222:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4647bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1227"} true;
call arbitrary_func();

label_0x1227:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 80bv64))));

label_0x122c:
t1_69 := RSP;
t2_70 := 72bv64;
RSP := PLUS_64(RSP, t2_70);
CF := bool2bv(LT_64(RSP, t1_69));
OF := AND_1((bool2bv((t1_69[64:63]) == (t2_70[64:63]))), (XOR_1((t1_69[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_69)), t2_70)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1230:

ra_75 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_48,origCOUNT_54,origDEST_47,origDEST_53,ra_75,t1_29,t1_35,t1_69,t2_30,t2_36,t2_70,t_1,t_13,t_15,t_19,t_21,t_23,t_27,t_43,t_5,t_59,t_61,t_65,t_9;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_48: bv64;
var origCOUNT_54: bv64;
var origDEST_47: bv64;
var origDEST_53: bv64;
var ra_75: bv64;
var t1_29: bv64;
var t1_35: bv64;
var t1_69: bv64;
var t2_30: bv64;
var t2_36: bv64;
var t2_70: bv64;
var t_1: bv64;
var t_13: bv128;
var t_15: bv32;
var t_19: bv128;
var t_21: bv128;
var t_23: bv32;
var t_27: bv128;
var t_43: bv64;
var t_5: bv32;
var t_59: bv128;
var t_61: bv32;
var t_65: bv32;
var t_9: bv32;


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
