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
axiom _function_addr_low == 21120bv64;
axiom _function_addr_high == 21327bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x5280:
t_1 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x5282:
t_3 := RSP;
RSP := MINUS_64(RSP, 32bv64);
CF := bool2bv(LT_64(t_3, 32bv64));
OF := AND_64((XOR_64(t_3, 32bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 32bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x5286:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(8676bv64, 21132bv64)), 0bv64)));

label_0x528c:
RBX := RCX;

label_0x528f:
t_7 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_7, 4bv32)), t_7)), 2bv32)), (XOR_32((RSHIFT_32(t_7, 4bv32)), t_7)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_7, 4bv32)), t_7)), 2bv32)), (XOR_32((RSHIFT_32(t_7, 4bv32)), t_7)))))[1:0]));
SF := t_7[32:31];
ZF := bool2bv(0bv32 == t_7);

label_0x5291:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5349;
}

label_0x5297:
RAX := PLUS_64((PLUS_64(8666bv64, 21150bv64)), 0bv64)[64:0];

label_0x529e:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8655bv64, 21157bv64)), 4bv64), 3bv64);

label_0x52a9:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8712bv64, 21168bv64)), 0bv64), RAX);

label_0x52b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x52b5:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8716bv64, 21180bv64)), 0bv64), RAX);

label_0x52bc:
RAX := (0bv32 ++ 1bv32);

label_0x52c1:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8632bv64, 21192bv64)), 0bv64), R9);

label_0x52c8:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8633bv64, 21199bv64)), 0bv64), RDX);

label_0x52cf:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8646bv64, 21206bv64)), 4bv64), 0bv64);

label_0x52da:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8695bv64, 21217bv64)), 0bv64), R8);

label_0x52e1:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8680bv64, 21224bv64)), 0bv64), RDX);

label_0x52e8:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(8657bv64, 21231bv64)), 0bv64), R9);

label_0x52ef:
t_11 := RAX[32:0];
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(8571bv64, 21237bv64)), 0bv64)));
mem := STORE_LE_32(mem, PLUS_64((PLUS_64(8571bv64, 21237bv64)), 0bv64), t_11);

label_0x52f5:
t_13 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x52f7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x530f;
}

label_0x52f9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21246bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5410"} true;
call arbitrary_func();

label_0x52fe:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(8547bv64, 21252bv64)), 1bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(8547bv64, 21252bv64)), 1bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(8547bv64, 21252bv64)), 1bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(8547bv64, 21252bv64)), 1bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64((PLUS_64(8547bv64, 21252bv64)), 1bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x5305:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x530f;
}

label_0x5307:
RCX := RBX;

label_0x530a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21263bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5370"} true;
call arbitrary_func();

label_0x530f:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(8602bv64, 21270bv64)), 0bv64));

label_0x5316:
t_21 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))))[1:0]));
SF := t_21[64:63];
ZF := bool2bv(0bv64 == t_21);

label_0x5319:
if (bv2bool(ZF)) {
  goto label_0x5326;
}

label_0x531b:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x531e:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_5;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5320:
RDX := (0bv32 ++ PLUS_64(R8, 2bv64)[32:0]);

label_0x5324:

target_25 := RAX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21286bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_25"} true;
call arbitrary_func();

label_0x5326:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(8571bv64, 21293bv64)), 0bv64));

label_0x532d:
t_27 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x5330:
if (bv2bool(ZF)) {
  goto label_0x5349;
}

label_0x5332:

target_31 := RAX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21300bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_31"} true;
call arbitrary_func();

label_0x5334:
t_33 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0x5336:
if (bv2bool(ZF)) {
  goto label_0x5349;
}

label_0x5338:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_8;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x533a:
RCX := (0bv32 ++ 3221225794bv32);

label_0x533f:
t1_37 := RSP;
t2_38 := 32bv64;
RSP := PLUS_64(RSP, t2_38);
CF := bool2bv(LT_64(RSP, t1_37));
OF := AND_1((bool2bv((t1_37[64:63]) == (t2_38[64:63]))), (XOR_1((t1_37[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_37)), t2_38)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x5343:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x5344:
assert {:SlashVerifyCommandType "remotejmp"} {:SlashVerifyJmpTarget "0x5270"} true;
return;

label_0x5349:
t1_43 := RSP;
t2_44 := 32bv64;
RSP := PLUS_64(RSP, t2_44);
CF := bool2bv(LT_64(RSP, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x534d:
RBX := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x534e:

ra_49 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RBX,RCX,RDX,RSP,SF,ZF,mem,ra_49,t1_37,t1_43,t2_38,t2_44,t_1,t_11,t_13,t_17,t_21,t_27,t_3,t_33,t_7,target_25,target_31;

const unconstrained_1: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
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
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RBX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var ra_49: bv64;
var t1_37: bv64;
var t1_43: bv64;
var t2_38: bv64;
var t2_44: bv64;
var t_1: bv64;
var t_11: bv32;
var t_13: bv32;
var t_17: bv32;
var t_21: bv64;
var t_27: bv64;
var t_3: bv64;
var t_33: bv32;
var t_7: bv32;
var target_25: bv64;
var target_31: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4272bv64);
axiom policy(4368bv64);
axiom policy(4464bv64);
axiom policy(4560bv64);
axiom policy(4960bv64);
axiom policy(4976bv64);
axiom policy(5008bv64);
axiom policy(5168bv64);
axiom policy(5216bv64);
axiom policy(5328bv64);
axiom policy(5872bv64);
axiom policy(4944bv64);
axiom policy(5632bv64);
axiom policy(5648bv64);
axiom policy(5760bv64);
axiom policy(5888bv64);
axiom policy(6224bv64);
axiom policy(6272bv64);
axiom policy(6288bv64);
axiom policy(6304bv64);
axiom policy(6320bv64);
axiom policy(6336bv64);
axiom policy(6352bv64);
axiom policy(6448bv64);
axiom policy(6848bv64);
axiom policy(6944bv64);
axiom policy(6960bv64);
axiom policy(7056bv64);
axiom policy(10096bv64);
axiom policy(10528bv64);
axiom policy(11312bv64);
axiom policy(13744bv64);
axiom policy(14160bv64);
axiom policy(14176bv64);
axiom policy(14672bv64);
axiom policy(14832bv64);
axiom policy(14848bv64);
axiom policy(15568bv64);
axiom policy(16528bv64);
axiom policy(19088bv64);
axiom policy(19472bv64);
axiom policy(19840bv64);
axiom policy(20720bv64);
axiom policy(20800bv64);
axiom policy(21008bv64);
axiom policy(21088bv64);
axiom policy(21104bv64);
axiom policy(21120bv64);
axiom policy(21328bv64);
axiom policy(21344bv64);
axiom policy(21360bv64);
axiom policy(21520bv64);
