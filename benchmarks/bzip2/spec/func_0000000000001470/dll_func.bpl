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
axiom _function_addr_low == 5232bv64;
axiom _function_addr_high == 5728bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1470:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x1475:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x147a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x147e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1483:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1487:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5261bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5261bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5261bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5261bv64)), 1bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5261bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x148e:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x14b3;
}

label_0x1490:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x1494:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1498:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x149d:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x14a2:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x14a7:
RCX := PLUS_64((PLUS_64(0bv64, 5294bv64)), 0bv64)[64:0];

label_0x14ae:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5299bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14b3"} true;
call arbitrary_func();

label_0x14b3:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x14b8:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x14df;
}

label_0x14ba:
RCX := (0bv32 ++ 2bv32);

label_0x14bf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5316bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14c4"} true;
call arbitrary_func();

label_0x14c4:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x14c9:
RDX := PLUS_64((PLUS_64(0bv64, 5328bv64)), 0bv64)[64:0];

label_0x14d0:
RCX := RAX;

label_0x14d3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5336bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14d8"} true;
call arbitrary_func();

label_0x14d8:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x14da:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5343bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x14df"} true;
call arbitrary_func();

label_0x14df:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x14e3:
t_13 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)))))));
RAX := (0bv32 ++ t_13[32:0]);
OF := bool2bv(t_13 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_13 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_2;
SF := unconstrained_3;
ZF := unconstrained_4;
AF := unconstrained_5;

label_0x14e8:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x14ea:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x14ef:
t_15 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RCX := t_15[64:0];
OF := bool2bv(t_15 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_15 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_6;
SF := unconstrained_7;
ZF := unconstrained_8;
AF := unconstrained_9;

label_0x14f3:
RDX := PLUS_64((PLUS_64(0bv64, 5370bv64)), 0bv64)[64:0];

label_0x14fa:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x14ff:
t_17 := TIMES_128(((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
R8 := t_17[64:0];
OF := bool2bv(t_17 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
CF := bool2bv(t_17 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
PF := unconstrained_10;
SF := unconstrained_11;
ZF := unconstrained_12;
AF := unconstrained_13;

label_0x1503:
R9 := PLUS_64((PLUS_64(0bv64, 5386bv64)), 0bv64)[64:0];

label_0x150a:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64)))));

label_0x150f:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RDX, RCX)), 16bv64));

label_0x1514:
t1_19 := RCX;
t2_20 := R8;
RCX := PLUS_64(RCX, t2_20);
CF := bool2bv(LT_64(RCX, t1_19));
OF := AND_1((bool2bv((t1_19[64:63]) == (t2_20[64:63]))), (XOR_1((t1_19[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_19)), t2_20)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1517:
R8 := RAX;

label_0x151a:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x151f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5412bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1524"} true;
call arbitrary_func();

label_0x1524:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x1529:
t_25 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_25[64:0];
OF := bool2bv(t_25 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_25 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_14;
SF := unconstrained_15;
ZF := unconstrained_16;
AF := unconstrained_17;

label_0x152d:
RCX := PLUS_64((PLUS_64(0bv64, 5428bv64)), 0bv64)[64:0];

label_0x1534:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x1538:
t_27 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)))))));
RDX := (0bv32 ++ t_27[32:0]);
OF := bool2bv(t_27 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_27 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_18;
SF := unconstrained_19;
ZF := unconstrained_20;
AF := unconstrained_21;

label_0x153d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0x1541:
t1_29 := RAX[32:0];
t2_30 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_30));
CF := bool2bv(LT_32((RAX[32:0]), t1_29));
OF := AND_1((bool2bv((t1_29[32:31]) == (t2_30[32:31]))), (XOR_1((t1_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_29)), t2_30)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1543:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x1547:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x154c:
t_35 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_35[64:0];
OF := bool2bv(t_35 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_35 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_22;
SF := unconstrained_23;
ZF := unconstrained_24;
AF := unconstrained_25;

label_0x1550:
RCX := PLUS_64((PLUS_64(0bv64, 5463bv64)), 0bv64)[64:0];

label_0x1557:
t1_37 := RCX;
t2_38 := RAX;
RCX := PLUS_64(RCX, t2_38);
CF := bool2bv(LT_64(RCX, t1_37));
OF := AND_1((bool2bv((t1_37[64:63]) == (t2_38[64:63]))), (XOR_1((t1_37[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_37)), t2_38)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x155a:
RAX := RCX;

label_0x155d:
t1_43 := RAX;
t2_44 := 4bv64;
RAX := PLUS_64(RAX, t2_44);
CF := bool2bv(LT_64(RAX, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1561:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1566:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x156b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1571:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1576:
t_51 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x1579:
if (bv2bool(ZF)) {
  goto label_0x157c;
}

label_0x157b:
assume false;

label_0x157c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1581:
origDEST_55 := RAX;
origCOUNT_56 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_29);

label_0x1585:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x158c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1590:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1595:
origDEST_61 := RCX;
origCOUNT_62 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_31);

label_0x1599:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_32;
SF := unconstrained_33;
AF := unconstrained_34;
PF := unconstrained_35;

label_0x159d:
if (bv2bool(CF)) {
  goto label_0x15a0;
}

label_0x159f:
assume false;

label_0x15a0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x15a5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x15a9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x15ab:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x15b0:
t_67 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_67[64:0];
OF := bool2bv(t_67 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_67 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_36;
SF := unconstrained_37;
ZF := unconstrained_38;
AF := unconstrained_39;

label_0x15b4:
RCX := PLUS_64((PLUS_64(0bv64, 5563bv64)), 0bv64)[64:0];

label_0x15bb:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x15bf:
t_69 := TIMES_64(((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)))))));
RDX := (0bv32 ++ t_69[32:0]);
OF := bool2bv(t_69 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
CF := bool2bv(t_69 != ((ITE_64(bv2bool(RDX[32:0][32:31]) ,(1bv32 ++ RDX[32:0]) ,(0bv32 ++ RDX[32:0])))));
PF := unconstrained_40;
SF := unconstrained_41;
ZF := unconstrained_42;
AF := unconstrained_43;

label_0x15c4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64)));

label_0x15c8:
t1_71 := RAX[32:0];
t2_72 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_72));
CF := bool2bv(LT_32((RAX[32:0]), t1_71));
OF := AND_1((bool2bv((t1_71[32:31]) == (t2_72[32:31]))), (XOR_1((t1_71[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_71)), t2_72)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x15ca:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x15ce:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)))));

label_0x15d3:
t_77 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_77[64:0];
OF := bool2bv(t_77 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_77 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_44;
SF := unconstrained_45;
ZF := unconstrained_46;
AF := unconstrained_47;

label_0x15d7:
RCX := PLUS_64((PLUS_64(0bv64, 5598bv64)), 0bv64)[64:0];

label_0x15de:
t1_79 := RCX;
t2_80 := RAX;
RCX := PLUS_64(RCX, t2_80);
CF := bool2bv(LT_64(RCX, t1_79));
OF := AND_1((bool2bv((t1_79[64:63]) == (t2_80[64:63]))), (XOR_1((t1_79[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_79)), t2_80)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x15e1:
RAX := RCX;

label_0x15e4:
t1_85 := RAX;
t2_86 := 8bv64;
RAX := PLUS_64(RAX, t2_86);
CF := bool2bv(LT_64(RAX, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15e8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x15ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15f2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15f8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15fd:
t_93 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x1600:
if (bv2bool(ZF)) {
  goto label_0x1603;
}

label_0x1602:
assume false;

label_0x1603:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1608:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_51);

label_0x160c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1613:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1617:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x161c:
origDEST_103 := RCX;
origCOUNT_104 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_53);

label_0x1620:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x1624:
if (bv2bool(CF)) {
  goto label_0x1627;
}

label_0x1626:
assume false;

label_0x1627:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x162c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x1630:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1632:
t_109 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5688bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5688bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5688bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5688bv64)), 1bv64))), t_109)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_109, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 5688bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))))[1:0]));
SF := t_109[32:31];
ZF := bool2bv(0bv32 == t_109);

label_0x1639:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x164b;
}

label_0x163b:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x163f:
RCX := PLUS_64((PLUS_64(0bv64, 5702bv64)), 0bv64)[64:0];

label_0x1646:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5707bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x164b"} true;
call arbitrary_func();

label_0x164b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x164f:
t1_113 := RSP;
t2_114 := 88bv64;
RSP := PLUS_64(RSP, t2_114);
CF := bool2bv(LT_64(RSP, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1653:

ra_119 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_56,origCOUNT_62,origCOUNT_98,origDEST_103,origDEST_55,origDEST_61,origDEST_97,ra_119,t1_113,t1_19,t1_29,t1_37,t1_43,t1_71,t1_79,t1_85,t2_114,t2_20,t2_30,t2_38,t2_44,t2_72,t2_80,t2_86,t_1,t_109,t_13,t_15,t_17,t_25,t_27,t_35,t_5,t_51,t_67,t_69,t_77,t_9,t_93;

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
var origCOUNT_104: bv64;
var origCOUNT_56: bv64;
var origCOUNT_62: bv64;
var origCOUNT_98: bv64;
var origDEST_103: bv64;
var origDEST_55: bv64;
var origDEST_61: bv64;
var origDEST_97: bv64;
var ra_119: bv64;
var t1_113: bv64;
var t1_19: bv64;
var t1_29: bv32;
var t1_37: bv64;
var t1_43: bv64;
var t1_71: bv32;
var t1_79: bv64;
var t1_85: bv64;
var t2_114: bv64;
var t2_20: bv64;
var t2_30: bv32;
var t2_38: bv64;
var t2_44: bv64;
var t2_72: bv32;
var t2_80: bv64;
var t2_86: bv64;
var t_1: bv64;
var t_109: bv32;
var t_13: bv64;
var t_15: bv128;
var t_17: bv128;
var t_25: bv128;
var t_27: bv64;
var t_35: bv128;
var t_5: bv32;
var t_51: bv64;
var t_67: bv128;
var t_69: bv64;
var t_77: bv128;
var t_9: bv32;
var t_93: bv64;


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
