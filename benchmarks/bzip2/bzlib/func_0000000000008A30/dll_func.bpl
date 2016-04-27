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
axiom _function_addr_low == 35376bv64;
axiom _function_addr_high == 36064bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x8a30:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x8a35:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x8a39:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x8a3e:
mem := STORE_LE_8(mem, PLUS_64(RSP, 33bv64), 0bv8);

label_0x8a43:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x8a48:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 48bv64));

label_0x8a4c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x8a51:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x8a53:
t_5 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x8a56:
if (bv2bool(ZF)) {
  goto label_0x8ca8;
}

label_0x8a5c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8a61:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x8a65:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8b51;
}

label_0x8a6b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8a70:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35445bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8a75"} true;
call arbitrary_func();

label_0x8a75:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x8a78:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 33bv64))));

label_0x8a7d:
RCX := (0bv32 ++ OR_32((RCX[32:0]), (RAX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x8a7f:
RAX := (0bv32 ++ RCX[32:0]);

label_0x8a81:
mem := STORE_LE_8(mem, PLUS_64(RSP, 33bv64), RAX[32:0][8:0]);

label_0x8a85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8a8a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8a8f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 116bv64)));

label_0x8a92:
t_15 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), t_15)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_15, (LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)), 2bv32)), (XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)), 2bv32)), (XOR_32((RSHIFT_32(t_15, 4bv32)), t_15)))))[1:0]));
SF := t_15[32:31];
ZF := bool2bv(0bv32 == t_15);

label_0x8a95:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x8a9c;
}

label_0x8a97:
goto label_0x8ca8;

label_0x8a9c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8aa1:
t_19 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_19)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_19, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_19, 4bv32)), t_19)), 2bv32)), (XOR_32((RSHIFT_32(t_19, 4bv32)), t_19)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_19, 4bv32)), t_19)), 2bv32)), (XOR_32((RSHIFT_32(t_19, 4bv32)), t_19)))))[1:0]));
SF := t_19[32:31];
ZF := bool2bv(0bv32 == t_19);

label_0x8aa5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8ac8;
}

label_0x8aa7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8aac:
t_23 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_23)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_23, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_23, 4bv32)), t_23)), 2bv32)), (XOR_32((RSHIFT_32(t_23, 4bv32)), t_23)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_23, 4bv32)), t_23)), 2bv32)), (XOR_32((RSHIFT_32(t_23, 4bv32)), t_23)))))[1:0]));
SF := t_23[32:31];
ZF := bool2bv(0bv32 == t_23);

label_0x8ab0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8ac8;
}

label_0x8ab2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8ab7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35516bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8abc"} true;
call arbitrary_func();

label_0x8abc:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x8abf:
t_27 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)), 2bv32)), (XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)), 2bv32)), (XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)))))[1:0]));
SF := t_27[32:31];
ZF := bool2bv(0bv32 == t_27);

label_0x8ac1:
if (bv2bool(ZF)) {
  goto label_0x8ac8;
}

label_0x8ac3:
goto label_0x8ca8;

label_0x8ac8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8acd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35538bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8ad2"} true;
call arbitrary_func();

label_0x8ad2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8ad7:
t1_31 := RAX;
t2_32 := 12bv64;
RAX := PLUS_64(RAX, t2_32);
CF := bool2bv(LT_64(RAX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8adb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x8ae0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x8ae5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8aeb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8af0:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x8af3:
if (bv2bool(ZF)) {
  goto label_0x8af6;
}

label_0x8af5:
assume false;

label_0x8af6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x8afb:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_7);

label_0x8aff:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8b06:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8b0a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x8b0f:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_9);

label_0x8b13:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_10;
SF := unconstrained_11;
AF := unconstrained_12;
PF := unconstrained_13;

label_0x8b17:
if (bv2bool(CF)) {
  goto label_0x8b1a;
}

label_0x8b19:
assume false;

label_0x8b1a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x8b1f:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0x8b25:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b2a:
t_55 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_55)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_55, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))))[1:0]));
SF := t_55[32:31];
ZF := bool2bv(0bv32 == t_55);

label_0x8b2e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8b51;
}

label_0x8b30:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b35:
t_59 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_59)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_59, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))))[1:0]));
SF := t_59[32:31];
ZF := bool2bv(0bv32 == t_59);

label_0x8b39:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8b51;
}

label_0x8b3b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b40:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35653bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8b45"} true;
call arbitrary_func();

label_0x8b45:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x8b48:
t_63 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x8b4a:
if (bv2bool(ZF)) {
  goto label_0x8b51;
}

label_0x8b4c:
goto label_0x8ca8;

label_0x8b51:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b56:
t_67 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))), t_67)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_67, (LOAD_LE_32(mem, PLUS_64(RAX, 12bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))))[1:0]));
SF := t_67[32:31];
ZF := bool2bv(0bv32 == t_67);

label_0x8b5a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8ca3;
}

label_0x8b60:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b65:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35690bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8b6a"} true;
call arbitrary_func();

label_0x8b6a:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x8b6d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x8b72:
RCX := (0bv32 ++ OR_32((RCX[32:0]), (RAX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x8b74:
RAX := (0bv32 ++ RCX[32:0]);

label_0x8b76:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0x8b7a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b7f:
t_73 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_73)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_73, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x8b83:
if (bv2bool(ZF)) {
  goto label_0x8c20;
}

label_0x8b89:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b8e:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x8b92:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8c20;
}

label_0x8b98:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8b9d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35746bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8ba2"} true;
call arbitrary_func();

label_0x8ba2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8ba7:
t_81 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_81)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_81, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))))[1:0]));
SF := t_81[32:31];
ZF := bool2bv(0bv32 == t_81);

label_0x8bab:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8bb4;
}

label_0x8bad:
mem := STORE_LE_8(mem, PLUS_64(RSP, 34bv64), 1bv8);

label_0x8bb2:
goto label_0x8bb9;

label_0x8bb4:
mem := STORE_LE_8(mem, PLUS_64(RSP, 34bv64), 0bv8);

label_0x8bb9:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 34bv64))));

label_0x8bbe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8bc3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35784bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8bc8"} true;
call arbitrary_func();

label_0x8bc8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8bcd:
t1_85 := RAX;
t2_86 := 12bv64;
RAX := PLUS_64(RAX, t2_86);
CF := bool2bv(LT_64(RAX, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8bd1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x8bd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8bdb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8be1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8be6:
t_93 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x8be9:
if (bv2bool(ZF)) {
  goto label_0x8bec;
}

label_0x8beb:
assume false;

label_0x8bec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8bf1:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_19);

label_0x8bf5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8bfc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8c00:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8c05:
origDEST_103 := RCX;
origCOUNT_104 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_21);

label_0x8c09:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_22;
SF := unconstrained_23;
AF := unconstrained_24;
PF := unconstrained_25;

label_0x8c0d:
if (bv2bool(CF)) {
  goto label_0x8c10;
}

label_0x8c0f:
assume false;

label_0x8c10:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x8c15:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x8c1b:
goto label_0x8ca3;

label_0x8c20:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8c25:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8c2a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 112bv64)));

label_0x8c2d:
t_109 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), t_109)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_109, (LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))))[1:0]));
SF := t_109[32:31];
ZF := bool2bv(0bv32 == t_109);

label_0x8c30:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x8c93;
}

label_0x8c32:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_26;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x8c34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8c39:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 35902bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x8c3e"} true;
call arbitrary_func();

label_0x8c3e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8c43:
t1_113 := RAX;
t2_114 := 12bv64;
RAX := PLUS_64(RAX, t2_114);
CF := bool2bv(LT_64(RAX, t1_113));
OF := AND_1((bool2bv((t1_113[64:63]) == (t2_114[64:63]))), (XOR_1((t1_113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_113)), t2_114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8c47:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x8c4c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8c51:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8c57:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8c5c:
t_121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x8c5f:
if (bv2bool(ZF)) {
  goto label_0x8c62;
}

label_0x8c61:
assume false;

label_0x8c62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8c67:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_30);

label_0x8c6b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8c72:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8c76:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8c7b:
origDEST_131 := RCX;
origCOUNT_132 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_32);

label_0x8c7f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x8c83:
if (bv2bool(CF)) {
  goto label_0x8c86;
}

label_0x8c85:
assume false;

label_0x8c86:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x8c8b:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x8c91:
goto label_0x8ca3;

label_0x8c93:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x8c98:
RAX := LOAD_LE_64(mem, RAX);

label_0x8c9b:
t_137 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_137)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_137, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))))[1:0]));
SF := t_137[32:31];
ZF := bool2bv(0bv32 == t_137);

label_0x8c9f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8ca3;
}

label_0x8ca1:
goto label_0x8ca8;

label_0x8ca3:
goto label_0x8a51;

label_0x8ca8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x8cad:
t_141 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))))[1:0]));
SF := t_141[32:31];
ZF := bool2bv(0bv32 == t_141);

label_0x8caf:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8cc4;
}

label_0x8cb1:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 33bv64))));

label_0x8cb6:
t_145 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0x8cb8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x8cc4;
}

label_0x8cba:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x8cc2:
goto label_0x8ccc;

label_0x8cc4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0x8ccc:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 36bv64))));

label_0x8cd1:
t1_149 := RSP;
t2_150 := 88bv64;
RSP := PLUS_64(RSP, t2_150);
CF := bool2bv(LT_64(RSP, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x8cd5:

ra_155 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_126,origCOUNT_132,origCOUNT_44,origCOUNT_50,origCOUNT_98,origDEST_103,origDEST_125,origDEST_131,origDEST_43,origDEST_49,origDEST_97,ra_155,t1_113,t1_149,t1_31,t1_85,t2_114,t2_150,t2_32,t2_86,t_1,t_109,t_121,t_137,t_141,t_145,t_15,t_19,t_23,t_27,t_39,t_5,t_55,t_59,t_63,t_67,t_73,t_77,t_81,t_9,t_93;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_104: bv64;
var origCOUNT_126: bv64;
var origCOUNT_132: bv64;
var origCOUNT_44: bv64;
var origCOUNT_50: bv64;
var origCOUNT_98: bv64;
var origDEST_103: bv64;
var origDEST_125: bv64;
var origDEST_131: bv64;
var origDEST_43: bv64;
var origDEST_49: bv64;
var origDEST_97: bv64;
var ra_155: bv64;
var t1_113: bv64;
var t1_149: bv64;
var t1_31: bv64;
var t1_85: bv64;
var t2_114: bv64;
var t2_150: bv64;
var t2_32: bv64;
var t2_86: bv64;
var t_1: bv64;
var t_109: bv32;
var t_121: bv64;
var t_137: bv32;
var t_141: bv32;
var t_145: bv32;
var t_15: bv32;
var t_19: bv32;
var t_23: bv32;
var t_27: bv32;
var t_39: bv64;
var t_5: bv32;
var t_55: bv32;
var t_59: bv32;
var t_63: bv32;
var t_67: bv32;
var t_73: bv32;
var t_77: bv32;
var t_81: bv32;
var t_9: bv32;
var t_93: bv64;


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
