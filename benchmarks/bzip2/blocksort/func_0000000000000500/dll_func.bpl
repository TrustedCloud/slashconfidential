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
axiom _function_addr_low == 1280bv64;
axiom _function_addr_high == 2064bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x500:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x505:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x50a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x50f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x514:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x518:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x51c:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x520:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x527;
}

label_0x522:
goto label_0x7f9;

label_0x527:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x52b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x52f:
t_9 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_9, (RAX[32:0])));
OF := AND_32((XOR_32(t_9, (RAX[32:0]))), (XOR_32(t_9, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_9)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x531:
RAX := (0bv32 ++ RCX[32:0]);

label_0x533:
t_13 := MINUS_32((RAX[32:0]), 3bv32);
CF := bool2bv(LT_32((RAX[32:0]), 3bv32));
OF := AND_32((XOR_32((RAX[32:0]), 3bv32)), (XOR_32((RAX[32:0]), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (RAX[32:0]))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x536:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x69d;
}

label_0x53c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x540:
t_17 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 4bv32));
CF := bool2bv(LT_32(t_17, 4bv32));
OF := AND_32((XOR_32(t_17, 4bv32)), (XOR_32(t_17, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_17)), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x543:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x547:
goto label_0x553;

label_0x549:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x54d:
t_21 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_21, 1bv32)), (XOR_32(t_21, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_21)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x54f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x553:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x557:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x55b:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x69d;
}

label_0x561:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x566:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x56b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x56e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x572:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)))));

label_0x577:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x57c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x57f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0x583:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x587:
t1_29 := RAX[32:0];
t2_30 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_30));
CF := bool2bv(LT_32((RAX[32:0]), t1_29));
OF := AND_1((bool2bv((t1_29[32:31]) == (t2_30[32:31]))), (XOR_1((t1_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_29)), t2_30)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x58a:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x58d:
goto label_0x598;

label_0x58f:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x592:
t1_35 := RAX[32:0];
t2_36 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_36));
CF := bool2bv(LT_32((RAX[32:0]), t1_35));
OF := AND_1((bool2bv((t1_35[32:31]) == (t2_36[32:31]))), (XOR_1((t1_35[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_35)), t2_36)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x595:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x598:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x59c:
t_41 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0x59f:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x63a;
}

label_0x5a5:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x5a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x5ae:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x5b1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x5b6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x5b9:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0x5bd:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x63a;
}

label_0x5bf:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x5c3:
origDEST_49 := RAX;
origCOUNT_50 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, RSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_2);

label_0x5c7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x5cc:
t1_55 := RCX;
t2_56 := RAX;
RCX := PLUS_64(RCX, t2_56);
CF := bool2bv(LT_64(RCX, t1_55));
OF := AND_1((bool2bv((t1_55[64:63]) == (t2_56[64:63]))), (XOR_1((t1_55[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_55)), t2_56)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5cf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RCX);

label_0x5d4:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x5d7:
t_61 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 4bv32));
CF := bool2bv(LT_32(t_61, 4bv32));
OF := AND_32((XOR_32(t_61, 4bv32)), (XOR_32(t_61, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_61)), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5da:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x5dc:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, RSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_4);

label_0x5e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x5e5:
t1_71 := RCX;
t2_72 := RAX;
RCX := PLUS_64(RCX, t2_72);
CF := bool2bv(LT_64(RCX, t1_71));
OF := AND_1((bool2bv((t1_71[64:63]) == (t2_72[64:63]))), (XOR_1((t1_71[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_71)), t2_72)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5e8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RCX);

label_0x5ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x5f2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5f8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5fd:
t_79 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))))[1:0]));
SF := t_79[64:63];
ZF := bool2bv(0bv64 == t_79);

label_0x600:
if (bv2bool(ZF)) {
  goto label_0x603;
}

label_0x602:
assume false;

label_0x603:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x608:
origDEST_83 := RAX;
origCOUNT_84 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_8);

label_0x60c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x613:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x617:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x61c:
origDEST_89 := RCX;
origCOUNT_90 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, LSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), origDEST_89[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_10);

label_0x620:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_11;
SF := unconstrained_12;
AF := unconstrained_13;
PF := unconstrained_14;

label_0x624:
if (bv2bool(CF)) {
  goto label_0x627;
}

label_0x626:
assume false;

label_0x627:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x62c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x631:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x633:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x635:
goto label_0x58f;

label_0x63a:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x63d:
t_95 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 4bv32));
CF := bool2bv(LT_32(t_95, 4bv32));
OF := AND_32((XOR_32(t_95, 4bv32)), (XOR_32(t_95, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_95)), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x640:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x642:
origDEST_99 := RAX;
origCOUNT_100 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), CF, RSHIFT_64(origDEST_99, (MINUS_64(64bv64, origCOUNT_100)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_100 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), AF, unconstrained_16);

label_0x646:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x64b:
t1_105 := RCX;
t2_106 := RAX;
RCX := PLUS_64(RCX, t2_106);
CF := bool2bv(LT_64(RCX, t1_105));
OF := AND_1((bool2bv((t1_105[64:63]) == (t2_106[64:63]))), (XOR_1((t1_105[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_105)), t2_106)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x64e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RCX);

label_0x653:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x658:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x65e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x663:
t_113 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))))[1:0]));
SF := t_113[64:63];
ZF := bool2bv(0bv64 == t_113);

label_0x666:
if (bv2bool(ZF)) {
  goto label_0x669;
}

label_0x668:
assume false;

label_0x669:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x66e:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_20);

label_0x672:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x679:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x67d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x682:
origDEST_123 := RCX;
origCOUNT_124 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), CF, LSHIFT_64(origDEST_123, (MINUS_64(64bv64, origCOUNT_124)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_124 == 1bv64)), origDEST_123[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), AF, unconstrained_22);

label_0x686:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_23;
SF := unconstrained_24;
AF := unconstrained_25;
PF := unconstrained_26;

label_0x68a:
if (bv2bool(CF)) {
  goto label_0x68d;
}

label_0x68c:
assume false;

label_0x68d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x692:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x696:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x698:
goto label_0x549;

label_0x69d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x6a1:
t_129 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_129, 1bv32)), (XOR_32(t_129, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_129)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6a3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x6a7:
goto label_0x6b3;

label_0x6a9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x6ad:
t_133 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_133, 1bv32)), (XOR_32(t_133, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_133)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6af:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x6b3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x6b7:
t_137 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_137)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_137, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))))[1:0]));
SF := t_137[32:31];
ZF := bool2bv(0bv32 == t_137);

label_0x6bb:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x7f9;
}

label_0x6c1:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x6c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x6cb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x6ce:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x6d2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)))));

label_0x6d7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x6dc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x6df:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0x6e3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x6e7:
t_141 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_141[32:31]) == (1bv32[32:31]))), (XOR_1((t_141[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_141)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6e9:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x6ec:
goto label_0x6f6;

label_0x6ee:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x6f1:
t_145 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_145[32:31]) == (1bv32[32:31]))), (XOR_1((t_145[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6f3:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x6f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x6fa:
t_149 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_149)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_149, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))))[1:0]));
SF := t_149[32:31];
ZF := bool2bv(0bv32 == t_149);

label_0x6fd:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x797;
}

label_0x703:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x707:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x70c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x70f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x714:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x717:
t_153 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))), t_153)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_153, (LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))))[1:0]));
SF := t_153[32:31];
ZF := bool2bv(0bv32 == t_153);

label_0x71b:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x797;
}

label_0x71d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x721:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, RSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_28);

label_0x725:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x72a:
t1_163 := RCX;
t2_164 := RAX;
RCX := PLUS_64(RCX, t2_164);
CF := bool2bv(LT_64(RCX, t1_163));
OF := AND_1((bool2bv((t1_163[64:63]) == (t2_164[64:63]))), (XOR_1((t1_163[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_163)), t2_164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x72d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RCX);

label_0x732:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x735:
t_169 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_169, 1bv32)), (XOR_32(t_169, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_169)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x737:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x739:
origDEST_173 := RAX;
origCOUNT_174 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), CF, RSHIFT_64(origDEST_173, (MINUS_64(64bv64, origCOUNT_174)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), AF, unconstrained_30);

label_0x73d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x742:
t1_179 := RCX;
t2_180 := RAX;
RCX := PLUS_64(RCX, t2_180);
CF := bool2bv(LT_64(RCX, t1_179));
OF := AND_1((bool2bv((t1_179[64:63]) == (t2_180[64:63]))), (XOR_1((t1_179[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_179)), t2_180)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x745:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0x74a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x74f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x755:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x75a:
t_187 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))))[1:0]));
SF := t_187[64:63];
ZF := bool2bv(0bv64 == t_187);

label_0x75d:
if (bv2bool(ZF)) {
  goto label_0x760;
}

label_0x75f:
assume false;

label_0x760:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x765:
origDEST_191 := RAX;
origCOUNT_192 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_34);

label_0x769:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x770:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x774:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x779:
origDEST_197 := RCX;
origCOUNT_198 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), CF, LSHIFT_64(origDEST_197, (MINUS_64(64bv64, origCOUNT_198)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_198 == 1bv64)), origDEST_197[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), AF, unconstrained_36);

label_0x77d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x781:
if (bv2bool(CF)) {
  goto label_0x784;
}

label_0x783:
assume false;

label_0x784:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x789:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x78e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x790:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x792:
goto label_0x6ee;

label_0x797:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x79a:
t_203 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_203, 1bv32)), (XOR_32(t_203, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_203)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x79c:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x79e:
origDEST_207 := RAX;
origCOUNT_208 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, RSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_42);

label_0x7a2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x7a7:
t1_213 := RCX;
t2_214 := RAX;
RCX := PLUS_64(RCX, t2_214);
CF := bool2bv(LT_64(RCX, t1_213));
OF := AND_1((bool2bv((t1_213[64:63]) == (t2_214[64:63]))), (XOR_1((t1_213[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_213)), t2_214)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RCX);

label_0x7af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7b4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7ba:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7bf:
t_221 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))))[1:0]));
SF := t_221[64:63];
ZF := bool2bv(0bv64 == t_221);

label_0x7c2:
if (bv2bool(ZF)) {
  goto label_0x7c5;
}

label_0x7c4:
assume false;

label_0x7c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7ca:
origDEST_225 := RAX;
origCOUNT_226 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), CF, LSHIFT_64(origDEST_225, (MINUS_64(64bv64, origCOUNT_226)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_226 == 1bv64)), origDEST_225[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), AF, unconstrained_46);

label_0x7ce:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7d5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7de:
origDEST_231 := RCX;
origCOUNT_232 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), CF, LSHIFT_64(origDEST_231, (MINUS_64(64bv64, origCOUNT_232)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_232 == 1bv64)), origDEST_231[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), AF, unconstrained_48);

label_0x7e2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x7e6:
if (bv2bool(CF)) {
  goto label_0x7e9;
}

label_0x7e8:
assume false;

label_0x7e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7ee:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x7f2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7f4:
goto label_0x6a9;

label_0x7f9:
t1_237 := RSP;
t2_238 := 72bv64;
RSP := PLUS_64(RSP, t2_238);
CF := bool2bv(LT_64(RSP, t1_237));
OF := AND_1((bool2bv((t1_237[64:63]) == (t2_238[64:63]))), (XOR_1((t1_237[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_237)), t2_238)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x7fd:

ra_243 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_100,origCOUNT_118,origCOUNT_124,origCOUNT_158,origCOUNT_174,origCOUNT_192,origCOUNT_198,origCOUNT_208,origCOUNT_226,origCOUNT_232,origCOUNT_50,origCOUNT_66,origCOUNT_84,origCOUNT_90,origDEST_117,origDEST_123,origDEST_157,origDEST_173,origDEST_191,origDEST_197,origDEST_207,origDEST_225,origDEST_231,origDEST_49,origDEST_65,origDEST_83,origDEST_89,origDEST_99,ra_243,t1_105,t1_163,t1_179,t1_213,t1_237,t1_29,t1_35,t1_55,t1_71,t2_106,t2_164,t2_180,t2_214,t2_238,t2_30,t2_36,t2_56,t2_72,t_1,t_113,t_129,t_13,t_133,t_137,t_141,t_145,t_149,t_153,t_169,t_17,t_187,t_203,t_21,t_221,t_25,t_41,t_45,t_5,t_61,t_79,t_9,t_95;

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
var origCOUNT_100: bv64;
var origCOUNT_118: bv64;
var origCOUNT_124: bv64;
var origCOUNT_158: bv64;
var origCOUNT_174: bv64;
var origCOUNT_192: bv64;
var origCOUNT_198: bv64;
var origCOUNT_208: bv64;
var origCOUNT_226: bv64;
var origCOUNT_232: bv64;
var origCOUNT_50: bv64;
var origCOUNT_66: bv64;
var origCOUNT_84: bv64;
var origCOUNT_90: bv64;
var origDEST_117: bv64;
var origDEST_123: bv64;
var origDEST_157: bv64;
var origDEST_173: bv64;
var origDEST_191: bv64;
var origDEST_197: bv64;
var origDEST_207: bv64;
var origDEST_225: bv64;
var origDEST_231: bv64;
var origDEST_49: bv64;
var origDEST_65: bv64;
var origDEST_83: bv64;
var origDEST_89: bv64;
var origDEST_99: bv64;
var ra_243: bv64;
var t1_105: bv64;
var t1_163: bv64;
var t1_179: bv64;
var t1_213: bv64;
var t1_237: bv64;
var t1_29: bv32;
var t1_35: bv32;
var t1_55: bv64;
var t1_71: bv64;
var t2_106: bv64;
var t2_164: bv64;
var t2_180: bv64;
var t2_214: bv64;
var t2_238: bv64;
var t2_30: bv32;
var t2_36: bv32;
var t2_56: bv64;
var t2_72: bv64;
var t_1: bv64;
var t_113: bv64;
var t_129: bv32;
var t_13: bv32;
var t_133: bv32;
var t_137: bv32;
var t_141: bv32;
var t_145: bv32;
var t_149: bv32;
var t_153: bv32;
var t_169: bv32;
var t_17: bv32;
var t_187: bv64;
var t_203: bv32;
var t_21: bv32;
var t_221: bv64;
var t_25: bv32;
var t_41: bv32;
var t_45: bv32;
var t_5: bv32;
var t_61: bv32;
var t_79: bv64;
var t_9: bv32;
var t_95: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1280bv64);
axiom policy(2064bv64);
axiom policy(6688bv64);
axiom policy(11152bv64);
axiom policy(14480bv64);
axiom policy(16016bv64);
axiom policy(16160bv64);
axiom policy(25760bv64);
