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
axiom _function_addr_low == 5408bv64;
axiom _function_addr_high == 6768bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1520:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x1525:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x152a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x152e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1533:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x153a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1542:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 170bv64))));

label_0x1549:
t_5 := MINUS_32((RAX[32:0]), 65535bv32);
CF := bool2bv(LT_32((RAX[32:0]), 65535bv32));
OF := AND_32((XOR_32((RAX[32:0]), 65535bv32)), (XOR_32((RAX[32:0]), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (RAX[32:0]))), 65535bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x154e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15f3;
}

label_0x1554:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x155c:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x155e:
RCX := (0bv32 ++ 1bv32);

label_0x1563:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RCX[32:0]);

label_0x1567:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x156a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x156e:
origDEST_9 := RAX[32:0];
origCOUNT_10 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), CF, RSHIFT_32(origDEST_9, (MINUS_32(32bv32, origCOUNT_10)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_10 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), AF, unconstrained_2);

label_0x1570:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1578:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4bv64)));

label_0x157b:
origDEST_15 := RAX[32:0];
origCOUNT_16 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), CF, RSHIFT_32(origDEST_15, (MINUS_32(32bv32, origCOUNT_16)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv32)), AF, unconstrained_4);

label_0x157d:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x157f:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_6);

label_0x1583:
R8 := RAX;

label_0x1586:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_7;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1588:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1590:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 128bv64));

label_0x1597:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5532bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x159c"} true;
call arbitrary_func();

label_0x159c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x15a4:
t1_27 := RAX;
t2_28 := 170bv64;
RAX := PLUS_64(RAX, t2_28);
CF := bool2bv(LT_64(RAX, t1_27));
OF := AND_1((bool2bv((t1_27[64:63]) == (t2_28[64:63]))), (XOR_1((t1_27[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_27)), t2_28)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x15af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15b4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15ba:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15bf:
t_35 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))))[1:0]));
SF := t_35[64:63];
ZF := bool2bv(0bv64 == t_35);

label_0x15c2:
if (bv2bool(ZF)) {
  goto label_0x15c5;
}

label_0x15c4:
assume false;

label_0x15c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15ca:
origDEST_39 := RAX;
origCOUNT_40 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), CF, LSHIFT_64(origDEST_39, (MINUS_64(64bv64, origCOUNT_40)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv64)), origDEST_39[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), AF, unconstrained_11);

label_0x15ce:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x15d5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x15d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15de:
origDEST_45 := RCX;
origCOUNT_46 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), CF, LSHIFT_64(origDEST_45, (MINUS_64(64bv64, origCOUNT_46)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_46 == 1bv64)), origDEST_45[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), AF, unconstrained_13);

label_0x15e2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_14;
SF := unconstrained_15;
AF := unconstrained_16;
PF := unconstrained_17;

label_0x15e6:
if (bv2bool(CF)) {
  goto label_0x15e9;
}

label_0x15e8:
assume false;

label_0x15e9:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_18;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x15eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15f0:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x15f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x15fb:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 170bv64))));

label_0x1602:
t_51 := RAX[32:0][16:0];
RAX := (RAX[64:16]) ++ (PLUS_16((RAX[32:0][16:0]), 1bv16));
OF := AND_1((bool2bv((t_51[16:15]) == (1bv16[16:15]))), (XOR_1((t_51[16:15]), (RAX[32:0][16:0][16:15]))));
AF := bool2bv(16bv16 == (AND_16(16bv16, (XOR_16((XOR_16((RAX[32:0][16:0]), t_51)), 1bv16)))));
PF := NOT_1((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))), 1bv16)), (XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))))[1:0]));
SF := RAX[32:0][16:0][16:15];
ZF := bool2bv(0bv16 == (RAX[32:0][16:0]));

label_0x1605:
mem := STORE_LE_16(mem, PLUS_64(RSP, 40bv64), RAX[32:0][16:0]);

label_0x160a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1612:
t1_55 := RAX;
t2_56 := 170bv64;
RAX := PLUS_64(RAX, t2_56);
CF := bool2bv(LT_64(RAX, t1_55));
OF := AND_1((bool2bv((t1_55[64:63]) == (t2_56[64:63]))), (XOR_1((t1_55[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_55)), t2_56)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1618:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x161d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1622:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1628:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x162d:
t_63 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))))[1:0]));
SF := t_63[64:63];
ZF := bool2bv(0bv64 == t_63);

label_0x1630:
if (bv2bool(ZF)) {
  goto label_0x1633;
}

label_0x1632:
assume false;

label_0x1633:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1638:
origDEST_67 := RAX;
origCOUNT_68 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_22);

label_0x163c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1643:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1647:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x164c:
origDEST_73 := RCX;
origCOUNT_74 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_24);

label_0x1650:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x1654:
if (bv2bool(CF)) {
  goto label_0x1657;
}

label_0x1656:
assume false;

label_0x1657:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x165c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 40bv64))));

label_0x1661:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1664:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x166c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x1673:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x167b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5760bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1680"} true;
call arbitrary_func();

label_0x1680:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x1684:
RAX := (0bv32 ++ 4bv32);

label_0x1689:
t_79 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_79[64:0];
OF := bool2bv(t_79 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_79 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_29;
SF := unconstrained_30;
ZF := unconstrained_31;
AF := unconstrained_32;

label_0x168d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1695:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 136bv64));

label_0x169c:
t1_81 := RCX;
t2_82 := RAX;
RCX := PLUS_64(RCX, t2_82);
CF := bool2bv(LT_64(RCX, t1_81));
OF := AND_1((bool2bv((t1_81[64:63]) == (t2_82[64:63]))), (XOR_1((t1_81[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_81)), t2_82)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x169f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0x16a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16a9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16af:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x16b4:
t_89 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))))[1:0]));
SF := t_89[64:63];
ZF := bool2bv(0bv64 == t_89);

label_0x16b7:
if (bv2bool(ZF)) {
  goto label_0x16ba;
}

label_0x16b9:
assume false;

label_0x16ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16bf:
origDEST_93 := RAX;
origCOUNT_94 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_36);

label_0x16c3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x16ca:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x16ce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16d3:
origDEST_99 := RCX;
origCOUNT_100 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), CF, LSHIFT_64(origDEST_99, (MINUS_64(64bv64, origCOUNT_100)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_100 == 1bv64)), origDEST_99[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), AF, unconstrained_38);

label_0x16d7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x16db:
if (bv2bool(CF)) {
  goto label_0x16de;
}

label_0x16dd:
assume false;

label_0x16de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16e3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 124bv64)));

label_0x16e7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x16e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x16f1:
t1_105 := RAX;
t2_106 := 170bv64;
RAX := PLUS_64(RAX, t2_106);
CF := bool2bv(LT_64(RAX, t1_105));
OF := AND_1((bool2bv((t1_105[64:63]) == (t2_106[64:63]))), (XOR_1((t1_105[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_105)), t2_106)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16f7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x16ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1707:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x170a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x170d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x1714:
origDEST_111 := RAX[32:0];
origCOUNT_112 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), CF, RSHIFT_32(origDEST_111, (MINUS_32(32bv32, origCOUNT_112)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv32)), AF, unconstrained_44);

label_0x1716:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x171d:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x171f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1727:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 128bv64));

label_0x172e:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1732:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1737:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x173c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1742:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1747:
t_121 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x174a:
if (bv2bool(ZF)) {
  goto label_0x174d;
}

label_0x174c:
assume false;

label_0x174d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1752:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_49);

label_0x1756:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x175d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1761:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1766:
origDEST_131 := RCX;
origCOUNT_132 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_51);

label_0x176a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_52;
SF := unconstrained_53;
AF := unconstrained_54;
PF := unconstrained_55;

label_0x176e:
if (bv2bool(CF)) {
  goto label_0x1771;
}

label_0x1770:
assume false;

label_0x1771:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1776:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x177e:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1781:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1784:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x178c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x178f:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1792:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x1799:
origDEST_137 := RAX[32:0];
origCOUNT_138 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), CF, RSHIFT_32(origDEST_137, (MINUS_32(32bv32, origCOUNT_138)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv32)), AF, unconstrained_57);

label_0x179b:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x17a2:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x17a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x17ac:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 128bv64));

label_0x17b3:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x17b7:
t1_145 := RAX;
t2_146 := 2bv64;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17bb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x17c0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x17c5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17cb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17d0:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0x17d3:
if (bv2bool(ZF)) {
  goto label_0x17d6;
}

label_0x17d5:
assume false;

label_0x17d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x17db:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_62);

label_0x17df:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x17e6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17ea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x17ef:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_64);

label_0x17f3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_65;
SF := unconstrained_66;
AF := unconstrained_67;
PF := unconstrained_68;

label_0x17f7:
if (bv2bool(CF)) {
  goto label_0x17fa;
}

label_0x17f9:
assume false;

label_0x17fa:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_69;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x17fc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1801:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x1804:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x1809:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0x1811:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1819:
t1_169 := RAX;
t2_170 := 160bv64;
RAX := PLUS_64(RAX, t2_170);
CF := bool2bv(LT_64(RAX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x181f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x1824:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1829:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_70;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x182f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1834:
t_177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))))[1:0]));
SF := t_177[64:63];
ZF := bool2bv(0bv64 == t_177);

label_0x1837:
if (bv2bool(ZF)) {
  goto label_0x183a;
}

label_0x1839:
assume false;

label_0x183a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x183f:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_73);

label_0x1843:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x184a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x184e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1853:
origDEST_187 := RCX;
origCOUNT_188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_74));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_75);

label_0x1857:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_76;
SF := unconstrained_77;
AF := unconstrained_78;
PF := unconstrained_79;

label_0x185b:
if (bv2bool(CF)) {
  goto label_0x185e;
}

label_0x185d:
assume false;

label_0x185e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1863:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x1866:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x186e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x1875:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x187d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6274bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1882"} true;
call arbitrary_func();

label_0x1882:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), RAX[32:0]);

label_0x1889:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1891:
t1_193 := RAX;
t2_194 := 164bv64;
RAX := PLUS_64(RAX, t2_194);
CF := bool2bv(LT_64(RAX, t1_193));
OF := AND_1((bool2bv((t1_193[64:63]) == (t2_194[64:63]))), (XOR_1((t1_193[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_193)), t2_194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1897:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x189c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x18a1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_80;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18a7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x18ac:
t_201 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))))[1:0]));
SF := t_201[64:63];
ZF := bool2bv(0bv64 == t_201);

label_0x18af:
if (bv2bool(ZF)) {
  goto label_0x18b2;
}

label_0x18b1:
assume false;

label_0x18b2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x18b7:
origDEST_205 := RAX;
origCOUNT_206 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_83);

label_0x18bb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x18c2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x18c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x18cb:
origDEST_211 := RCX;
origCOUNT_212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), CF, LSHIFT_64(origDEST_211, (MINUS_64(64bv64, origCOUNT_212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv64)), origDEST_211[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), AF, unconstrained_85);

label_0x18cf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_86;
SF := unconstrained_87;
AF := unconstrained_88;
PF := unconstrained_89;

label_0x18d3:
if (bv2bool(CF)) {
  goto label_0x18d6;
}

label_0x18d5:
assume false;

label_0x18d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x18db:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x18e2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x18e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x18ec:
t1_217 := RAX;
t2_218 := 168bv64;
RAX := PLUS_64(RAX, t2_218);
CF := bool2bv(LT_64(RAX, t1_217));
OF := AND_1((bool2bv((t1_217[64:63]) == (t2_218[64:63]))), (XOR_1((t1_217[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_217)), t2_218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18f2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x18f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x18fc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1902:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1907:
t_225 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))))[1:0]));
SF := t_225[64:63];
ZF := bool2bv(0bv64 == t_225);

label_0x190a:
if (bv2bool(ZF)) {
  goto label_0x190d;
}

label_0x190c:
assume false;

label_0x190d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1912:
origDEST_229 := RAX;
origCOUNT_230 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), CF, LSHIFT_64(origDEST_229, (MINUS_64(64bv64, origCOUNT_230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_230 == 1bv64)), origDEST_229[64:63], unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), AF, unconstrained_93);

label_0x1916:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x191d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1921:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1926:
origDEST_235 := RCX;
origCOUNT_236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), CF, LSHIFT_64(origDEST_235, (MINUS_64(64bv64, origCOUNT_236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv64)), origDEST_235[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), AF, unconstrained_95);

label_0x192a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_96;
SF := unconstrained_97;
AF := unconstrained_98;
PF := unconstrained_99;

label_0x192e:
if (bv2bool(CF)) {
  goto label_0x1931;
}

label_0x1930:
assume false;

label_0x1931:
RAX := (0bv32 ++ 1bv32);

label_0x1936:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x193b:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x193e:
t_241 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_241)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_241, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_241, 4bv32)), t_241)), 2bv32)), (XOR_32((RSHIFT_32(t_241, 4bv32)), t_241)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_241, 4bv32)), t_241)), 2bv32)), (XOR_32((RSHIFT_32(t_241, 4bv32)), t_241)))))[1:0]));
SF := t_241[32:31];
ZF := bool2bv(0bv32 == t_241);

label_0x1943:
if (bv2bool(ZF)) {
  goto label_0x1a53;
}

label_0x1949:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1951:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 160bv64))));

label_0x1958:
t_245 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))))[1:0]));
SF := t_245[32:31];
ZF := bool2bv(0bv32 == t_245);

label_0x195a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1a53;
}

label_0x1960:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x1965:
t_249 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_249, 4bv32)), t_249)), 2bv32)), (XOR_32((RSHIFT_32(t_249, 4bv32)), t_249)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_249, 4bv32)), t_249)), 2bv32)), (XOR_32((RSHIFT_32(t_249, 4bv32)), t_249)))))[1:0]));
SF := t_249[32:31];
ZF := bool2bv(0bv32 == t_249);

label_0x1967:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x19a4;
}

label_0x1969:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1971:
R9 := LOAD_LE_64(mem, PLUS_64(RAX, 144bv64));

label_0x1978:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x197d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1985:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 136bv64));

label_0x198c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1994:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6553bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1999"} true;
call arbitrary_func();

label_0x1999:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x199d:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x19a2:
goto label_0x19dd;

label_0x19a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19ac:
R9 := LOAD_LE_64(mem, PLUS_64(RAX, 136bv64));

label_0x19b3:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x19b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19c0:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 144bv64));

label_0x19c7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19cf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6612bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x19d4"} true;
call arbitrary_func();

label_0x19d4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x19d8:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x19dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19e5:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 168bv64))));

label_0x19ec:
t_253 := RAX[32:0][16:0];
RAX := (RAX[64:16]) ++ (PLUS_16((RAX[32:0][16:0]), 1bv16));
OF := AND_1((bool2bv((t_253[16:15]) == (1bv16[16:15]))), (XOR_1((t_253[16:15]), (RAX[32:0][16:0][16:15]))));
AF := bool2bv(16bv16 == (AND_16(16bv16, (XOR_16((XOR_16((RAX[32:0][16:0]), t_253)), 1bv16)))));
PF := NOT_1((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))), 1bv16)), (XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))))[1:0]));
SF := RAX[32:0][16:0][16:15];
ZF := bool2bv(0bv16 == (RAX[32:0][16:0]));

label_0x19ef:
mem := STORE_LE_16(mem, PLUS_64(RSP, 42bv64), RAX[32:0][16:0]);

label_0x19f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x19fc:
t1_257 := RAX;
t2_258 := 168bv64;
RAX := PLUS_64(RAX, t2_258);
CF := bool2bv(LT_64(RAX, t1_257));
OF := AND_1((bool2bv((t1_257[64:63]) == (t2_258[64:63]))), (XOR_1((t1_257[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_257)), t2_258)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a02:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x1a07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1a0c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a12:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a17:
t_265 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_103;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)), 2bv64)), (XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)), 2bv64)), (XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)))))[1:0]));
SF := t_265[64:63];
ZF := bool2bv(0bv64 == t_265);

label_0x1a1a:
if (bv2bool(ZF)) {
  goto label_0x1a1d;
}

label_0x1a1c:
assume false;

label_0x1a1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1a22:
origDEST_269 := RAX;
origCOUNT_270 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_104));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_105);

label_0x1a26:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a2d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a31:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1a36:
origDEST_275 := RCX;
origCOUNT_276 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), CF, LSHIFT_64(origDEST_275, (MINUS_64(64bv64, origCOUNT_276)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_276 == 1bv64)), origDEST_275[64:63], unconstrained_106));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), AF, unconstrained_107);

label_0x1a3a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_108;
SF := unconstrained_109;
AF := unconstrained_110;
PF := unconstrained_111;

label_0x1a3e:
if (bv2bool(CF)) {
  goto label_0x1a41;
}

label_0x1a40:
assume false;

label_0x1a41:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1a46:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 42bv64))));

label_0x1a4b:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1a4e:
goto label_0x193e;

label_0x1a53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a5b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 160bv64))));

label_0x1a62:
t1_281 := RSP;
t2_282 := 152bv64;
RSP := PLUS_64(RSP, t2_282);
CF := bool2bv(LT_64(RSP, t1_281));
OF := AND_1((bool2bv((t1_281[64:63]) == (t2_282[64:63]))), (XOR_1((t1_281[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_281)), t2_282)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1a69:

ra_287 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_10,origCOUNT_100,origCOUNT_112,origCOUNT_126,origCOUNT_132,origCOUNT_138,origCOUNT_158,origCOUNT_16,origCOUNT_164,origCOUNT_182,origCOUNT_188,origCOUNT_206,origCOUNT_212,origCOUNT_22,origCOUNT_230,origCOUNT_236,origCOUNT_270,origCOUNT_276,origCOUNT_40,origCOUNT_46,origCOUNT_68,origCOUNT_74,origCOUNT_94,origDEST_111,origDEST_125,origDEST_131,origDEST_137,origDEST_15,origDEST_157,origDEST_163,origDEST_181,origDEST_187,origDEST_205,origDEST_21,origDEST_211,origDEST_229,origDEST_235,origDEST_269,origDEST_275,origDEST_39,origDEST_45,origDEST_67,origDEST_73,origDEST_9,origDEST_93,origDEST_99,ra_287,t1_105,t1_145,t1_169,t1_193,t1_217,t1_257,t1_27,t1_281,t1_55,t1_81,t2_106,t2_146,t2_170,t2_194,t2_218,t2_258,t2_28,t2_282,t2_56,t2_82,t_1,t_121,t_153,t_177,t_201,t_225,t_241,t_245,t_249,t_253,t_265,t_35,t_5,t_51,t_63,t_79,t_89;

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
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_10: bv32;
var origCOUNT_100: bv64;
var origCOUNT_112: bv32;
var origCOUNT_126: bv64;
var origCOUNT_132: bv64;
var origCOUNT_138: bv32;
var origCOUNT_158: bv64;
var origCOUNT_16: bv32;
var origCOUNT_164: bv64;
var origCOUNT_182: bv64;
var origCOUNT_188: bv64;
var origCOUNT_206: bv64;
var origCOUNT_212: bv64;
var origCOUNT_22: bv64;
var origCOUNT_230: bv64;
var origCOUNT_236: bv64;
var origCOUNT_270: bv64;
var origCOUNT_276: bv64;
var origCOUNT_40: bv64;
var origCOUNT_46: bv64;
var origCOUNT_68: bv64;
var origCOUNT_74: bv64;
var origCOUNT_94: bv64;
var origDEST_111: bv32;
var origDEST_125: bv64;
var origDEST_131: bv64;
var origDEST_137: bv32;
var origDEST_15: bv32;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_181: bv64;
var origDEST_187: bv64;
var origDEST_205: bv64;
var origDEST_21: bv64;
var origDEST_211: bv64;
var origDEST_229: bv64;
var origDEST_235: bv64;
var origDEST_269: bv64;
var origDEST_275: bv64;
var origDEST_39: bv64;
var origDEST_45: bv64;
var origDEST_67: bv64;
var origDEST_73: bv64;
var origDEST_9: bv32;
var origDEST_93: bv64;
var origDEST_99: bv64;
var ra_287: bv64;
var t1_105: bv64;
var t1_145: bv64;
var t1_169: bv64;
var t1_193: bv64;
var t1_217: bv64;
var t1_257: bv64;
var t1_27: bv64;
var t1_281: bv64;
var t1_55: bv64;
var t1_81: bv64;
var t2_106: bv64;
var t2_146: bv64;
var t2_170: bv64;
var t2_194: bv64;
var t2_218: bv64;
var t2_258: bv64;
var t2_28: bv64;
var t2_282: bv64;
var t2_56: bv64;
var t2_82: bv64;
var t_1: bv64;
var t_121: bv64;
var t_153: bv64;
var t_177: bv64;
var t_201: bv64;
var t_225: bv64;
var t_241: bv32;
var t_245: bv32;
var t_249: bv32;
var t_253: bv16;
var t_265: bv64;
var t_35: bv64;
var t_5: bv32;
var t_51: bv16;
var t_63: bv64;
var t_79: bv128;
var t_89: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(96bv64);
axiom policy(656bv64);
axiom policy(5408bv64);
axiom policy(6768bv64);
axiom policy(12448bv64);
axiom policy(12592bv64);
axiom policy(14480bv64);
