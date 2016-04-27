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
axiom _function_addr_low == 28080bv64;
axiom _function_addr_high == 31088bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x6db0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x6db5:
t_1 := RSP;
RSP := MINUS_64(RSP, 280bv64);
CF := bool2bv(LT_64(t_1, 280bv64));
OF := AND_64((XOR_64(t_1, 280bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 280bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x6dbc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6dc4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 92bv64))));

label_0x6dc8:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x6dcb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), 0bv32);

label_0x6dd3:
goto label_0x6ddf;

label_0x6dd5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x6dd9:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6ddb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x6ddf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6de7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 96bv64)));

label_0x6dea:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x6dee:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x6e8f;
}

label_0x6df4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6dfc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 648bv64)));

label_0x6e02:
origDEST_13 := RAX[32:0];
origCOUNT_14 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), CF, RSHIFT_32(origDEST_13, (MINUS_32(32bv32, origCOUNT_14)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv32)), AF, unconstrained_2);

label_0x6e05:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6e0d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 648bv64)));

label_0x6e13:
origDEST_19 := RCX[32:0];
origCOUNT_20 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), CF, LSHIFT_32(origDEST_19, (MINUS_32(32bv32, origCOUNT_20)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv32)), origDEST_19[32:31], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv32)), AF, unconstrained_4);

label_0x6e16:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x6e1a:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x6e1c:
RCX := (0bv32 ++ RCX[32:0]);

label_0x6e1e:
RDX := PLUS_64((PLUS_64(0bv64, 28197bv64)), 0bv64)[64:0];

label_0x6e25:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6e28:
mem := STORE_LE_32(mem, PLUS_64(RSP, 216bv64), RAX[32:0]);

label_0x6e2f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6e37:
t1_29 := RAX;
t2_30 := 648bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e3d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x6e42:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x6e47:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e4d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6e52:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x6e55:
if (bv2bool(ZF)) {
  goto label_0x6e58;
}

label_0x6e57:
assume false;

label_0x6e58:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x6e5d:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_10);

label_0x6e61:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6e68:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6e6c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x6e71:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_12);

label_0x6e75:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_13;
SF := unconstrained_14;
AF := unconstrained_15;
PF := unconstrained_16;

label_0x6e79:
if (bv2bool(CF)) {
  goto label_0x6e7c;
}

label_0x6e7b:
assume false;

label_0x6e7c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x6e81:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)));

label_0x6e88:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x6e8a:
goto label_0x6dd5;

label_0x6e8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6e97:
t1_53 := RAX;
t2_54 := 128bv64;
RAX := PLUS_64(RAX, t2_54);
CF := bool2bv(LT_64(RAX, t1_53));
OF := AND_1((bool2bv((t1_53[64:63]) == (t2_54[64:63]))), (XOR_1((t1_53[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_53)), t2_54)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6e9d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6ea5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 92bv64)));

label_0x6ea8:
t1_59 := RAX;
t2_60 := RCX;
RAX := PLUS_64(RAX, t2_60);
CF := bool2bv(LT_64(RAX, t1_59));
OF := AND_1((bool2bv((t1_59[64:63]) == (t2_60[64:63]))), (XOR_1((t1_59[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_59)), t2_60)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6eab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x6eb3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6ebb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6ec1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6ec6:
t_67 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x6ec9:
if (bv2bool(ZF)) {
  goto label_0x6ecc;
}

label_0x6ecb:
assume false;

label_0x6ecc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6ed4:
origDEST_71 := RAX;
origCOUNT_72 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_20);

label_0x6ed8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6edf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6ee3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6eeb:
origDEST_77 := RCX;
origCOUNT_78 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_22);

label_0x6eef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_23;
SF := unconstrained_24;
AF := unconstrained_25;
PF := unconstrained_26;

label_0x6ef3:
if (bv2bool(CF)) {
  goto label_0x6ef6;
}

label_0x6ef5:
assume false;

label_0x6ef6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6efe:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x6f01:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6f09:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 96bv64)));

label_0x6f0c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x6f10:
t_83 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_83)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_83, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)), 2bv32)), (XOR_32((RSHIFT_32(t_83, 4bv32)), t_83)))))[1:0]));
SF := t_83[32:31];
ZF := bool2bv(0bv32 == t_83);

label_0x6f15:
if (bv2bool(ZF)) {
  goto label_0x6f32;
}

label_0x6f17:
t_87 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_87)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_87, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))))[1:0]));
SF := t_87[32:31];
ZF := bool2bv(0bv32 == t_87);

label_0x6f1c:
if (bv2bool(ZF)) {
  goto label_0x7027;
}

label_0x6f22:
t_91 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_91)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_91, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))))[1:0]));
SF := t_91[32:31];
ZF := bool2bv(0bv32 == t_91);

label_0x6f27:
if (bv2bool(ZF)) {
  goto label_0x720c;
}

label_0x6f2d:
goto label_0x74c3;

label_0x6f32:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6f3a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x6f3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6f46:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x6f4a:
t1_95 := RCX;
t2_96 := RAX;
RCX := PLUS_64(RCX, t2_96);
CF := bool2bv(LT_64(RCX, t1_95));
OF := AND_1((bool2bv((t1_95[64:63]) == (t2_96[64:63]))), (XOR_1((t1_95[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_95)), t2_96)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x6f4d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RCX);

label_0x6f55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6f5d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6f63:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6f68:
t_103 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))))[1:0]));
SF := t_103[64:63];
ZF := bool2bv(0bv64 == t_103);

label_0x6f6b:
if (bv2bool(ZF)) {
  goto label_0x6f6e;
}

label_0x6f6d:
assume false;

label_0x6f6e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6f76:
origDEST_107 := RAX;
origCOUNT_108 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_30);

label_0x6f7a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6f81:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6f85:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6f8d:
origDEST_113 := RCX;
origCOUNT_114 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_32);

label_0x6f91:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x6f95:
if (bv2bool(CF)) {
  goto label_0x6f98;
}

label_0x6f97:
assume false;

label_0x6f98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x6fa0:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x6fa4:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x6fa6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6fae:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x6fb1:
t_119 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_119[32:31]) == (1bv32[32:31]))), (XOR_1((t_119[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_119)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6fb3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 220bv64), RAX[32:0]);

label_0x6fba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x6fc2:
t1_123 := RAX;
t2_124 := 108bv64;
RAX := PLUS_64(RAX, t2_124);
CF := bool2bv(LT_64(RAX, t1_123));
OF := AND_1((bool2bv((t1_123[64:63]) == (t2_124[64:63]))), (XOR_1((t1_123[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_123)), t2_124)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6fc6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x6fce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x6fd6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6fdc:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x6fe1:
t_131 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))))[1:0]));
SF := t_131[64:63];
ZF := bool2bv(0bv64 == t_131);

label_0x6fe4:
if (bv2bool(ZF)) {
  goto label_0x6fe7;
}

label_0x6fe6:
assume false;

label_0x6fe7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x6fef:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_40);

label_0x6ff3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6ffa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6ffe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7006:
origDEST_141 := RCX;
origCOUNT_142 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), CF, LSHIFT_64(origDEST_141, (MINUS_64(64bv64, origCOUNT_142)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_142 == 1bv64)), origDEST_141[64:63], unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), AF, unconstrained_42);

label_0x700a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_43;
SF := unconstrained_44;
AF := unconstrained_45;
PF := unconstrained_46;

label_0x700e:
if (bv2bool(CF)) {
  goto label_0x7011;
}

label_0x7010:
assume false;

label_0x7011:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x7019:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)));

label_0x7020:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7022:
goto label_0x795f;

label_0x7027:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x702f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7033:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x703b:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x703f:
t1_147 := RCX;
t2_148 := RAX;
RCX := PLUS_64(RCX, t2_148);
CF := bool2bv(LT_64(RCX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7042:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RCX);

label_0x704a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7052:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7058:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x705d:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x7060:
if (bv2bool(ZF)) {
  goto label_0x7063;
}

label_0x7062:
assume false;

label_0x7063:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x706b:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_50);

label_0x706f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7076:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x707a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7082:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_52);

label_0x7086:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x708a:
if (bv2bool(CF)) {
  goto label_0x708d;
}

label_0x708c:
assume false;

label_0x708d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x7095:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x7099:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x709b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x70a3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x70a6:
t_171 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_171[32:31]) == (1bv32[32:31]))), (XOR_1((t_171[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_171)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x70a8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 224bv64), RAX[32:0]);

label_0x70af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x70b7:
t1_175 := RAX;
t2_176 := 108bv64;
RAX := PLUS_64(RAX, t2_176);
CF := bool2bv(LT_64(RAX, t1_175));
OF := AND_1((bool2bv((t1_175[64:63]) == (t2_176[64:63]))), (XOR_1((t1_175[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_175)), t2_176)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x70bb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x70c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x70cb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x70d1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x70d6:
t_183 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))))[1:0]));
SF := t_183[64:63];
ZF := bool2bv(0bv64 == t_183);

label_0x70d9:
if (bv2bool(ZF)) {
  goto label_0x70dc;
}

label_0x70db:
assume false;

label_0x70dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x70e4:
origDEST_187 := RAX;
origCOUNT_188 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_60);

label_0x70e8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x70ef:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x70f3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x70fb:
origDEST_193 := RCX;
origCOUNT_194 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), CF, LSHIFT_64(origDEST_193, (MINUS_64(64bv64, origCOUNT_194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_194 == 1bv64)), origDEST_193[64:63], unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), AF, unconstrained_62);

label_0x70ff:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_63;
SF := unconstrained_64;
AF := unconstrained_65;
PF := unconstrained_66;

label_0x7103:
if (bv2bool(CF)) {
  goto label_0x7106;
}

label_0x7105:
assume false;

label_0x7106:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x710e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 224bv64)));

label_0x7115:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7117:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x711f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7123:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x712b:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x712f:
t1_199 := RCX;
t2_200 := RAX;
RCX := PLUS_64(RCX, t2_200);
CF := bool2bv(LT_64(RCX, t1_199));
OF := AND_1((bool2bv((t1_199[64:63]) == (t2_200[64:63]))), (XOR_1((t1_199[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_199)), t2_200)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7132:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RCX);

label_0x713a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7142:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_67;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7148:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x714d:
t_207 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_207, 4bv64)), t_207)), 2bv64)), (XOR_64((RSHIFT_64(t_207, 4bv64)), t_207)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_207, 4bv64)), t_207)), 2bv64)), (XOR_64((RSHIFT_64(t_207, 4bv64)), t_207)))))[1:0]));
SF := t_207[64:63];
ZF := bool2bv(0bv64 == t_207);

label_0x7150:
if (bv2bool(ZF)) {
  goto label_0x7153;
}

label_0x7152:
assume false;

label_0x7153:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x715b:
origDEST_211 := RAX;
origCOUNT_212 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), CF, LSHIFT_64(origDEST_211, (MINUS_64(64bv64, origCOUNT_212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv64)), origDEST_211[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), AF, unconstrained_70);

label_0x715f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7166:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x716a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7172:
origDEST_217 := RCX;
origCOUNT_218 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), CF, LSHIFT_64(origDEST_217, (MINUS_64(64bv64, origCOUNT_218)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv64)), origDEST_217[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), AF, unconstrained_72);

label_0x7176:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_73;
SF := unconstrained_74;
AF := unconstrained_75;
PF := unconstrained_76;

label_0x717a:
if (bv2bool(CF)) {
  goto label_0x717d;
}

label_0x717c:
assume false;

label_0x717d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x7185:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x7189:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x718b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7193:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x7196:
t_223 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_223[32:31]) == (1bv32[32:31]))), (XOR_1((t_223[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_223)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7198:
mem := STORE_LE_32(mem, PLUS_64(RSP, 228bv64), RAX[32:0]);

label_0x719f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x71a7:
t1_227 := RAX;
t2_228 := 108bv64;
RAX := PLUS_64(RAX, t2_228);
CF := bool2bv(LT_64(RAX, t1_227));
OF := AND_1((bool2bv((t1_227[64:63]) == (t2_228[64:63]))), (XOR_1((t1_227[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_227)), t2_228)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x71ab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x71b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x71bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x71c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x71c6:
t_235 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))))[1:0]));
SF := t_235[64:63];
ZF := bool2bv(0bv64 == t_235);

label_0x71c9:
if (bv2bool(ZF)) {
  goto label_0x71cc;
}

label_0x71cb:
assume false;

label_0x71cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x71d4:
origDEST_239 := RAX;
origCOUNT_240 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_80);

label_0x71d8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x71df:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x71e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x71eb:
origDEST_245 := RCX;
origCOUNT_246 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_82);

label_0x71ef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x71f3:
if (bv2bool(CF)) {
  goto label_0x71f6;
}

label_0x71f5:
assume false;

label_0x71f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x71fe:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 228bv64)));

label_0x7205:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7207:
goto label_0x795f;

label_0x720c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7214:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7218:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7220:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7224:
t1_251 := RCX;
t2_252 := RAX;
RCX := PLUS_64(RCX, t2_252);
CF := bool2bv(LT_64(RCX, t1_251));
OF := AND_1((bool2bv((t1_251[64:63]) == (t2_252[64:63]))), (XOR_1((t1_251[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_251)), t2_252)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7227:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RCX);

label_0x722f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x7237:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x723d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7242:
t_259 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_88;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)), 2bv64)), (XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)), 2bv64)), (XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)))))[1:0]));
SF := t_259[64:63];
ZF := bool2bv(0bv64 == t_259);

label_0x7245:
if (bv2bool(ZF)) {
  goto label_0x7248;
}

label_0x7247:
assume false;

label_0x7248:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x7250:
origDEST_263 := RAX;
origCOUNT_264 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_89));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_90);

label_0x7254:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x725b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x725f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x7267:
origDEST_269 := RCX;
origCOUNT_270 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_92);

label_0x726b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_93;
SF := unconstrained_94;
AF := unconstrained_95;
PF := unconstrained_96;

label_0x726f:
if (bv2bool(CF)) {
  goto label_0x7272;
}

label_0x7271:
assume false;

label_0x7272:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x727a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x727e:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7280:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7288:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x728b:
t_275 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_275[32:31]) == (1bv32[32:31]))), (XOR_1((t_275[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_275)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x728d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 232bv64), RAX[32:0]);

label_0x7294:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x729c:
t1_279 := RAX;
t2_280 := 108bv64;
RAX := PLUS_64(RAX, t2_280);
CF := bool2bv(LT_64(RAX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x72a0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x72a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x72b0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_97;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x72b6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x72bb:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_98;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x72be:
if (bv2bool(ZF)) {
  goto label_0x72c1;
}

label_0x72c0:
assume false;

label_0x72c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x72c9:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_99));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_100);

label_0x72cd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x72d4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x72d8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x72e0:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_101));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_102);

label_0x72e4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_103;
SF := unconstrained_104;
AF := unconstrained_105;
PF := unconstrained_106;

label_0x72e8:
if (bv2bool(CF)) {
  goto label_0x72eb;
}

label_0x72ea:
assume false;

label_0x72eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x72f3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 232bv64)));

label_0x72fa:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x72fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7304:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7308:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7310:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7314:
t1_303 := RCX;
t2_304 := RAX;
RCX := PLUS_64(RCX, t2_304);
CF := bool2bv(LT_64(RCX, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7317:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RCX);

label_0x731f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7327:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x732d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7332:
t_311 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_108;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))))[1:0]));
SF := t_311[64:63];
ZF := bool2bv(0bv64 == t_311);

label_0x7335:
if (bv2bool(ZF)) {
  goto label_0x7338;
}

label_0x7337:
assume false;

label_0x7338:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7340:
origDEST_315 := RAX;
origCOUNT_316 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_109));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_110);

label_0x7344:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x734b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x734f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x7357:
origDEST_321 := RCX;
origCOUNT_322 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), CF, LSHIFT_64(origDEST_321, (MINUS_64(64bv64, origCOUNT_322)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_322 == 1bv64)), origDEST_321[64:63], unconstrained_111));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), AF, unconstrained_112);

label_0x735b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_113;
SF := unconstrained_114;
AF := unconstrained_115;
PF := unconstrained_116;

label_0x735f:
if (bv2bool(CF)) {
  goto label_0x7362;
}

label_0x7361:
assume false;

label_0x7362:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x736a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x736e:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7370:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7378:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x737b:
t_327 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_327[32:31]) == (1bv32[32:31]))), (XOR_1((t_327[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_327)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x737d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 236bv64), RAX[32:0]);

label_0x7384:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x738c:
t1_331 := RAX;
t2_332 := 108bv64;
RAX := PLUS_64(RAX, t2_332);
CF := bool2bv(LT_64(RAX, t1_331));
OF := AND_1((bool2bv((t1_331[64:63]) == (t2_332[64:63]))), (XOR_1((t1_331[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_331)), t2_332)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7390:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x7398:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x73a0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x73a6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x73ab:
t_339 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))))[1:0]));
SF := t_339[64:63];
ZF := bool2bv(0bv64 == t_339);

label_0x73ae:
if (bv2bool(ZF)) {
  goto label_0x73b1;
}

label_0x73b0:
assume false;

label_0x73b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x73b9:
origDEST_343 := RAX;
origCOUNT_344 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), CF, LSHIFT_64(origDEST_343, (MINUS_64(64bv64, origCOUNT_344)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_344 == 1bv64)), origDEST_343[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), AF, unconstrained_120);

label_0x73bd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x73c4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x73c8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x73d0:
origDEST_349 := RCX;
origCOUNT_350 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, LSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), origDEST_349[64:63], unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_122);

label_0x73d4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_123;
SF := unconstrained_124;
AF := unconstrained_125;
PF := unconstrained_126;

label_0x73d8:
if (bv2bool(CF)) {
  goto label_0x73db;
}

label_0x73da:
assume false;

label_0x73db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x73e3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 236bv64)));

label_0x73ea:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x73ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x73f4:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x73f8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7400:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7404:
t1_355 := RCX;
t2_356 := RAX;
RCX := PLUS_64(RCX, t2_356);
CF := bool2bv(LT_64(RCX, t1_355));
OF := AND_1((bool2bv((t1_355[64:63]) == (t2_356[64:63]))), (XOR_1((t1_355[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_355)), t2_356)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7407:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RCX);

label_0x740c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x7411:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7417:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x741c:
t_363 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_128;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)), 2bv64)), (XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)), 2bv64)), (XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)))))[1:0]));
SF := t_363[64:63];
ZF := bool2bv(0bv64 == t_363);

label_0x741f:
if (bv2bool(ZF)) {
  goto label_0x7422;
}

label_0x7421:
assume false;

label_0x7422:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x7427:
origDEST_367 := RAX;
origCOUNT_368 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, LSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), origDEST_367[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_130);

label_0x742b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7432:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7436:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x743b:
origDEST_373 := RCX;
origCOUNT_374 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), CF, LSHIFT_64(origDEST_373, (MINUS_64(64bv64, origCOUNT_374)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_374 == 1bv64)), origDEST_373[64:63], unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), AF, unconstrained_132);

label_0x743f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_133;
SF := unconstrained_134;
AF := unconstrained_135;
PF := unconstrained_136;

label_0x7443:
if (bv2bool(CF)) {
  goto label_0x7446;
}

label_0x7445:
assume false;

label_0x7446:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x744b:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x744f:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7451:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7459:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x745c:
t_379 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_379[32:31]) == (1bv32[32:31]))), (XOR_1((t_379[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_379)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x745e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 240bv64), RAX[32:0]);

label_0x7465:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x746d:
t1_383 := RAX;
t2_384 := 108bv64;
RAX := PLUS_64(RAX, t2_384);
CF := bool2bv(LT_64(RAX, t1_383));
OF := AND_1((bool2bv((t1_383[64:63]) == (t2_384[64:63]))), (XOR_1((t1_383[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_383)), t2_384)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7471:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RAX);

label_0x7476:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x747b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_137;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7481:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7486:
t_391 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_138;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_391, 4bv64)), t_391)), 2bv64)), (XOR_64((RSHIFT_64(t_391, 4bv64)), t_391)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_391, 4bv64)), t_391)), 2bv64)), (XOR_64((RSHIFT_64(t_391, 4bv64)), t_391)))))[1:0]));
SF := t_391[64:63];
ZF := bool2bv(0bv64 == t_391);

label_0x7489:
if (bv2bool(ZF)) {
  goto label_0x748c;
}

label_0x748b:
assume false;

label_0x748c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x7491:
origDEST_395 := RAX;
origCOUNT_396 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), CF, LSHIFT_64(origDEST_395, (MINUS_64(64bv64, origCOUNT_396)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_396 == 1bv64)), origDEST_395[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_396 == 0bv64)), AF, unconstrained_140);

label_0x7495:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x749c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x74a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x74a5:
origDEST_401 := RCX;
origCOUNT_402 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), CF, LSHIFT_64(origDEST_401, (MINUS_64(64bv64, origCOUNT_402)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_402 == 1bv64)), origDEST_401[64:63], unconstrained_141));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_402 == 0bv64)), AF, unconstrained_142);

label_0x74a9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_143;
SF := unconstrained_144;
AF := unconstrained_145;
PF := unconstrained_146;

label_0x74ad:
if (bv2bool(CF)) {
  goto label_0x74b0;
}

label_0x74af:
assume false;

label_0x74b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x74b5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 240bv64)));

label_0x74bc:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x74be:
goto label_0x795f;

label_0x74c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x74cb:
t1_407 := RAX;
t2_408 := 128bv64;
RAX := PLUS_64(RAX, t2_408);
CF := bool2bv(LT_64(RAX, t1_407));
OF := AND_1((bool2bv((t1_407[64:63]) == (t2_408[64:63]))), (XOR_1((t1_407[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_407)), t2_408)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x74d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x74d9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 96bv64)));

label_0x74dc:
t_413 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), 4bv32));
CF := bool2bv(LT_32(t_413, 4bv32));
OF := AND_32((XOR_32(t_413, 4bv32)), (XOR_32(t_413, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_413)), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x74df:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x74e2:
t1_417 := RAX;
t2_418 := RCX;
RAX := PLUS_64(RAX, t2_418);
CF := bool2bv(LT_64(RAX, t1_417));
OF := AND_1((bool2bv((t1_417[64:63]) == (t2_418[64:63]))), (XOR_1((t1_417[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_417)), t2_418)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x74e5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x74ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x74ef:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x74f5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x74fa:
t_425 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_148;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)), 2bv64)), (XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)), 2bv64)), (XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)))))[1:0]));
SF := t_425[64:63];
ZF := bool2bv(0bv64 == t_425);

label_0x74fd:
if (bv2bool(ZF)) {
  goto label_0x7500;
}

label_0x74ff:
assume false;

label_0x7500:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x7505:
origDEST_429 := RAX;
origCOUNT_430 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), CF, LSHIFT_64(origDEST_429, (MINUS_64(64bv64, origCOUNT_430)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_430 == 1bv64)), origDEST_429[64:63], unconstrained_149));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), AF, unconstrained_150);

label_0x7509:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7510:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7514:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x7519:
origDEST_435 := RCX;
origCOUNT_436 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), CF, LSHIFT_64(origDEST_435, (MINUS_64(64bv64, origCOUNT_436)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_436 == 1bv64)), origDEST_435[64:63], unconstrained_151));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), AF, unconstrained_152);

label_0x751d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_153;
SF := unconstrained_154;
AF := unconstrained_155;
PF := unconstrained_156;

label_0x7521:
if (bv2bool(CF)) {
  goto label_0x7524;
}

label_0x7523:
assume false;

label_0x7524:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x7529:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x752c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7534:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7538:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7540:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7544:
t1_441 := RCX;
t2_442 := RAX;
RCX := PLUS_64(RCX, t2_442);
CF := bool2bv(LT_64(RCX, t1_441));
OF := AND_1((bool2bv((t1_441[64:63]) == (t2_442[64:63]))), (XOR_1((t1_441[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_441)), t2_442)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7547:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RCX);

label_0x754c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7551:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7557:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x755c:
t_449 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_158;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)), 2bv64)), (XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)), 2bv64)), (XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)))))[1:0]));
SF := t_449[64:63];
ZF := bool2bv(0bv64 == t_449);

label_0x755f:
if (bv2bool(ZF)) {
  goto label_0x7562;
}

label_0x7561:
assume false;

label_0x7562:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x7567:
origDEST_453 := RAX;
origCOUNT_454 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), CF, LSHIFT_64(origDEST_453, (MINUS_64(64bv64, origCOUNT_454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_454 == 1bv64)), origDEST_453[64:63], unconstrained_159));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), AF, unconstrained_160);

label_0x756b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7572:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7576:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x757b:
origDEST_459 := RCX;
origCOUNT_460 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), CF, LSHIFT_64(origDEST_459, (MINUS_64(64bv64, origCOUNT_460)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_460 == 1bv64)), origDEST_459[64:63], unconstrained_161));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), AF, unconstrained_162);

label_0x757f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_163;
SF := unconstrained_164;
AF := unconstrained_165;
PF := unconstrained_166;

label_0x7583:
if (bv2bool(CF)) {
  goto label_0x7586;
}

label_0x7585:
assume false;

label_0x7586:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x758b:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x758f:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7591:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7599:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x759c:
t_465 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_465[32:31]) == (1bv32[32:31]))), (XOR_1((t_465[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_465)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x759e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 244bv64), RAX[32:0]);

label_0x75a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x75ad:
t1_469 := RAX;
t2_470 := 108bv64;
RAX := PLUS_64(RAX, t2_470);
CF := bool2bv(LT_64(RAX, t1_469));
OF := AND_1((bool2bv((t1_469[64:63]) == (t2_470[64:63]))), (XOR_1((t1_469[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_469)), t2_470)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x75b1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x75b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x75bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x75c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x75c6:
t_477 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_168;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)), 2bv64)), (XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)), 2bv64)), (XOR_64((RSHIFT_64(t_477, 4bv64)), t_477)))))[1:0]));
SF := t_477[64:63];
ZF := bool2bv(0bv64 == t_477);

label_0x75c9:
if (bv2bool(ZF)) {
  goto label_0x75cc;
}

label_0x75cb:
assume false;

label_0x75cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x75d1:
origDEST_481 := RAX;
origCOUNT_482 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), CF, LSHIFT_64(origDEST_481, (MINUS_64(64bv64, origCOUNT_482)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_482 == 1bv64)), origDEST_481[64:63], unconstrained_169));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), AF, unconstrained_170);

label_0x75d5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x75dc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x75e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x75e5:
origDEST_487 := RCX;
origCOUNT_488 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), CF, LSHIFT_64(origDEST_487, (MINUS_64(64bv64, origCOUNT_488)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_488 == 1bv64)), origDEST_487[64:63], unconstrained_171));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), AF, unconstrained_172);

label_0x75e9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_173;
SF := unconstrained_174;
AF := unconstrained_175;
PF := unconstrained_176;

label_0x75ed:
if (bv2bool(CF)) {
  goto label_0x75f0;
}

label_0x75ef:
assume false;

label_0x75f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x75f5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 244bv64)));

label_0x75fc:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x75fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7606:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x760a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7612:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x7616:
t1_493 := RCX;
t2_494 := RAX;
RCX := PLUS_64(RCX, t2_494);
CF := bool2bv(LT_64(RCX, t1_493));
OF := AND_1((bool2bv((t1_493[64:63]) == (t2_494[64:63]))), (XOR_1((t1_493[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_493)), t2_494)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7619:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RCX);

label_0x761e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x7623:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7629:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x762e:
t_501 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_178;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))))[1:0]));
SF := t_501[64:63];
ZF := bool2bv(0bv64 == t_501);

label_0x7631:
if (bv2bool(ZF)) {
  goto label_0x7634;
}

label_0x7633:
assume false;

label_0x7634:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x7639:
origDEST_505 := RAX;
origCOUNT_506 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), CF, LSHIFT_64(origDEST_505, (MINUS_64(64bv64, origCOUNT_506)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_506 == 1bv64)), origDEST_505[64:63], unconstrained_179));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), AF, unconstrained_180);

label_0x763d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7644:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7648:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x764d:
origDEST_511 := RCX;
origCOUNT_512 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), CF, LSHIFT_64(origDEST_511, (MINUS_64(64bv64, origCOUNT_512)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_512 == 1bv64)), origDEST_511[64:63], unconstrained_181));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), AF, unconstrained_182);

label_0x7651:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_183;
SF := unconstrained_184;
AF := unconstrained_185;
PF := unconstrained_186;

label_0x7655:
if (bv2bool(CF)) {
  goto label_0x7658;
}

label_0x7657:
assume false;

label_0x7658:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x765d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x7661:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7663:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x766b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x766e:
t_517 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_517[32:31]) == (1bv32[32:31]))), (XOR_1((t_517[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_517)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7670:
mem := STORE_LE_32(mem, PLUS_64(RSP, 248bv64), RAX[32:0]);

label_0x7677:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x767f:
t1_521 := RAX;
t2_522 := 108bv64;
RAX := PLUS_64(RAX, t2_522);
CF := bool2bv(LT_64(RAX, t1_521));
OF := AND_1((bool2bv((t1_521[64:63]) == (t2_522[64:63]))), (XOR_1((t1_521[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_521)), t2_522)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7683:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x7688:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x768d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7693:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7698:
t_529 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_188;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_529, 4bv64)), t_529)), 2bv64)), (XOR_64((RSHIFT_64(t_529, 4bv64)), t_529)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_529, 4bv64)), t_529)), 2bv64)), (XOR_64((RSHIFT_64(t_529, 4bv64)), t_529)))))[1:0]));
SF := t_529[64:63];
ZF := bool2bv(0bv64 == t_529);

label_0x769b:
if (bv2bool(ZF)) {
  goto label_0x769e;
}

label_0x769d:
assume false;

label_0x769e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x76a3:
origDEST_533 := RAX;
origCOUNT_534 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), CF, LSHIFT_64(origDEST_533, (MINUS_64(64bv64, origCOUNT_534)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_534 == 1bv64)), origDEST_533[64:63], unconstrained_189));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_534 == 0bv64)), AF, unconstrained_190);

label_0x76a7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x76ae:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x76b2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x76b7:
origDEST_539 := RCX;
origCOUNT_540 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), CF, LSHIFT_64(origDEST_539, (MINUS_64(64bv64, origCOUNT_540)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_540 == 1bv64)), origDEST_539[64:63], unconstrained_191));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), AF, unconstrained_192);

label_0x76bb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_193;
SF := unconstrained_194;
AF := unconstrained_195;
PF := unconstrained_196;

label_0x76bf:
if (bv2bool(CF)) {
  goto label_0x76c2;
}

label_0x76c1:
assume false;

label_0x76c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x76c7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 248bv64)));

label_0x76ce:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x76d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x76d8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x76dc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x76e4:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x76e8:
t1_545 := RCX;
t2_546 := RAX;
RCX := PLUS_64(RCX, t2_546);
CF := bool2bv(LT_64(RCX, t1_545));
OF := AND_1((bool2bv((t1_545[64:63]) == (t2_546[64:63]))), (XOR_1((t1_545[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_545)), t2_546)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x76eb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RCX);

label_0x76f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x76f5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_197;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x76fb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7700:
t_553 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_198;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_553, 4bv64)), t_553)), 2bv64)), (XOR_64((RSHIFT_64(t_553, 4bv64)), t_553)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_553, 4bv64)), t_553)), 2bv64)), (XOR_64((RSHIFT_64(t_553, 4bv64)), t_553)))))[1:0]));
SF := t_553[64:63];
ZF := bool2bv(0bv64 == t_553);

label_0x7703:
if (bv2bool(ZF)) {
  goto label_0x7706;
}

label_0x7705:
assume false;

label_0x7706:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x770b:
origDEST_557 := RAX;
origCOUNT_558 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), CF, LSHIFT_64(origDEST_557, (MINUS_64(64bv64, origCOUNT_558)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_558 == 1bv64)), origDEST_557[64:63], unconstrained_199));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_558 == 0bv64)), AF, unconstrained_200);

label_0x770f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7716:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x771a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x771f:
origDEST_563 := RCX;
origCOUNT_564 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), CF, LSHIFT_64(origDEST_563, (MINUS_64(64bv64, origCOUNT_564)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_564 == 1bv64)), origDEST_563[64:63], unconstrained_201));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), AF, unconstrained_202);

label_0x7723:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_203;
SF := unconstrained_204;
AF := unconstrained_205;
PF := unconstrained_206;

label_0x7727:
if (bv2bool(CF)) {
  goto label_0x772a;
}

label_0x7729:
assume false;

label_0x772a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x772f:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x7733:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7735:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x773d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x7740:
t_569 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_569[32:31]) == (1bv32[32:31]))), (XOR_1((t_569[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_569)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7742:
mem := STORE_LE_32(mem, PLUS_64(RSP, 252bv64), RAX[32:0]);

label_0x7749:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7751:
t1_573 := RAX;
t2_574 := 108bv64;
RAX := PLUS_64(RAX, t2_574);
CF := bool2bv(LT_64(RAX, t1_573));
OF := AND_1((bool2bv((t1_573[64:63]) == (t2_574[64:63]))), (XOR_1((t1_573[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_573)), t2_574)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7755:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x775a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x775f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7765:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x776a:
t_581 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_208;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_581, 4bv64)), t_581)), 2bv64)), (XOR_64((RSHIFT_64(t_581, 4bv64)), t_581)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_581, 4bv64)), t_581)), 2bv64)), (XOR_64((RSHIFT_64(t_581, 4bv64)), t_581)))))[1:0]));
SF := t_581[64:63];
ZF := bool2bv(0bv64 == t_581);

label_0x776d:
if (bv2bool(ZF)) {
  goto label_0x7770;
}

label_0x776f:
assume false;

label_0x7770:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x7775:
origDEST_585 := RAX;
origCOUNT_586 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), CF, LSHIFT_64(origDEST_585, (MINUS_64(64bv64, origCOUNT_586)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_586 == 1bv64)), origDEST_585[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_586 == 0bv64)), AF, unconstrained_210);

label_0x7779:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7780:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7784:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x7789:
origDEST_591 := RCX;
origCOUNT_592 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), CF, LSHIFT_64(origDEST_591, (MINUS_64(64bv64, origCOUNT_592)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_592 == 1bv64)), origDEST_591[64:63], unconstrained_211));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), AF, unconstrained_212);

label_0x778d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_213;
SF := unconstrained_214;
AF := unconstrained_215;
PF := unconstrained_216;

label_0x7791:
if (bv2bool(CF)) {
  goto label_0x7794;
}

label_0x7793:
assume false;

label_0x7794:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x7799:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 252bv64)));

label_0x77a0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x77a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x77aa:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x77ae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x77b6:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x77ba:
t1_597 := RCX;
t2_598 := RAX;
RCX := PLUS_64(RCX, t2_598);
CF := bool2bv(LT_64(RCX, t1_597));
OF := AND_1((bool2bv((t1_597[64:63]) == (t2_598[64:63]))), (XOR_1((t1_597[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_597)), t2_598)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x77bd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RCX);

label_0x77c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x77c7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_217;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x77cd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x77d2:
t_605 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_218;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_605, 4bv64)), t_605)), 2bv64)), (XOR_64((RSHIFT_64(t_605, 4bv64)), t_605)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_605, 4bv64)), t_605)), 2bv64)), (XOR_64((RSHIFT_64(t_605, 4bv64)), t_605)))))[1:0]));
SF := t_605[64:63];
ZF := bool2bv(0bv64 == t_605);

label_0x77d5:
if (bv2bool(ZF)) {
  goto label_0x77d8;
}

label_0x77d7:
assume false;

label_0x77d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x77dd:
origDEST_609 := RAX;
origCOUNT_610 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), CF, LSHIFT_64(origDEST_609, (MINUS_64(64bv64, origCOUNT_610)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_610 == 1bv64)), origDEST_609[64:63], unconstrained_219));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv64)), AF, unconstrained_220);

label_0x77e1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x77e8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x77ec:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x77f1:
origDEST_615 := RCX;
origCOUNT_616 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), CF, LSHIFT_64(origDEST_615, (MINUS_64(64bv64, origCOUNT_616)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_616 == 1bv64)), origDEST_615[64:63], unconstrained_221));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_616 == 0bv64)), AF, unconstrained_222);

label_0x77f5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_223;
SF := unconstrained_224;
AF := unconstrained_225;
PF := unconstrained_226;

label_0x77f9:
if (bv2bool(CF)) {
  goto label_0x77fc;
}

label_0x77fb:
assume false;

label_0x77fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x7801:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x7805:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x7807:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x780f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x7812:
t_621 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_621[32:31]) == (1bv32[32:31]))), (XOR_1((t_621[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_621)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7814:
mem := STORE_LE_32(mem, PLUS_64(RSP, 256bv64), RAX[32:0]);

label_0x781b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7823:
t1_625 := RAX;
t2_626 := 108bv64;
RAX := PLUS_64(RAX, t2_626);
CF := bool2bv(LT_64(RAX, t1_625));
OF := AND_1((bool2bv((t1_625[64:63]) == (t2_626[64:63]))), (XOR_1((t1_625[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_625)), t2_626)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7827:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x782c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7831:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_227;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7837:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x783c:
t_633 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_228;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_633, 4bv64)), t_633)), 2bv64)), (XOR_64((RSHIFT_64(t_633, 4bv64)), t_633)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_633, 4bv64)), t_633)), 2bv64)), (XOR_64((RSHIFT_64(t_633, 4bv64)), t_633)))))[1:0]));
SF := t_633[64:63];
ZF := bool2bv(0bv64 == t_633);

label_0x783f:
if (bv2bool(ZF)) {
  goto label_0x7842;
}

label_0x7841:
assume false;

label_0x7842:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7847:
origDEST_637 := RAX;
origCOUNT_638 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), CF, LSHIFT_64(origDEST_637, (MINUS_64(64bv64, origCOUNT_638)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_638 == 1bv64)), origDEST_637[64:63], unconstrained_229));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_638 == 0bv64)), AF, unconstrained_230);

label_0x784b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7852:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7856:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x785b:
origDEST_643 := RCX;
origCOUNT_644 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), CF, LSHIFT_64(origDEST_643, (MINUS_64(64bv64, origCOUNT_644)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_644 == 1bv64)), origDEST_643[64:63], unconstrained_231));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), AF, unconstrained_232);

label_0x785f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_233;
SF := unconstrained_234;
AF := unconstrained_235;
PF := unconstrained_236;

label_0x7863:
if (bv2bool(CF)) {
  goto label_0x7866;
}

label_0x7865:
assume false;

label_0x7866:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x786b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 256bv64)));

label_0x7872:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7874:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x787c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 96bv64)));

label_0x787f:
t_649 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 4bv32));
CF := bool2bv(LT_32(t_649, 4bv32));
OF := AND_32((XOR_32(t_649, 4bv32)), (XOR_32(t_649, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_649)), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7882:
mem := STORE_LE_32(mem, PLUS_64(RSP, 260bv64), RAX[32:0]);

label_0x7889:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x7891:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x7895:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x789d:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 64bv64));

label_0x78a1:
t1_653 := RCX;
t2_654 := RAX;
RCX := PLUS_64(RCX, t2_654);
CF := bool2bv(LT_64(RCX, t1_653));
OF := AND_1((bool2bv((t1_653[64:63]) == (t2_654[64:63]))), (XOR_1((t1_653[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_653)), t2_654)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x78a4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RCX);

label_0x78a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x78ae:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_237;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x78b4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x78b9:
t_661 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_238;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_661, 4bv64)), t_661)), 2bv64)), (XOR_64((RSHIFT_64(t_661, 4bv64)), t_661)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_661, 4bv64)), t_661)), 2bv64)), (XOR_64((RSHIFT_64(t_661, 4bv64)), t_661)))))[1:0]));
SF := t_661[64:63];
ZF := bool2bv(0bv64 == t_661);

label_0x78bc:
if (bv2bool(ZF)) {
  goto label_0x78bf;
}

label_0x78be:
assume false;

label_0x78bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x78c4:
origDEST_665 := RAX;
origCOUNT_666 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), CF, LSHIFT_64(origDEST_665, (MINUS_64(64bv64, origCOUNT_666)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_666 == 1bv64)), origDEST_665[64:63], unconstrained_239));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), AF, unconstrained_240);

label_0x78c8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x78cf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x78d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x78d8:
origDEST_671 := RCX;
origCOUNT_672 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), CF, LSHIFT_64(origDEST_671, (MINUS_64(64bv64, origCOUNT_672)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_672 == 1bv64)), origDEST_671[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_672 == 0bv64)), AF, unconstrained_242);

label_0x78dc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_243;
SF := unconstrained_244;
AF := unconstrained_245;
PF := unconstrained_246;

label_0x78e0:
if (bv2bool(CF)) {
  goto label_0x78e3;
}

label_0x78e2:
assume false;

label_0x78e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x78e8:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 260bv64))));

label_0x78f0:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x78f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x78fa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)));

label_0x78fd:
t_677 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_677[32:31]) == (1bv32[32:31]))), (XOR_1((t_677[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_677)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x78ff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 264bv64), RAX[32:0]);

label_0x7906:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x790e:
t1_681 := RAX;
t2_682 := 108bv64;
RAX := PLUS_64(RAX, t2_682);
CF := bool2bv(LT_64(RAX, t1_681));
OF := AND_1((bool2bv((t1_681[64:63]) == (t2_682[64:63]))), (XOR_1((t1_681[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_681)), t2_682)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7912:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x7917:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x791c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_247;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7922:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7927:
t_689 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_248;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_689, 4bv64)), t_689)), 2bv64)), (XOR_64((RSHIFT_64(t_689, 4bv64)), t_689)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_689, 4bv64)), t_689)), 2bv64)), (XOR_64((RSHIFT_64(t_689, 4bv64)), t_689)))))[1:0]));
SF := t_689[64:63];
ZF := bool2bv(0bv64 == t_689);

label_0x792a:
if (bv2bool(ZF)) {
  goto label_0x792d;
}

label_0x792c:
assume false;

label_0x792d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x7932:
origDEST_693 := RAX;
origCOUNT_694 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), CF, LSHIFT_64(origDEST_693, (MINUS_64(64bv64, origCOUNT_694)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_694 == 1bv64)), origDEST_693[64:63], unconstrained_249));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), AF, unconstrained_250);

label_0x7936:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x793d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7941:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x7946:
origDEST_699 := RCX;
origCOUNT_700 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), CF, LSHIFT_64(origDEST_699, (MINUS_64(64bv64, origCOUNT_700)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_700 == 1bv64)), origDEST_699[64:63], unconstrained_251));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_700 == 0bv64)), AF, unconstrained_252);

label_0x794a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_253;
SF := unconstrained_254;
AF := unconstrained_255;
PF := unconstrained_256;

label_0x794e:
if (bv2bool(CF)) {
  goto label_0x7951;
}

label_0x7950:
assume false;

label_0x7951:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x7956:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 264bv64)));

label_0x795d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x795f:
t1_705 := RSP;
t2_706 := 280bv64;
RSP := PLUS_64(RSP, t2_706);
CF := bool2bv(LT_64(RSP, t1_705));
OF := AND_1((bool2bv((t1_705[64:63]) == (t2_706[64:63]))), (XOR_1((t1_705[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_705)), t2_706)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x7966:

ra_711 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_108,origCOUNT_114,origCOUNT_136,origCOUNT_14,origCOUNT_142,origCOUNT_160,origCOUNT_166,origCOUNT_188,origCOUNT_194,origCOUNT_20,origCOUNT_212,origCOUNT_218,origCOUNT_240,origCOUNT_246,origCOUNT_264,origCOUNT_270,origCOUNT_292,origCOUNT_298,origCOUNT_316,origCOUNT_322,origCOUNT_344,origCOUNT_350,origCOUNT_368,origCOUNT_374,origCOUNT_396,origCOUNT_402,origCOUNT_42,origCOUNT_430,origCOUNT_436,origCOUNT_454,origCOUNT_460,origCOUNT_48,origCOUNT_482,origCOUNT_488,origCOUNT_506,origCOUNT_512,origCOUNT_534,origCOUNT_540,origCOUNT_558,origCOUNT_564,origCOUNT_586,origCOUNT_592,origCOUNT_610,origCOUNT_616,origCOUNT_638,origCOUNT_644,origCOUNT_666,origCOUNT_672,origCOUNT_694,origCOUNT_700,origCOUNT_72,origCOUNT_78,origDEST_107,origDEST_113,origDEST_13,origDEST_135,origDEST_141,origDEST_159,origDEST_165,origDEST_187,origDEST_19,origDEST_193,origDEST_211,origDEST_217,origDEST_239,origDEST_245,origDEST_263,origDEST_269,origDEST_291,origDEST_297,origDEST_315,origDEST_321,origDEST_343,origDEST_349,origDEST_367,origDEST_373,origDEST_395,origDEST_401,origDEST_41,origDEST_429,origDEST_435,origDEST_453,origDEST_459,origDEST_47,origDEST_481,origDEST_487,origDEST_505,origDEST_511,origDEST_533,origDEST_539,origDEST_557,origDEST_563,origDEST_585,origDEST_591,origDEST_609,origDEST_615,origDEST_637,origDEST_643,origDEST_665,origDEST_671,origDEST_693,origDEST_699,origDEST_71,origDEST_77,ra_711,t1_123,t1_147,t1_175,t1_199,t1_227,t1_251,t1_279,t1_29,t1_303,t1_331,t1_355,t1_383,t1_407,t1_417,t1_441,t1_469,t1_493,t1_521,t1_53,t1_545,t1_573,t1_59,t1_597,t1_625,t1_653,t1_681,t1_705,t1_95,t2_124,t2_148,t2_176,t2_200,t2_228,t2_252,t2_280,t2_30,t2_304,t2_332,t2_356,t2_384,t2_408,t2_418,t2_442,t2_470,t2_494,t2_522,t2_54,t2_546,t2_574,t2_598,t2_60,t2_626,t2_654,t2_682,t2_706,t2_96,t_1,t_103,t_119,t_131,t_155,t_171,t_183,t_207,t_223,t_235,t_259,t_275,t_287,t_311,t_327,t_339,t_363,t_37,t_379,t_391,t_413,t_425,t_449,t_465,t_477,t_5,t_501,t_517,t_529,t_553,t_569,t_581,t_605,t_621,t_633,t_649,t_661,t_67,t_677,t_689,t_83,t_87,t_9,t_91;

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
const unconstrained_134: bv1;
const unconstrained_135: bv1;
const unconstrained_136: bv1;
const unconstrained_137: bv1;
const unconstrained_138: bv1;
const unconstrained_139: bv1;
const unconstrained_14: bv1;
const unconstrained_140: bv1;
const unconstrained_141: bv1;
const unconstrained_142: bv1;
const unconstrained_143: bv1;
const unconstrained_144: bv1;
const unconstrained_145: bv1;
const unconstrained_146: bv1;
const unconstrained_147: bv1;
const unconstrained_148: bv1;
const unconstrained_149: bv1;
const unconstrained_15: bv1;
const unconstrained_150: bv1;
const unconstrained_151: bv1;
const unconstrained_152: bv1;
const unconstrained_153: bv1;
const unconstrained_154: bv1;
const unconstrained_155: bv1;
const unconstrained_156: bv1;
const unconstrained_157: bv1;
const unconstrained_158: bv1;
const unconstrained_159: bv1;
const unconstrained_16: bv1;
const unconstrained_160: bv1;
const unconstrained_161: bv1;
const unconstrained_162: bv1;
const unconstrained_163: bv1;
const unconstrained_164: bv1;
const unconstrained_165: bv1;
const unconstrained_166: bv1;
const unconstrained_167: bv1;
const unconstrained_168: bv1;
const unconstrained_169: bv1;
const unconstrained_17: bv1;
const unconstrained_170: bv1;
const unconstrained_171: bv1;
const unconstrained_172: bv1;
const unconstrained_173: bv1;
const unconstrained_174: bv1;
const unconstrained_175: bv1;
const unconstrained_176: bv1;
const unconstrained_177: bv1;
const unconstrained_178: bv1;
const unconstrained_179: bv1;
const unconstrained_18: bv1;
const unconstrained_180: bv1;
const unconstrained_181: bv1;
const unconstrained_182: bv1;
const unconstrained_183: bv1;
const unconstrained_184: bv1;
const unconstrained_185: bv1;
const unconstrained_186: bv1;
const unconstrained_187: bv1;
const unconstrained_188: bv1;
const unconstrained_189: bv1;
const unconstrained_19: bv1;
const unconstrained_190: bv1;
const unconstrained_191: bv1;
const unconstrained_192: bv1;
const unconstrained_193: bv1;
const unconstrained_194: bv1;
const unconstrained_195: bv1;
const unconstrained_196: bv1;
const unconstrained_197: bv1;
const unconstrained_198: bv1;
const unconstrained_199: bv1;
const unconstrained_2: bv1;
const unconstrained_20: bv1;
const unconstrained_200: bv1;
const unconstrained_201: bv1;
const unconstrained_202: bv1;
const unconstrained_203: bv1;
const unconstrained_204: bv1;
const unconstrained_205: bv1;
const unconstrained_206: bv1;
const unconstrained_207: bv1;
const unconstrained_208: bv1;
const unconstrained_209: bv1;
const unconstrained_21: bv1;
const unconstrained_210: bv1;
const unconstrained_211: bv1;
const unconstrained_212: bv1;
const unconstrained_213: bv1;
const unconstrained_214: bv1;
const unconstrained_215: bv1;
const unconstrained_216: bv1;
const unconstrained_217: bv1;
const unconstrained_218: bv1;
const unconstrained_219: bv1;
const unconstrained_22: bv1;
const unconstrained_220: bv1;
const unconstrained_221: bv1;
const unconstrained_222: bv1;
const unconstrained_223: bv1;
const unconstrained_224: bv1;
const unconstrained_225: bv1;
const unconstrained_226: bv1;
const unconstrained_227: bv1;
const unconstrained_228: bv1;
const unconstrained_229: bv1;
const unconstrained_23: bv1;
const unconstrained_230: bv1;
const unconstrained_231: bv1;
const unconstrained_232: bv1;
const unconstrained_233: bv1;
const unconstrained_234: bv1;
const unconstrained_235: bv1;
const unconstrained_236: bv1;
const unconstrained_237: bv1;
const unconstrained_238: bv1;
const unconstrained_239: bv1;
const unconstrained_24: bv1;
const unconstrained_240: bv1;
const unconstrained_241: bv1;
const unconstrained_242: bv1;
const unconstrained_243: bv1;
const unconstrained_244: bv1;
const unconstrained_245: bv1;
const unconstrained_246: bv1;
const unconstrained_247: bv1;
const unconstrained_248: bv1;
const unconstrained_249: bv1;
const unconstrained_25: bv1;
const unconstrained_250: bv1;
const unconstrained_251: bv1;
const unconstrained_252: bv1;
const unconstrained_253: bv1;
const unconstrained_254: bv1;
const unconstrained_255: bv1;
const unconstrained_256: bv1;
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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_108: bv64;
var origCOUNT_114: bv64;
var origCOUNT_136: bv64;
var origCOUNT_14: bv32;
var origCOUNT_142: bv64;
var origCOUNT_160: bv64;
var origCOUNT_166: bv64;
var origCOUNT_188: bv64;
var origCOUNT_194: bv64;
var origCOUNT_20: bv32;
var origCOUNT_212: bv64;
var origCOUNT_218: bv64;
var origCOUNT_240: bv64;
var origCOUNT_246: bv64;
var origCOUNT_264: bv64;
var origCOUNT_270: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_316: bv64;
var origCOUNT_322: bv64;
var origCOUNT_344: bv64;
var origCOUNT_350: bv64;
var origCOUNT_368: bv64;
var origCOUNT_374: bv64;
var origCOUNT_396: bv64;
var origCOUNT_402: bv64;
var origCOUNT_42: bv64;
var origCOUNT_430: bv64;
var origCOUNT_436: bv64;
var origCOUNT_454: bv64;
var origCOUNT_460: bv64;
var origCOUNT_48: bv64;
var origCOUNT_482: bv64;
var origCOUNT_488: bv64;
var origCOUNT_506: bv64;
var origCOUNT_512: bv64;
var origCOUNT_534: bv64;
var origCOUNT_540: bv64;
var origCOUNT_558: bv64;
var origCOUNT_564: bv64;
var origCOUNT_586: bv64;
var origCOUNT_592: bv64;
var origCOUNT_610: bv64;
var origCOUNT_616: bv64;
var origCOUNT_638: bv64;
var origCOUNT_644: bv64;
var origCOUNT_666: bv64;
var origCOUNT_672: bv64;
var origCOUNT_694: bv64;
var origCOUNT_700: bv64;
var origCOUNT_72: bv64;
var origCOUNT_78: bv64;
var origDEST_107: bv64;
var origDEST_113: bv64;
var origDEST_13: bv32;
var origDEST_135: bv64;
var origDEST_141: bv64;
var origDEST_159: bv64;
var origDEST_165: bv64;
var origDEST_187: bv64;
var origDEST_19: bv32;
var origDEST_193: bv64;
var origDEST_211: bv64;
var origDEST_217: bv64;
var origDEST_239: bv64;
var origDEST_245: bv64;
var origDEST_263: bv64;
var origDEST_269: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_315: bv64;
var origDEST_321: bv64;
var origDEST_343: bv64;
var origDEST_349: bv64;
var origDEST_367: bv64;
var origDEST_373: bv64;
var origDEST_395: bv64;
var origDEST_401: bv64;
var origDEST_41: bv64;
var origDEST_429: bv64;
var origDEST_435: bv64;
var origDEST_453: bv64;
var origDEST_459: bv64;
var origDEST_47: bv64;
var origDEST_481: bv64;
var origDEST_487: bv64;
var origDEST_505: bv64;
var origDEST_511: bv64;
var origDEST_533: bv64;
var origDEST_539: bv64;
var origDEST_557: bv64;
var origDEST_563: bv64;
var origDEST_585: bv64;
var origDEST_591: bv64;
var origDEST_609: bv64;
var origDEST_615: bv64;
var origDEST_637: bv64;
var origDEST_643: bv64;
var origDEST_665: bv64;
var origDEST_671: bv64;
var origDEST_693: bv64;
var origDEST_699: bv64;
var origDEST_71: bv64;
var origDEST_77: bv64;
var ra_711: bv64;
var t1_123: bv64;
var t1_147: bv64;
var t1_175: bv64;
var t1_199: bv64;
var t1_227: bv64;
var t1_251: bv64;
var t1_279: bv64;
var t1_29: bv64;
var t1_303: bv64;
var t1_331: bv64;
var t1_355: bv64;
var t1_383: bv64;
var t1_407: bv64;
var t1_417: bv64;
var t1_441: bv64;
var t1_469: bv64;
var t1_493: bv64;
var t1_521: bv64;
var t1_53: bv64;
var t1_545: bv64;
var t1_573: bv64;
var t1_59: bv64;
var t1_597: bv64;
var t1_625: bv64;
var t1_653: bv64;
var t1_681: bv64;
var t1_705: bv64;
var t1_95: bv64;
var t2_124: bv64;
var t2_148: bv64;
var t2_176: bv64;
var t2_200: bv64;
var t2_228: bv64;
var t2_252: bv64;
var t2_280: bv64;
var t2_30: bv64;
var t2_304: bv64;
var t2_332: bv64;
var t2_356: bv64;
var t2_384: bv64;
var t2_408: bv64;
var t2_418: bv64;
var t2_442: bv64;
var t2_470: bv64;
var t2_494: bv64;
var t2_522: bv64;
var t2_54: bv64;
var t2_546: bv64;
var t2_574: bv64;
var t2_598: bv64;
var t2_60: bv64;
var t2_626: bv64;
var t2_654: bv64;
var t2_682: bv64;
var t2_706: bv64;
var t2_96: bv64;
var t_1: bv64;
var t_103: bv64;
var t_119: bv32;
var t_131: bv64;
var t_155: bv64;
var t_171: bv32;
var t_183: bv64;
var t_207: bv64;
var t_223: bv32;
var t_235: bv64;
var t_259: bv64;
var t_275: bv32;
var t_287: bv64;
var t_311: bv64;
var t_327: bv32;
var t_339: bv64;
var t_363: bv64;
var t_37: bv64;
var t_379: bv32;
var t_391: bv64;
var t_413: bv32;
var t_425: bv64;
var t_449: bv64;
var t_465: bv32;
var t_477: bv64;
var t_5: bv32;
var t_501: bv64;
var t_517: bv32;
var t_529: bv64;
var t_553: bv64;
var t_569: bv32;
var t_581: bv64;
var t_605: bv64;
var t_621: bv32;
var t_633: bv64;
var t_649: bv32;
var t_661: bv64;
var t_67: bv64;
var t_677: bv32;
var t_689: bv64;
var t_83: bv32;
var t_87: bv32;
var t_9: bv32;
var t_91: bv32;


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
