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
axiom _function_addr_low == 5312bv64;
axiom _function_addr_high == 6492bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x14c0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x14c5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x14ca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x14cf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x14d4:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x14d8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), 0bv32);

label_0x14e0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x14e7:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x14ea:
goto label_0x14f4;

label_0x14ec:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x14ef:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x14f1:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x14f4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x14fb:
t_9 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x14fe:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x15b1;
}

label_0x1504:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), 0bv32);

label_0x150c:
goto label_0x1518;

label_0x150e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1512:
t_13 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_13[32:31]) == (1bv32[32:31]))), (XOR_1((t_13[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_13)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1514:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x1518:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x151f:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x1523:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x15ac;
}

label_0x1529:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x152e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x1536:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x153a:
t_21 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, RSP)));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, RSP))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, RSP)))), (XOR_32((RAX[32:0]), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (RAX[32:0]))), (LOAD_LE_32(mem, RSP)))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x153d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15a7;
}

label_0x153f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64)))));

label_0x1544:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, RSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_2);

label_0x1548:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1550:
t1_31 := RCX;
t2_32 := RAX;
RCX := PLUS_64(RCX, t2_32);
CF := bool2bv(LT_64(RCX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1553:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RCX);

label_0x1558:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x155d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1563:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1568:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x156b:
if (bv2bool(ZF)) {
  goto label_0x156e;
}

label_0x156d:
assume false;

label_0x156e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x1573:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_6);

label_0x1577:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x157e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1582:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x1587:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_8);

label_0x158b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_9;
SF := unconstrained_10;
AF := unconstrained_11;
PF := unconstrained_12;

label_0x158f:
if (bv2bool(CF)) {
  goto label_0x1592;
}

label_0x1591:
assume false;

label_0x1592:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x1597:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x159b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x159d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64)));

label_0x15a1:
t_55 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_55[32:31]) == (1bv32[32:31]))), (XOR_1((t_55[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_55)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x15a3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0x15a7:
goto label_0x150e;

label_0x15ac:
goto label_0x14ec;

label_0x15b1:
mem := STORE_LE_32(mem, RSP, 0bv32);

label_0x15b8:
goto label_0x15c2;

label_0x15ba:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x15bd:
t_59 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_59[32:31]) == (1bv32[32:31]))), (XOR_1((t_59[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_59)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x15bf:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x15c2:
t_63 := MINUS_32((LOAD_LE_32(mem, RSP)), 23bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 23bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 23bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_63)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_63, (LOAD_LE_32(mem, RSP)))), 23bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x15c6:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1624;
}

label_0x15c8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x15cc:
origDEST_67 := RAX;
origCOUNT_68 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, RSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_14);

label_0x15d0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x15d5:
t1_73 := RCX;
t2_74 := RAX;
RCX := PLUS_64(RCX, t2_74);
CF := bool2bv(LT_64(RCX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x15d8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RCX);

label_0x15dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x15e2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15e8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15ed:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0x15f0:
if (bv2bool(ZF)) {
  goto label_0x15f3;
}

label_0x15f2:
assume false;

label_0x15f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x15f8:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_18);

label_0x15fc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1603:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1607:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x160c:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_20);

label_0x1610:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_21;
SF := unconstrained_22;
AF := unconstrained_23;
PF := unconstrained_24;

label_0x1614:
if (bv2bool(CF)) {
  goto label_0x1617;
}

label_0x1616:
assume false;

label_0x1617:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x161c:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1622:
goto label_0x15ba;

label_0x1624:
mem := STORE_LE_32(mem, RSP, 0bv32);

label_0x162b:
goto label_0x1635;

label_0x162d:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1630:
t_97 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_97[32:31]) == (1bv32[32:31]))), (XOR_1((t_97[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_97)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1632:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1635:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x163c:
t_101 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x163f:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x16d6;
}

label_0x1645:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1649:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x1651:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x1655:
t_105 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_105[32:31]) == (1bv32[32:31]))), (XOR_1((t_105[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_105)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1657:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x1659:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x165e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x1661:
t_109 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_109[32:31]) == (1bv32[32:31]))), (XOR_1((t_109[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_109)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1663:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), RAX[32:0]);

label_0x1667:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x166b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x1673:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x1677:
t_113 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_113[32:31]) == (1bv32[32:31]))), (XOR_1((t_113[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_113)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1679:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x167b:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, RSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_26);

label_0x167f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1684:
t1_123 := RCX;
t2_124 := RAX;
RCX := PLUS_64(RCX, t2_124);
CF := bool2bv(LT_64(RCX, t1_123));
OF := AND_1((bool2bv((t1_123[64:63]) == (t2_124[64:63]))), (XOR_1((t1_123[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_123)), t2_124)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1687:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0x168c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1691:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1697:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x169c:
t_131 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)), 2bv64)), (XOR_64((RSHIFT_64(t_131, 4bv64)), t_131)))))[1:0]));
SF := t_131[64:63];
ZF := bool2bv(0bv64 == t_131);

label_0x169f:
if (bv2bool(ZF)) {
  goto label_0x16a2;
}

label_0x16a1:
assume false;

label_0x16a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x16a7:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_30);

label_0x16ab:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x16b2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x16b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x16bb:
origDEST_141 := RCX;
origCOUNT_142 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), CF, LSHIFT_64(origDEST_141, (MINUS_64(64bv64, origCOUNT_142)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_142 == 1bv64)), origDEST_141[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_142 == 0bv64)), AF, unconstrained_32);

label_0x16bf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x16c3:
if (bv2bool(CF)) {
  goto label_0x16c6;
}

label_0x16c5:
assume false;

label_0x16c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x16cb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 72bv64)));

label_0x16cf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x16d1:
goto label_0x162d;

label_0x16d6:
mem := STORE_LE_32(mem, RSP, 1bv32);

label_0x16dd:
goto label_0x16e7;

label_0x16df:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x16e2:
t_147 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_147[32:31]) == (1bv32[32:31]))), (XOR_1((t_147[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_147)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x16e4:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x16e7:
t_151 := MINUS_32((LOAD_LE_32(mem, RSP)), 23bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 23bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 23bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_151)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_151, (LOAD_LE_32(mem, RSP)))), 23bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)), 2bv32)), (XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)), 2bv32)), (XOR_32((RSHIFT_32(t_151, 4bv32)), t_151)))))[1:0]));
SF := t_151[32:31];
ZF := bool2bv(0bv32 == t_151);

label_0x16eb:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1773;
}

label_0x16f1:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x16f5:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x16f8:
t_155 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_155, 1bv32)), (XOR_32(t_155, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_155)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x16fa:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x16fd:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1702:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1707:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(R8, (LSHIFT_64(RCX, 2bv64)))));

label_0x170b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RAX, 2bv64)))));

label_0x170e:
t1_159 := RAX[32:0];
t2_160 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_160));
CF := bool2bv(LT_32((RAX[32:0]), t1_159));
OF := AND_1((bool2bv((t1_159[32:31]) == (t2_160[32:31]))), (XOR_1((t1_159[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_159)), t2_160)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1710:
mem := STORE_LE_32(mem, PLUS_64(RSP, 76bv64), RAX[32:0]);

label_0x1714:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1718:
origDEST_165 := RAX;
origCOUNT_166 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, RSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_38);

label_0x171c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1721:
t1_171 := RCX;
t2_172 := RAX;
RCX := PLUS_64(RCX, t2_172);
CF := bool2bv(LT_64(RCX, t1_171));
OF := AND_1((bool2bv((t1_171[64:63]) == (t2_172[64:63]))), (XOR_1((t1_171[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_171)), t2_172)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1724:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RCX);

label_0x1729:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x172e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_39;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1734:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1739:
t_179 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_40;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))))[1:0]));
SF := t_179[64:63];
ZF := bool2bv(0bv64 == t_179);

label_0x173c:
if (bv2bool(ZF)) {
  goto label_0x173f;
}

label_0x173e:
assume false;

label_0x173f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1744:
origDEST_183 := RAX;
origCOUNT_184 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_42);

label_0x1748:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x174f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1753:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1758:
origDEST_189 := RCX;
origCOUNT_190 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_44);

label_0x175c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_45;
SF := unconstrained_46;
AF := unconstrained_47;
PF := unconstrained_48;

label_0x1760:
if (bv2bool(CF)) {
  goto label_0x1763;
}

label_0x1762:
assume false;

label_0x1763:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1768:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 76bv64)));

label_0x176c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x176e:
goto label_0x16df;

label_0x1773:
mem := STORE_LE_32(mem, RSP, 0bv32);

label_0x177a:
goto label_0x1784;

label_0x177c:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x177f:
t_195 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_195[32:31]) == (1bv32[32:31]))), (XOR_1((t_195[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_195)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1781:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1784:
t_199 := MINUS_32((LOAD_LE_32(mem, RSP)), 23bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 23bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 23bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_199)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_199, (LOAD_LE_32(mem, RSP)))), 23bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_199, 4bv32)), t_199)), 2bv32)), (XOR_32((RSHIFT_32(t_199, 4bv32)), t_199)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_199, 4bv32)), t_199)), 2bv32)), (XOR_32((RSHIFT_32(t_199, 4bv32)), t_199)))))[1:0]));
SF := t_199[32:31];
ZF := bool2bv(0bv32 == t_199);

label_0x1788:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x17e6;
}

label_0x178a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x178e:
origDEST_203 := RAX;
origCOUNT_204 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), CF, RSHIFT_64(origDEST_203, (MINUS_64(64bv64, origCOUNT_204)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), AF, unconstrained_50);

label_0x1792:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1797:
t1_209 := RCX;
t2_210 := RAX;
RCX := PLUS_64(RCX, t2_210);
CF := bool2bv(LT_64(RCX, t1_209));
OF := AND_1((bool2bv((t1_209[64:63]) == (t2_210[64:63]))), (XOR_1((t1_209[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_209)), t2_210)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x179a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RCX);

label_0x179f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x17a4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17aa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17af:
t_217 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))))[1:0]));
SF := t_217[64:63];
ZF := bool2bv(0bv64 == t_217);

label_0x17b2:
if (bv2bool(ZF)) {
  goto label_0x17b5;
}

label_0x17b4:
assume false;

label_0x17b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x17ba:
origDEST_221 := RAX;
origCOUNT_222 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), CF, LSHIFT_64(origDEST_221, (MINUS_64(64bv64, origCOUNT_222)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_222 == 1bv64)), origDEST_221[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), AF, unconstrained_54);

label_0x17be:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x17c5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17c9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x17ce:
origDEST_227 := RCX;
origCOUNT_228 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_56);

label_0x17d2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x17d6:
if (bv2bool(CF)) {
  goto label_0x17d9;
}

label_0x17d8:
assume false;

label_0x17d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x17de:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x17e4:
goto label_0x177c;

label_0x17e6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), 0bv32);

label_0x17ee:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x17f5:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x17f8:
goto label_0x1802;

label_0x17fa:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x17fd:
t_233 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_233[32:31]) == (1bv32[32:31]))), (XOR_1((t_233[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_233)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x17ff:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1802:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x1809:
t_237 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_237)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_237, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))))[1:0]));
SF := t_237[32:31];
ZF := bool2bv(0bv32 == t_237);

label_0x180c:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x18af;
}

label_0x1812:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1815:
t_241 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_241[32:31]) == (1bv32[32:31]))), (XOR_1((t_241[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_241)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1817:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x1819:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x181d:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1822:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1827:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(R8, (LSHIFT_64(RCX, 2bv64)))));

label_0x182b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RAX, 2bv64)))));

label_0x182e:
t_245 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_245, (RCX[32:0])));
OF := AND_32((XOR_32(t_245, (RCX[32:0]))), (XOR_32(t_245, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_245)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1830:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x1834:
t1_249 := RCX[32:0];
t2_250 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_250));
CF := bool2bv(LT_32((RCX[32:0]), t1_249));
OF := AND_1((bool2bv((t1_249[32:31]) == (t2_250[32:31]))), (XOR_1((t1_249[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_249)), t2_250)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1836:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1838:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x183c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x1840:
t_255 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_255, 1bv32)), (XOR_32(t_255, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_255)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1842:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x1846:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x184a:
origDEST_259 := RAX;
origCOUNT_260 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), CF, RSHIFT_64(origDEST_259, (MINUS_64(64bv64, origCOUNT_260)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_260 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), AF, unconstrained_62);

label_0x184e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1853:
t1_265 := RCX;
t2_266 := RAX;
RCX := PLUS_64(RCX, t2_266);
CF := bool2bv(LT_64(RCX, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1856:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RCX);

label_0x185b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1860:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1866:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x186b:
t_273 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_64;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)), 2bv64)), (XOR_64((RSHIFT_64(t_273, 4bv64)), t_273)))))[1:0]));
SF := t_273[64:63];
ZF := bool2bv(0bv64 == t_273);

label_0x186e:
if (bv2bool(ZF)) {
  goto label_0x1871;
}

label_0x1870:
assume false;

label_0x1871:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1876:
origDEST_277 := RAX;
origCOUNT_278 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), CF, LSHIFT_64(origDEST_277, (MINUS_64(64bv64, origCOUNT_278)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_278 == 1bv64)), origDEST_277[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_278 == 0bv64)), AF, unconstrained_66);

label_0x187a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1881:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1885:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x188a:
origDEST_283 := RCX;
origCOUNT_284 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), CF, LSHIFT_64(origDEST_283, (MINUS_64(64bv64, origCOUNT_284)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_284 == 1bv64)), origDEST_283[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), AF, unconstrained_68);

label_0x188e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_69;
SF := unconstrained_70;
AF := unconstrained_71;
PF := unconstrained_72;

label_0x1892:
if (bv2bool(CF)) {
  goto label_0x1895;
}

label_0x1894:
assume false;

label_0x1895:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x189a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0x189e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x18a0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x18a4:
origDEST_289 := RAX[32:0];
origCOUNT_290 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), CF, RSHIFT_32(origDEST_289, (MINUS_32(32bv32, origCOUNT_290)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_290 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv32)), AF, unconstrained_74);

label_0x18a6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x18aa:
goto label_0x17fa;

label_0x18af:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x18b6:
t_295 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_295[32:31]) == (1bv32[32:31]))), (XOR_1((t_295[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_295)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x18b8:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x18bb:
goto label_0x18c5;

label_0x18bd:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x18c0:
t_299 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_299[32:31]) == (1bv32[32:31]))), (XOR_1((t_299[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_299)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x18c2:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x18c5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x18cc:
t_303 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_303)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_303, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)), 2bv32)), (XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)), 2bv32)), (XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)))))[1:0]));
SF := t_303[32:31];
ZF := bool2bv(0bv32 == t_303);

label_0x18cf:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x1957;
}

label_0x18d5:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x18d8:
t_307 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_307, 1bv32)), (XOR_32(t_307, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_307)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x18da:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x18dc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x18e1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x18e4:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RAX)), 2bv64)[32:0]);

label_0x18e8:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x18ec:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x18f1:
t_311 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
CF := bool2bv(LT_32(t_311, (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := AND_32((XOR_32(t_311, (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64))))))), (XOR_32(t_311, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_311)), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64))))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x18f4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), RAX[32:0]);

label_0x18f8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x18fc:
origDEST_315 := RAX;
origCOUNT_316 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, RSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_76);

label_0x1900:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x1905:
t1_321 := RCX;
t2_322 := RAX;
RCX := PLUS_64(RCX, t2_322);
CF := bool2bv(LT_64(RCX, t1_321));
OF := AND_1((bool2bv((t1_321[64:63]) == (t2_322[64:63]))), (XOR_1((t1_321[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_321)), t2_322)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1908:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0x190d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1912:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1918:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x191d:
t_329 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)), 2bv64)), (XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)), 2bv64)), (XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)))))[1:0]));
SF := t_329[64:63];
ZF := bool2bv(0bv64 == t_329);

label_0x1920:
if (bv2bool(ZF)) {
  goto label_0x1923;
}

label_0x1922:
assume false;

label_0x1923:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1928:
origDEST_333 := RAX;
origCOUNT_334 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), CF, LSHIFT_64(origDEST_333, (MINUS_64(64bv64, origCOUNT_334)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_334 == 1bv64)), origDEST_333[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), AF, unconstrained_80);

label_0x192c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1933:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1937:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x193c:
origDEST_339 := RCX;
origCOUNT_340 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), CF, LSHIFT_64(origDEST_339, (MINUS_64(64bv64, origCOUNT_340)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_340 == 1bv64)), origDEST_339[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), AF, unconstrained_82);

label_0x1940:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x1944:
if (bv2bool(CF)) {
  goto label_0x1947;
}

label_0x1946:
assume false;

label_0x1947:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x194c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 84bv64)));

label_0x1950:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1952:
goto label_0x18bd;

label_0x1957:
t1_345 := RSP;
t2_346 := 104bv64;
RSP := PLUS_64(RSP, t2_346);
CF := bool2bv(LT_64(RSP, t1_345));
OF := AND_1((bool2bv((t1_345[64:63]) == (t2_346[64:63]))), (XOR_1((t1_345[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_345)), t2_346)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x195b:

ra_351 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_118,origCOUNT_136,origCOUNT_142,origCOUNT_166,origCOUNT_184,origCOUNT_190,origCOUNT_204,origCOUNT_222,origCOUNT_228,origCOUNT_26,origCOUNT_260,origCOUNT_278,origCOUNT_284,origCOUNT_290,origCOUNT_316,origCOUNT_334,origCOUNT_340,origCOUNT_44,origCOUNT_50,origCOUNT_68,origCOUNT_86,origCOUNT_92,origDEST_117,origDEST_135,origDEST_141,origDEST_165,origDEST_183,origDEST_189,origDEST_203,origDEST_221,origDEST_227,origDEST_25,origDEST_259,origDEST_277,origDEST_283,origDEST_289,origDEST_315,origDEST_333,origDEST_339,origDEST_43,origDEST_49,origDEST_67,origDEST_85,origDEST_91,ra_351,t1_123,t1_159,t1_171,t1_209,t1_249,t1_265,t1_31,t1_321,t1_345,t1_73,t2_124,t2_160,t2_172,t2_210,t2_250,t2_266,t2_32,t2_322,t2_346,t2_74,t_1,t_101,t_105,t_109,t_113,t_13,t_131,t_147,t_151,t_155,t_17,t_179,t_195,t_199,t_21,t_217,t_233,t_237,t_241,t_245,t_255,t_273,t_295,t_299,t_303,t_307,t_311,t_329,t_39,t_5,t_55,t_59,t_63,t_81,t_9,t_97;

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
var origCOUNT_118: bv64;
var origCOUNT_136: bv64;
var origCOUNT_142: bv64;
var origCOUNT_166: bv64;
var origCOUNT_184: bv64;
var origCOUNT_190: bv64;
var origCOUNT_204: bv64;
var origCOUNT_222: bv64;
var origCOUNT_228: bv64;
var origCOUNT_26: bv64;
var origCOUNT_260: bv64;
var origCOUNT_278: bv64;
var origCOUNT_284: bv64;
var origCOUNT_290: bv32;
var origCOUNT_316: bv64;
var origCOUNT_334: bv64;
var origCOUNT_340: bv64;
var origCOUNT_44: bv64;
var origCOUNT_50: bv64;
var origCOUNT_68: bv64;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_117: bv64;
var origDEST_135: bv64;
var origDEST_141: bv64;
var origDEST_165: bv64;
var origDEST_183: bv64;
var origDEST_189: bv64;
var origDEST_203: bv64;
var origDEST_221: bv64;
var origDEST_227: bv64;
var origDEST_25: bv64;
var origDEST_259: bv64;
var origDEST_277: bv64;
var origDEST_283: bv64;
var origDEST_289: bv32;
var origDEST_315: bv64;
var origDEST_333: bv64;
var origDEST_339: bv64;
var origDEST_43: bv64;
var origDEST_49: bv64;
var origDEST_67: bv64;
var origDEST_85: bv64;
var origDEST_91: bv64;
var ra_351: bv64;
var t1_123: bv64;
var t1_159: bv32;
var t1_171: bv64;
var t1_209: bv64;
var t1_249: bv32;
var t1_265: bv64;
var t1_31: bv64;
var t1_321: bv64;
var t1_345: bv64;
var t1_73: bv64;
var t2_124: bv64;
var t2_160: bv32;
var t2_172: bv64;
var t2_210: bv64;
var t2_250: bv32;
var t2_266: bv64;
var t2_32: bv64;
var t2_322: bv64;
var t2_346: bv64;
var t2_74: bv64;
var t_1: bv64;
var t_101: bv32;
var t_105: bv32;
var t_109: bv32;
var t_113: bv32;
var t_13: bv32;
var t_131: bv64;
var t_147: bv32;
var t_151: bv32;
var t_155: bv32;
var t_17: bv32;
var t_179: bv64;
var t_195: bv32;
var t_199: bv32;
var t_21: bv32;
var t_217: bv64;
var t_233: bv32;
var t_237: bv32;
var t_241: bv32;
var t_245: bv32;
var t_255: bv32;
var t_273: bv64;
var t_295: bv32;
var t_299: bv32;
var t_303: bv32;
var t_307: bv32;
var t_311: bv32;
var t_329: bv64;
var t_39: bv64;
var t_5: bv32;
var t_55: bv32;
var t_59: bv32;
var t_63: bv32;
var t_81: bv64;
var t_9: bv32;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(256bv64);
axiom policy(5312bv64);
