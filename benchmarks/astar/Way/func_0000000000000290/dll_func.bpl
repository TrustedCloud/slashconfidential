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
axiom _function_addr_low == 656bv64;
axiom _function_addr_high == 5408bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x290:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x295:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x29a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x29f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x2a4:
t_1 := RSP;
RSP := MINUS_64(RSP, 424bv64);
CF := bool2bv(LT_64(t_1, 424bv64));
OF := AND_64((XOR_64(t_1, 424bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 424bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x2b3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0x2b6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0x2ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x2c2:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 128bv64));

label_0x2c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RAX);

label_0x2ce:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), 0bv32);

label_0x2d6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), 0bv32);

label_0x2de:
goto label_0x2ea;

label_0x2e0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0x2e4:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2e6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), RAX[32:0]);

label_0x2ea:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 448bv64)));

label_0x2f1:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x2f5:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1505;
}

label_0x2fb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)))));

label_0x300:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x308:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x30b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0x30f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x313:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x317:
t_13 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_13, (RAX[32:0])));
OF := AND_32((XOR_32(t_13, (RAX[32:0]))), (XOR_32(t_13, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_13)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x319:
RAX := (0bv32 ++ RCX[32:0]);

label_0x31b:
t_17 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_17, 1bv32)), (XOR_32(t_17, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_17)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x31d:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x320:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x324:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x329:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x32d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x335:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x33c:
t_21 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x33e:
if (bv2bool(ZF)) {
  goto label_0x526;
}

label_0x344:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x348:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x350:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x354:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x358:
t_25 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x35a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x526;
}

label_0x360:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x365:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, RSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_3);

label_0x369:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x371:
t1_35 := RCX;
t2_36 := RAX;
RCX := PLUS_64(RCX, t2_36);
CF := bool2bv(LT_64(RCX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x374:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0x379:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x37e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x384:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x389:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x38c:
if (bv2bool(ZF)) {
  goto label_0x38f;
}

label_0x38e:
assume false;

label_0x38f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x394:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_7);

label_0x398:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x39f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3a8:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_9);

label_0x3ac:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_10;
SF := unconstrained_11;
AF := unconstrained_12;
PF := unconstrained_13;

label_0x3b0:
if (bv2bool(CF)) {
  goto label_0x3b3;
}

label_0x3b2:
assume false;

label_0x3b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3b8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x3bb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3bd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3c1:
t_59 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_59[32:31]) == (1bv32[32:31]))), (XOR_1((t_59[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_59)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3c3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x3cf:
t1_63 := RAX;
t2_64 := 170bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0x3dd:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x3e1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x3e6:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x3ea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x3ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x3f4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3fa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3ff:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x402:
if (bv2bool(ZF)) {
  goto label_0x405;
}

label_0x404:
assume false;

label_0x405:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x40a:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_17);

label_0x40e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x415:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x419:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x41e:
origDEST_81 := RCX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_19);

label_0x422:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_20;
SF := unconstrained_21;
AF := unconstrained_22;
PF := unconstrained_23;

label_0x426:
if (bv2bool(CF)) {
  goto label_0x429;
}

label_0x428:
assume false;

label_0x429:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x42e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x436:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x439:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x43c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x444:
t1_87 := RAX;
t2_88 := 168bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x44a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0x452:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x456:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x45b:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x45f:
t1_93 := RAX;
t2_94 := 2bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x463:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x468:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x46d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x473:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x478:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x47b:
if (bv2bool(ZF)) {
  goto label_0x47e;
}

label_0x47d:
assume false;

label_0x47e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x483:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_27);

label_0x487:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x48e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x492:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x497:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_29);

label_0x49b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_30;
SF := unconstrained_31;
AF := unconstrained_32;
PF := unconstrained_33;

label_0x49f:
if (bv2bool(CF)) {
  goto label_0x4a2;
}

label_0x4a1:
assume false;

label_0x4a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4a7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x4af:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x4b2:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x4b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x4bd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x4c3:
t_117 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_117)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_117, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x4c6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x526;
}

label_0x4c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x4d0:
t1_121 := RAX;
t2_122 := 160bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x4db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x4e0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4eb:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x4ee:
if (bv2bool(ZF)) {
  goto label_0x4f1;
}

label_0x4f0:
assume false;

label_0x4f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x4f6:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_37);

label_0x4fa:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x501:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x505:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x50a:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_38));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_39);

label_0x50e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_40;
SF := unconstrained_41;
AF := unconstrained_42;
PF := unconstrained_43;

label_0x512:
if (bv2bool(CF)) {
  goto label_0x515;
}

label_0x514:
assume false;

label_0x515:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x51a:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x51d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x521:
goto label_0x1509;

label_0x526:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x52a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x52e:
t_145 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_145, (RAX[32:0])));
OF := AND_32((XOR_32(t_145, (RAX[32:0]))), (XOR_32(t_145, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_145)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x530:
RAX := (0bv32 ++ RCX[32:0]);

label_0x532:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x535:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x539:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x53e:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x542:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x54a:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x551:
t_149 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_149)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_149, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))))[1:0]));
SF := t_149[32:31];
ZF := bool2bv(0bv32 == t_149);

label_0x553:
if (bv2bool(ZF)) {
  goto label_0x73b;
}

label_0x559:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x55d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x565:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x569:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x56d:
t_153 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))))[1:0]));
SF := t_153[32:31];
ZF := bool2bv(0bv32 == t_153);

label_0x56f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x73b;
}

label_0x575:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x57a:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, RSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_46);

label_0x57e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x586:
t1_163 := RCX;
t2_164 := RAX;
RCX := PLUS_64(RCX, t2_164);
CF := bool2bv(LT_64(RCX, t1_163));
OF := AND_1((bool2bv((t1_163[64:63]) == (t2_164[64:63]))), (XOR_1((t1_163[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_163)), t2_164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x589:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0x58e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x593:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x599:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x59e:
t_171 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))))[1:0]));
SF := t_171[64:63];
ZF := bool2bv(0bv64 == t_171);

label_0x5a1:
if (bv2bool(ZF)) {
  goto label_0x5a4;
}

label_0x5a3:
assume false;

label_0x5a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x5a9:
origDEST_175 := RAX;
origCOUNT_176 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_50);

label_0x5ad:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5b4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5b8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x5bd:
origDEST_181 := RCX;
origCOUNT_182 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_52);

label_0x5c1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x5c5:
if (bv2bool(CF)) {
  goto label_0x5c8;
}

label_0x5c7:
assume false;

label_0x5c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x5cd:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x5d0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5d2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x5d6:
t_187 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_187[32:31]) == (1bv32[32:31]))), (XOR_1((t_187[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_187)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5d8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x5dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x5e4:
t1_191 := RAX;
t2_192 := 170bv64;
RAX := PLUS_64(RAX, t2_192);
CF := bool2bv(LT_64(RAX, t1_191));
OF := AND_1((bool2bv((t1_191[64:63]) == (t2_192[64:63]))), (XOR_1((t1_191[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_191)), t2_192)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5ea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0x5f2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x5f6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x5fb:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x5ff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x604:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x609:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x60f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x614:
t_199 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x617:
if (bv2bool(ZF)) {
  goto label_0x61a;
}

label_0x619:
assume false;

label_0x61a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x61f:
origDEST_203 := RAX;
origCOUNT_204 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), CF, LSHIFT_64(origDEST_203, (MINUS_64(64bv64, origCOUNT_204)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv64)), origDEST_203[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv64)), AF, unconstrained_60);

label_0x623:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x62a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x62e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x633:
origDEST_209 := RCX;
origCOUNT_210 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_62);

label_0x637:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_63;
SF := unconstrained_64;
AF := unconstrained_65;
PF := unconstrained_66;

label_0x63b:
if (bv2bool(CF)) {
  goto label_0x63e;
}

label_0x63d:
assume false;

label_0x63e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x643:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x64b:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x64e:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x651:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x659:
t1_215 := RAX;
t2_216 := 168bv64;
RAX := PLUS_64(RAX, t2_216);
CF := bool2bv(LT_64(RAX, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x65f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RAX);

label_0x667:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x66b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x670:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x674:
t1_221 := RAX;
t2_222 := 2bv64;
RAX := PLUS_64(RAX, t2_222);
CF := bool2bv(LT_64(RAX, t1_221));
OF := AND_1((bool2bv((t1_221[64:63]) == (t2_222[64:63]))), (XOR_1((t1_221[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_221)), t2_222)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x678:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x67d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x682:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_67;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x688:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x68d:
t_229 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))))[1:0]));
SF := t_229[64:63];
ZF := bool2bv(0bv64 == t_229);

label_0x690:
if (bv2bool(ZF)) {
  goto label_0x693;
}

label_0x692:
assume false;

label_0x693:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x698:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_70);

label_0x69c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6a3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x6a7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x6ac:
origDEST_239 := RCX;
origCOUNT_240 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_72);

label_0x6b0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_73;
SF := unconstrained_74;
AF := unconstrained_75;
PF := unconstrained_76;

label_0x6b4:
if (bv2bool(CF)) {
  goto label_0x6b7;
}

label_0x6b6:
assume false;

label_0x6b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x6bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x6c4:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x6c7:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x6ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x6d2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x6d8:
t_245 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_245)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_245, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))))[1:0]));
SF := t_245[32:31];
ZF := bool2bv(0bv32 == t_245);

label_0x6db:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x73b;
}

label_0x6dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x6e5:
t1_249 := RAX;
t2_250 := 160bv64;
RAX := PLUS_64(RAX, t2_250);
CF := bool2bv(LT_64(RAX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6eb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x6f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x6f5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x6fb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x700:
t_257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))))[1:0]));
SF := t_257[64:63];
ZF := bool2bv(0bv64 == t_257);

label_0x703:
if (bv2bool(ZF)) {
  goto label_0x706;
}

label_0x705:
assume false;

label_0x706:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x70b:
origDEST_261 := RAX;
origCOUNT_262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_80);

label_0x70f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x716:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x71a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x71f:
origDEST_267 := RCX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_82);

label_0x723:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x727:
if (bv2bool(CF)) {
  goto label_0x72a;
}

label_0x729:
assume false;

label_0x72a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x72f:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x732:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x736:
goto label_0x1509;

label_0x73b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x73f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x743:
t_273 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_273, (RAX[32:0])));
OF := AND_32((XOR_32(t_273, (RAX[32:0]))), (XOR_32(t_273, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_273)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x745:
RAX := (0bv32 ++ RCX[32:0]);

label_0x747:
t_277 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_277[32:31]) == (1bv32[32:31]))), (XOR_1((t_277[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_277)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x749:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x74c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x750:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x755:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x759:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x761:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x768:
t_281 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_281)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_281, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_281, 4bv32)), t_281)), 2bv32)), (XOR_32((RSHIFT_32(t_281, 4bv32)), t_281)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_281, 4bv32)), t_281)), 2bv32)), (XOR_32((RSHIFT_32(t_281, 4bv32)), t_281)))))[1:0]));
SF := t_281[32:31];
ZF := bool2bv(0bv32 == t_281);

label_0x76a:
if (bv2bool(ZF)) {
  goto label_0x952;
}

label_0x770:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x774:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x77c:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x780:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x784:
t_285 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_285, 4bv32)), t_285)), 2bv32)), (XOR_32((RSHIFT_32(t_285, 4bv32)), t_285)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_285, 4bv32)), t_285)), 2bv32)), (XOR_32((RSHIFT_32(t_285, 4bv32)), t_285)))))[1:0]));
SF := t_285[32:31];
ZF := bool2bv(0bv32 == t_285);

label_0x786:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x952;
}

label_0x78c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x791:
origDEST_289 := RAX;
origCOUNT_290 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), CF, RSHIFT_64(origDEST_289, (MINUS_64(64bv64, origCOUNT_290)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_290 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), AF, unconstrained_89);

label_0x795:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x79d:
t1_295 := RCX;
t2_296 := RAX;
RCX := PLUS_64(RCX, t2_296);
CF := bool2bv(LT_64(RCX, t1_295));
OF := AND_1((bool2bv((t1_295[64:63]) == (t2_296[64:63]))), (XOR_1((t1_295[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_295)), t2_296)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7a0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RCX);

label_0x7a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7aa:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7b0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7b5:
t_303 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)), 2bv64)), (XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)), 2bv64)), (XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)))))[1:0]));
SF := t_303[64:63];
ZF := bool2bv(0bv64 == t_303);

label_0x7b8:
if (bv2bool(ZF)) {
  goto label_0x7bb;
}

label_0x7ba:
assume false;

label_0x7bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7c0:
origDEST_307 := RAX;
origCOUNT_308 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), CF, LSHIFT_64(origDEST_307, (MINUS_64(64bv64, origCOUNT_308)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_308 == 1bv64)), origDEST_307[64:63], unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_308 == 0bv64)), AF, unconstrained_93);

label_0x7c4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7cb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7d4:
origDEST_313 := RCX;
origCOUNT_314 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), CF, LSHIFT_64(origDEST_313, (MINUS_64(64bv64, origCOUNT_314)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_314 == 1bv64)), origDEST_313[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_314 == 0bv64)), AF, unconstrained_95);

label_0x7d8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_96;
SF := unconstrained_97;
AF := unconstrained_98;
PF := unconstrained_99;

label_0x7dc:
if (bv2bool(CF)) {
  goto label_0x7df;
}

label_0x7de:
assume false;

label_0x7df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7e4:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x7e7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x7e9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x7ed:
t_319 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_319[32:31]) == (1bv32[32:31]))), (XOR_1((t_319[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_319)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x7ef:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x7f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x7fb:
t1_323 := RAX;
t2_324 := 170bv64;
RAX := PLUS_64(RAX, t2_324);
CF := bool2bv(LT_64(RAX, t1_323));
OF := AND_1((bool2bv((t1_323[64:63]) == (t2_324[64:63]))), (XOR_1((t1_323[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_323)), t2_324)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x801:
mem := STORE_LE_64(mem, PLUS_64(RSP, 320bv64), RAX);

label_0x809:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x80d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x812:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x816:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x81b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x820:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x826:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x82b:
t_331 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_331, 4bv64)), t_331)), 2bv64)), (XOR_64((RSHIFT_64(t_331, 4bv64)), t_331)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_331, 4bv64)), t_331)), 2bv64)), (XOR_64((RSHIFT_64(t_331, 4bv64)), t_331)))))[1:0]));
SF := t_331[64:63];
ZF := bool2bv(0bv64 == t_331);

label_0x82e:
if (bv2bool(ZF)) {
  goto label_0x831;
}

label_0x830:
assume false;

label_0x831:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x836:
origDEST_335 := RAX;
origCOUNT_336 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), CF, LSHIFT_64(origDEST_335, (MINUS_64(64bv64, origCOUNT_336)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_336 == 1bv64)), origDEST_335[64:63], unconstrained_102));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), AF, unconstrained_103);

label_0x83a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x841:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x845:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x84a:
origDEST_341 := RCX;
origCOUNT_342 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), CF, LSHIFT_64(origDEST_341, (MINUS_64(64bv64, origCOUNT_342)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_342 == 1bv64)), origDEST_341[64:63], unconstrained_104));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_342 == 0bv64)), AF, unconstrained_105);

label_0x84e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_106;
SF := unconstrained_107;
AF := unconstrained_108;
PF := unconstrained_109;

label_0x852:
if (bv2bool(CF)) {
  goto label_0x855;
}

label_0x854:
assume false;

label_0x855:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x85a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x862:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x865:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x868:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x870:
t1_347 := RAX;
t2_348 := 168bv64;
RAX := PLUS_64(RAX, t2_348);
CF := bool2bv(LT_64(RAX, t1_347));
OF := AND_1((bool2bv((t1_347[64:63]) == (t2_348[64:63]))), (XOR_1((t1_347[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_347)), t2_348)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x876:
mem := STORE_LE_64(mem, PLUS_64(RSP, 328bv64), RAX);

label_0x87e:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x882:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x887:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x88b:
t1_353 := RAX;
t2_354 := 2bv64;
RAX := PLUS_64(RAX, t2_354);
CF := bool2bv(LT_64(RAX, t1_353));
OF := AND_1((bool2bv((t1_353[64:63]) == (t2_354[64:63]))), (XOR_1((t1_353[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_353)), t2_354)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x88f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x894:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x899:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_110;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x89f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8a4:
t_361 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_111;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)), 2bv64)), (XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)), 2bv64)), (XOR_64((RSHIFT_64(t_361, 4bv64)), t_361)))))[1:0]));
SF := t_361[64:63];
ZF := bool2bv(0bv64 == t_361);

label_0x8a7:
if (bv2bool(ZF)) {
  goto label_0x8aa;
}

label_0x8a9:
assume false;

label_0x8aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x8af:
origDEST_365 := RAX;
origCOUNT_366 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), CF, LSHIFT_64(origDEST_365, (MINUS_64(64bv64, origCOUNT_366)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_366 == 1bv64)), origDEST_365[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), AF, unconstrained_113);

label_0x8b3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8ba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x8c3:
origDEST_371 := RCX;
origCOUNT_372 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), CF, LSHIFT_64(origDEST_371, (MINUS_64(64bv64, origCOUNT_372)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_372 == 1bv64)), origDEST_371[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_372 == 0bv64)), AF, unconstrained_115);

label_0x8c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_116;
SF := unconstrained_117;
AF := unconstrained_118;
PF := unconstrained_119;

label_0x8cb:
if (bv2bool(CF)) {
  goto label_0x8ce;
}

label_0x8cd:
assume false;

label_0x8ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x8d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x8db:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x8de:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x8e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x8e9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x8ef:
t_377 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_377)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_377, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)), 2bv32)), (XOR_32((RSHIFT_32(t_377, 4bv32)), t_377)))))[1:0]));
SF := t_377[32:31];
ZF := bool2bv(0bv32 == t_377);

label_0x8f2:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x952;
}

label_0x8f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x8fc:
t1_381 := RAX;
t2_382 := 160bv64;
RAX := PLUS_64(RAX, t2_382);
CF := bool2bv(LT_64(RAX, t1_381));
OF := AND_1((bool2bv((t1_381[64:63]) == (t2_382[64:63]))), (XOR_1((t1_381[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_381)), t2_382)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x902:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x907:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x90c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_120;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x912:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x917:
t_389 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_121;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)), 2bv64)), (XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)), 2bv64)), (XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)))))[1:0]));
SF := t_389[64:63];
ZF := bool2bv(0bv64 == t_389);

label_0x91a:
if (bv2bool(ZF)) {
  goto label_0x91d;
}

label_0x91c:
assume false;

label_0x91d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x922:
origDEST_393 := RAX;
origCOUNT_394 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), CF, LSHIFT_64(origDEST_393, (MINUS_64(64bv64, origCOUNT_394)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_394 == 1bv64)), origDEST_393[64:63], unconstrained_122));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), AF, unconstrained_123);

label_0x926:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x92d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x931:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x936:
origDEST_399 := RCX;
origCOUNT_400 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), CF, LSHIFT_64(origDEST_399, (MINUS_64(64bv64, origCOUNT_400)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_400 == 1bv64)), origDEST_399[64:63], unconstrained_124));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), AF, unconstrained_125);

label_0x93a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_126;
SF := unconstrained_127;
AF := unconstrained_128;
PF := unconstrained_129;

label_0x93e:
if (bv2bool(CF)) {
  goto label_0x941;
}

label_0x940:
assume false;

label_0x941:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x946:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x949:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x94d:
goto label_0x1509;

label_0x952:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x956:
t_405 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_405, 1bv32)), (XOR_32(t_405, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_405)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x958:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x95b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x95f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x964:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x968:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x970:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x977:
t_409 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_409)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_409, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_409, 4bv32)), t_409)), 2bv32)), (XOR_32((RSHIFT_32(t_409, 4bv32)), t_409)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_409, 4bv32)), t_409)), 2bv32)), (XOR_32((RSHIFT_32(t_409, 4bv32)), t_409)))))[1:0]));
SF := t_409[32:31];
ZF := bool2bv(0bv32 == t_409);

label_0x979:
if (bv2bool(ZF)) {
  goto label_0xb9d;
}

label_0x97f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x983:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x98b:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x98f:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x993:
t_413 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_130;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_413, 4bv32)), t_413)), 2bv32)), (XOR_32((RSHIFT_32(t_413, 4bv32)), t_413)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_413, 4bv32)), t_413)), 2bv32)), (XOR_32((RSHIFT_32(t_413, 4bv32)), t_413)))))[1:0]));
SF := t_413[32:31];
ZF := bool2bv(0bv32 == t_413);

label_0x995:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb9d;
}

label_0x99b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x9a0:
origDEST_417 := RAX;
origCOUNT_418 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), CF, RSHIFT_64(origDEST_417, (MINUS_64(64bv64, origCOUNT_418)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_418 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_131));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), AF, unconstrained_132);

label_0x9a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x9ac:
t1_423 := RCX;
t2_424 := RAX;
RCX := PLUS_64(RCX, t2_424);
CF := bool2bv(LT_64(RCX, t1_423));
OF := AND_1((bool2bv((t1_423[64:63]) == (t2_424[64:63]))), (XOR_1((t1_423[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_423)), t2_424)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x9af:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RCX);

label_0x9b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x9bf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9c5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9ca:
t_431 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_134;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_431, 4bv64)), t_431)), 2bv64)), (XOR_64((RSHIFT_64(t_431, 4bv64)), t_431)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_431, 4bv64)), t_431)), 2bv64)), (XOR_64((RSHIFT_64(t_431, 4bv64)), t_431)))))[1:0]));
SF := t_431[64:63];
ZF := bool2bv(0bv64 == t_431);

label_0x9cd:
if (bv2bool(ZF)) {
  goto label_0x9d0;
}

label_0x9cf:
assume false;

label_0x9d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x9d8:
origDEST_435 := RAX;
origCOUNT_436 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), CF, LSHIFT_64(origDEST_435, (MINUS_64(64bv64, origCOUNT_436)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_436 == 1bv64)), origDEST_435[64:63], unconstrained_135));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), AF, unconstrained_136);

label_0x9dc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9e3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9e7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x9ef:
origDEST_441 := RCX;
origCOUNT_442 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), CF, LSHIFT_64(origDEST_441, (MINUS_64(64bv64, origCOUNT_442)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_442 == 1bv64)), origDEST_441[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), AF, unconstrained_138);

label_0x9f3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_139;
SF := unconstrained_140;
AF := unconstrained_141;
PF := unconstrained_142;

label_0x9f7:
if (bv2bool(CF)) {
  goto label_0x9fa;
}

label_0x9f9:
assume false;

label_0x9fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa02:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0xa05:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa07:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xa0b:
t_447 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_447[32:31]) == (1bv32[32:31]))), (XOR_1((t_447[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_447)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa0d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xa11:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xa19:
t1_451 := RAX;
t2_452 := 170bv64;
RAX := PLUS_64(RAX, t2_452);
CF := bool2bv(LT_64(RAX, t1_451));
OF := AND_1((bool2bv((t1_451[64:63]) == (t2_452[64:63]))), (XOR_1((t1_451[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_451)), t2_452)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa1f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RAX);

label_0xa27:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xa2b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xa30:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xa34:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0xa3c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa44:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_143;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xa4a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xa4f:
t_459 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_144;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_459, 4bv64)), t_459)), 2bv64)), (XOR_64((RSHIFT_64(t_459, 4bv64)), t_459)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_459, 4bv64)), t_459)), 2bv64)), (XOR_64((RSHIFT_64(t_459, 4bv64)), t_459)))))[1:0]));
SF := t_459[64:63];
ZF := bool2bv(0bv64 == t_459);

label_0xa52:
if (bv2bool(ZF)) {
  goto label_0xa55;
}

label_0xa54:
assume false;

label_0xa55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa5d:
origDEST_463 := RAX;
origCOUNT_464 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), CF, LSHIFT_64(origDEST_463, (MINUS_64(64bv64, origCOUNT_464)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_464 == 1bv64)), origDEST_463[64:63], unconstrained_145));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_464 == 0bv64)), AF, unconstrained_146);

label_0xa61:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa68:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa6c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa74:
origDEST_469 := RCX;
origCOUNT_470 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), CF, LSHIFT_64(origDEST_469, (MINUS_64(64bv64, origCOUNT_470)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_470 == 1bv64)), origDEST_469[64:63], unconstrained_147));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_470 == 0bv64)), AF, unconstrained_148);

label_0xa78:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_149;
SF := unconstrained_150;
AF := unconstrained_151;
PF := unconstrained_152;

label_0xa7c:
if (bv2bool(CF)) {
  goto label_0xa7f;
}

label_0xa7e:
assume false;

label_0xa7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xa87:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xa8f:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xa92:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xa95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xa9d:
t1_475 := RAX;
t2_476 := 168bv64;
RAX := PLUS_64(RAX, t2_476);
CF := bool2bv(LT_64(RAX, t1_475));
OF := AND_1((bool2bv((t1_475[64:63]) == (t2_476[64:63]))), (XOR_1((t1_475[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_475)), t2_476)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xaa3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 344bv64), RAX);

label_0xaab:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xaaf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xab4:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xab8:
t1_481 := RAX;
t2_482 := 2bv64;
RAX := PLUS_64(RAX, t2_482);
CF := bool2bv(LT_64(RAX, t1_481));
OF := AND_1((bool2bv((t1_481[64:63]) == (t2_482[64:63]))), (XOR_1((t1_481[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_481)), t2_482)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xabc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0xac4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xacc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_153;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xad2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xad7:
t_489 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_154;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))))[1:0]));
SF := t_489[64:63];
ZF := bool2bv(0bv64 == t_489);

label_0xada:
if (bv2bool(ZF)) {
  goto label_0xadd;
}

label_0xadc:
assume false;

label_0xadd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xae5:
origDEST_493 := RAX;
origCOUNT_494 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), CF, LSHIFT_64(origDEST_493, (MINUS_64(64bv64, origCOUNT_494)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_494 == 1bv64)), origDEST_493[64:63], unconstrained_155));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), AF, unconstrained_156);

label_0xae9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xaf0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xaf4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xafc:
origDEST_499 := RCX;
origCOUNT_500 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), CF, LSHIFT_64(origDEST_499, (MINUS_64(64bv64, origCOUNT_500)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_500 == 1bv64)), origDEST_499[64:63], unconstrained_157));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_500 == 0bv64)), AF, unconstrained_158);

label_0xb00:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_159;
SF := unconstrained_160;
AF := unconstrained_161;
PF := unconstrained_162;

label_0xb04:
if (bv2bool(CF)) {
  goto label_0xb07;
}

label_0xb06:
assume false;

label_0xb07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xb0f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xb17:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xb1a:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xb1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xb25:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0xb2b:
t_505 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_505)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_505, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_505, 4bv32)), t_505)), 2bv32)), (XOR_32((RSHIFT_32(t_505, 4bv32)), t_505)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_505, 4bv32)), t_505)), 2bv32)), (XOR_32((RSHIFT_32(t_505, 4bv32)), t_505)))))[1:0]));
SF := t_505[32:31];
ZF := bool2bv(0bv32 == t_505);

label_0xb2e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb9d;
}

label_0xb30:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xb38:
t1_509 := RAX;
t2_510 := 160bv64;
RAX := PLUS_64(RAX, t2_510);
CF := bool2bv(LT_64(RAX, t1_509));
OF := AND_1((bool2bv((t1_509[64:63]) == (t2_510[64:63]))), (XOR_1((t1_509[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_509)), t2_510)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb3e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0xb46:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xb4e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_163;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb54:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb59:
t_517 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_164;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_517, 4bv64)), t_517)), 2bv64)), (XOR_64((RSHIFT_64(t_517, 4bv64)), t_517)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_517, 4bv64)), t_517)), 2bv64)), (XOR_64((RSHIFT_64(t_517, 4bv64)), t_517)))))[1:0]));
SF := t_517[64:63];
ZF := bool2bv(0bv64 == t_517);

label_0xb5c:
if (bv2bool(ZF)) {
  goto label_0xb5f;
}

label_0xb5e:
assume false;

label_0xb5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xb67:
origDEST_521 := RAX;
origCOUNT_522 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), CF, LSHIFT_64(origDEST_521, (MINUS_64(64bv64, origCOUNT_522)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_522 == 1bv64)), origDEST_521[64:63], unconstrained_165));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), AF, unconstrained_166);

label_0xb6b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb72:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb76:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xb7e:
origDEST_527 := RCX;
origCOUNT_528 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), CF, LSHIFT_64(origDEST_527, (MINUS_64(64bv64, origCOUNT_528)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_528 == 1bv64)), origDEST_527[64:63], unconstrained_167));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_528 == 0bv64)), AF, unconstrained_168);

label_0xb82:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_169;
SF := unconstrained_170;
AF := unconstrained_171;
PF := unconstrained_172;

label_0xb86:
if (bv2bool(CF)) {
  goto label_0xb89;
}

label_0xb88:
assume false;

label_0xb89:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xb91:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0xb94:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xb98:
goto label_0x1509;

label_0xb9d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0xba1:
t_533 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_533[32:31]) == (1bv32[32:31]))), (XOR_1((t_533[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_533)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xba3:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0xba6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xbaa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xbaf:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0xbb3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xbbb:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0xbc2:
t_537 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_537)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_537, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)), 2bv32)), (XOR_32((RSHIFT_32(t_537, 4bv32)), t_537)))))[1:0]));
SF := t_537[32:31];
ZF := bool2bv(0bv32 == t_537);

label_0xbc4:
if (bv2bool(ZF)) {
  goto label_0xde8;
}

label_0xbca:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xbce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xbd6:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xbda:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0xbde:
t_541 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_173;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)), 2bv32)), (XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)), 2bv32)), (XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)))))[1:0]));
SF := t_541[32:31];
ZF := bool2bv(0bv32 == t_541);

label_0xbe0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xde8;
}

label_0xbe6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0xbeb:
origDEST_545 := RAX;
origCOUNT_546 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), CF, RSHIFT_64(origDEST_545, (MINUS_64(64bv64, origCOUNT_546)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_546 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_174));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), AF, unconstrained_175);

label_0xbef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xbf7:
t1_551 := RCX;
t2_552 := RAX;
RCX := PLUS_64(RCX, t2_552);
CF := bool2bv(LT_64(RCX, t1_551));
OF := AND_1((bool2bv((t1_551[64:63]) == (t2_552[64:63]))), (XOR_1((t1_551[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_551)), t2_552)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xbfa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RCX);

label_0xc02:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc0a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc10:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc15:
t_559 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)), 2bv64)), (XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)), 2bv64)), (XOR_64((RSHIFT_64(t_559, 4bv64)), t_559)))))[1:0]));
SF := t_559[64:63];
ZF := bool2bv(0bv64 == t_559);

label_0xc18:
if (bv2bool(ZF)) {
  goto label_0xc1b;
}

label_0xc1a:
assume false;

label_0xc1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc23:
origDEST_563 := RAX;
origCOUNT_564 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), CF, LSHIFT_64(origDEST_563, (MINUS_64(64bv64, origCOUNT_564)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_564 == 1bv64)), origDEST_563[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_564 == 0bv64)), AF, unconstrained_179);

label_0xc27:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc2e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc32:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc3a:
origDEST_569 := RCX;
origCOUNT_570 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), CF, LSHIFT_64(origDEST_569, (MINUS_64(64bv64, origCOUNT_570)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_570 == 1bv64)), origDEST_569[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), AF, unconstrained_181);

label_0xc3e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_182;
SF := unconstrained_183;
AF := unconstrained_184;
PF := unconstrained_185;

label_0xc42:
if (bv2bool(CF)) {
  goto label_0xc45;
}

label_0xc44:
assume false;

label_0xc45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc4d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0xc50:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc52:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xc56:
t_575 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_575[32:31]) == (1bv32[32:31]))), (XOR_1((t_575[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_575)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc58:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xc5c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xc64:
t1_579 := RAX;
t2_580 := 170bv64;
RAX := PLUS_64(RAX, t2_580);
CF := bool2bv(LT_64(RAX, t1_579));
OF := AND_1((bool2bv((t1_579[64:63]) == (t2_580[64:63]))), (XOR_1((t1_579[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_579)), t2_580)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc6a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RAX);

label_0xc72:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xc76:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xc7b:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xc7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0xc87:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xc8f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc95:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc9a:
t_587 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)), 2bv64)), (XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)), 2bv64)), (XOR_64((RSHIFT_64(t_587, 4bv64)), t_587)))))[1:0]));
SF := t_587[64:63];
ZF := bool2bv(0bv64 == t_587);

label_0xc9d:
if (bv2bool(ZF)) {
  goto label_0xca0;
}

label_0xc9f:
assume false;

label_0xca0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xca8:
origDEST_591 := RAX;
origCOUNT_592 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), CF, LSHIFT_64(origDEST_591, (MINUS_64(64bv64, origCOUNT_592)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_592 == 1bv64)), origDEST_591[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_592 == 0bv64)), AF, unconstrained_189);

label_0xcac:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcb3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcb7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xcbf:
origDEST_597 := RCX;
origCOUNT_598 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), CF, LSHIFT_64(origDEST_597, (MINUS_64(64bv64, origCOUNT_598)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_598 == 1bv64)), origDEST_597[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_598 == 0bv64)), AF, unconstrained_191);

label_0xcc3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_192;
SF := unconstrained_193;
AF := unconstrained_194;
PF := unconstrained_195;

label_0xcc7:
if (bv2bool(CF)) {
  goto label_0xcca;
}

label_0xcc9:
assume false;

label_0xcca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xcd2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0xcda:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xcdd:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xce0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xce8:
t1_603 := RAX;
t2_604 := 168bv64;
RAX := PLUS_64(RAX, t2_604);
CF := bool2bv(LT_64(RAX, t1_603));
OF := AND_1((bool2bv((t1_603[64:63]) == (t2_604[64:63]))), (XOR_1((t1_603[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_603)), t2_604)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcee:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0xcf6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xcfa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xcff:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xd03:
t1_609 := RAX;
t2_610 := 2bv64;
RAX := PLUS_64(RAX, t2_610);
CF := bool2bv(LT_64(RAX, t1_609));
OF := AND_1((bool2bv((t1_609[64:63]) == (t2_610[64:63]))), (XOR_1((t1_609[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_609)), t2_610)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd07:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0xd0f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xd17:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_196;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd1d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd22:
t_617 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_197;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)), 2bv64)), (XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)), 2bv64)), (XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)))))[1:0]));
SF := t_617[64:63];
ZF := bool2bv(0bv64 == t_617);

label_0xd25:
if (bv2bool(ZF)) {
  goto label_0xd28;
}

label_0xd27:
assume false;

label_0xd28:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xd30:
origDEST_621 := RAX;
origCOUNT_622 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), CF, LSHIFT_64(origDEST_621, (MINUS_64(64bv64, origCOUNT_622)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_622 == 1bv64)), origDEST_621[64:63], unconstrained_198));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_622 == 0bv64)), AF, unconstrained_199);

label_0xd34:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd3b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd3f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xd47:
origDEST_627 := RCX;
origCOUNT_628 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), CF, LSHIFT_64(origDEST_627, (MINUS_64(64bv64, origCOUNT_628)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_628 == 1bv64)), origDEST_627[64:63], unconstrained_200));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), AF, unconstrained_201);

label_0xd4b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_202;
SF := unconstrained_203;
AF := unconstrained_204;
PF := unconstrained_205;

label_0xd4f:
if (bv2bool(CF)) {
  goto label_0xd52;
}

label_0xd51:
assume false;

label_0xd52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xd5a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0xd62:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xd65:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xd68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd70:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0xd76:
t_633 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_633)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_633, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)), 2bv32)), (XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)), 2bv32)), (XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)))))[1:0]));
SF := t_633[32:31];
ZF := bool2bv(0bv32 == t_633);

label_0xd79:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xde8;
}

label_0xd7b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd83:
t1_637 := RAX;
t2_638 := 160bv64;
RAX := PLUS_64(RAX, t2_638);
CF := bool2bv(LT_64(RAX, t1_637));
OF := AND_1((bool2bv((t1_637[64:63]) == (t2_638[64:63]))), (XOR_1((t1_637[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_637)), t2_638)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd89:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0xd91:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xd99:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_206;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd9f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xda4:
t_645 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_645, 4bv64)), t_645)), 2bv64)), (XOR_64((RSHIFT_64(t_645, 4bv64)), t_645)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_645, 4bv64)), t_645)), 2bv64)), (XOR_64((RSHIFT_64(t_645, 4bv64)), t_645)))))[1:0]));
SF := t_645[64:63];
ZF := bool2bv(0bv64 == t_645);

label_0xda7:
if (bv2bool(ZF)) {
  goto label_0xdaa;
}

label_0xda9:
assume false;

label_0xdaa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xdb2:
origDEST_649 := RAX;
origCOUNT_650 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), CF, LSHIFT_64(origDEST_649, (MINUS_64(64bv64, origCOUNT_650)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_650 == 1bv64)), origDEST_649[64:63], unconstrained_208));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), AF, unconstrained_209);

label_0xdb6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xdbd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xdc1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xdc9:
origDEST_655 := RCX;
origCOUNT_656 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), CF, LSHIFT_64(origDEST_655, (MINUS_64(64bv64, origCOUNT_656)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_656 == 1bv64)), origDEST_655[64:63], unconstrained_210));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), AF, unconstrained_211);

label_0xdcd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_212;
SF := unconstrained_213;
AF := unconstrained_214;
PF := unconstrained_215;

label_0xdd1:
if (bv2bool(CF)) {
  goto label_0xdd4;
}

label_0xdd3:
assume false;

label_0xdd4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xddc:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0xddf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xde3:
goto label_0x1509;

label_0xde8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0xdec:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0xdf0:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[32:0]);

label_0xdf4:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0xdf7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xdfb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xe00:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0xe04:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xe0c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0xe13:
t_661 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_661)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_661, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_661, 4bv32)), t_661)), 2bv32)), (XOR_32((RSHIFT_32(t_661, 4bv32)), t_661)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_661, 4bv32)), t_661)), 2bv32)), (XOR_32((RSHIFT_32(t_661, 4bv32)), t_661)))))[1:0]));
SF := t_661[32:31];
ZF := bool2bv(0bv32 == t_661);

label_0xe15:
if (bv2bool(ZF)) {
  goto label_0x1039;
}

label_0xe1b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xe1f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xe27:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xe2b:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0xe2f:
t_665 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_216;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_665, 4bv32)), t_665)), 2bv32)), (XOR_32((RSHIFT_32(t_665, 4bv32)), t_665)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_665, 4bv32)), t_665)), 2bv32)), (XOR_32((RSHIFT_32(t_665, 4bv32)), t_665)))))[1:0]));
SF := t_665[32:31];
ZF := bool2bv(0bv32 == t_665);

label_0xe31:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1039;
}

label_0xe37:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0xe3c:
origDEST_669 := RAX;
origCOUNT_670 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), CF, RSHIFT_64(origDEST_669, (MINUS_64(64bv64, origCOUNT_670)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_670 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_217));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), AF, unconstrained_218);

label_0xe40:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xe48:
t1_675 := RCX;
t2_676 := RAX;
RCX := PLUS_64(RCX, t2_676);
CF := bool2bv(LT_64(RCX, t1_675));
OF := AND_1((bool2bv((t1_675[64:63]) == (t2_676[64:63]))), (XOR_1((t1_675[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_675)), t2_676)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe4b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RCX);

label_0xe53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xe5b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_219;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe61:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xe66:
t_683 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_220;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)), 2bv64)), (XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)), 2bv64)), (XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)))))[1:0]));
SF := t_683[64:63];
ZF := bool2bv(0bv64 == t_683);

label_0xe69:
if (bv2bool(ZF)) {
  goto label_0xe6c;
}

label_0xe6b:
assume false;

label_0xe6c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xe74:
origDEST_687 := RAX;
origCOUNT_688 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), CF, LSHIFT_64(origDEST_687, (MINUS_64(64bv64, origCOUNT_688)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_688 == 1bv64)), origDEST_687[64:63], unconstrained_221));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), AF, unconstrained_222);

label_0xe78:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xe7f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xe83:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xe8b:
origDEST_693 := RCX;
origCOUNT_694 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), CF, LSHIFT_64(origDEST_693, (MINUS_64(64bv64, origCOUNT_694)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_694 == 1bv64)), origDEST_693[64:63], unconstrained_223));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), AF, unconstrained_224);

label_0xe8f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_225;
SF := unconstrained_226;
AF := unconstrained_227;
PF := unconstrained_228;

label_0xe93:
if (bv2bool(CF)) {
  goto label_0xe96;
}

label_0xe95:
assume false;

label_0xe96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xe9e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0xea1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xea3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xea7:
t_699 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_699[32:31]) == (1bv32[32:31]))), (XOR_1((t_699[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_699)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xea9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xead:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xeb5:
t1_703 := RAX;
t2_704 := 170bv64;
RAX := PLUS_64(RAX, t2_704);
CF := bool2bv(LT_64(RAX, t1_703));
OF := AND_1((bool2bv((t1_703[64:63]) == (t2_704[64:63]))), (XOR_1((t1_703[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_703)), t2_704)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xebb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RAX);

label_0xec3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xec7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xecc:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xed0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0xed8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xee0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_229;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xee6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xeeb:
t_711 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_230;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)), 2bv64)), (XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)), 2bv64)), (XOR_64((RSHIFT_64(t_711, 4bv64)), t_711)))))[1:0]));
SF := t_711[64:63];
ZF := bool2bv(0bv64 == t_711);

label_0xeee:
if (bv2bool(ZF)) {
  goto label_0xef1;
}

label_0xef0:
assume false;

label_0xef1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xef9:
origDEST_715 := RAX;
origCOUNT_716 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), CF, LSHIFT_64(origDEST_715, (MINUS_64(64bv64, origCOUNT_716)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_716 == 1bv64)), origDEST_715[64:63], unconstrained_231));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_716 == 0bv64)), AF, unconstrained_232);

label_0xefd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf04:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf08:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xf10:
origDEST_721 := RCX;
origCOUNT_722 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), CF, LSHIFT_64(origDEST_721, (MINUS_64(64bv64, origCOUNT_722)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_722 == 1bv64)), origDEST_721[64:63], unconstrained_233));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_722 == 0bv64)), AF, unconstrained_234);

label_0xf14:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_235;
SF := unconstrained_236;
AF := unconstrained_237;
PF := unconstrained_238;

label_0xf18:
if (bv2bool(CF)) {
  goto label_0xf1b;
}

label_0xf1a:
assume false;

label_0xf1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xf23:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xf2b:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xf2e:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xf31:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xf39:
t1_727 := RAX;
t2_728 := 168bv64;
RAX := PLUS_64(RAX, t2_728);
CF := bool2bv(LT_64(RAX, t1_727));
OF := AND_1((bool2bv((t1_727[64:63]) == (t2_728[64:63]))), (XOR_1((t1_727[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_727)), t2_728)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf3f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 376bv64), RAX);

label_0xf47:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0xf4b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0xf50:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0xf54:
t1_733 := RAX;
t2_734 := 2bv64;
RAX := PLUS_64(RAX, t2_734);
CF := bool2bv(LT_64(RAX, t1_733));
OF := AND_1((bool2bv((t1_733[64:63]) == (t2_734[64:63]))), (XOR_1((t1_733[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_733)), t2_734)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf58:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0xf60:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf68:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_239;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf6e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xf73:
t_741 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_240;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)), 2bv64)), (XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)), 2bv64)), (XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)))))[1:0]));
SF := t_741[64:63];
ZF := bool2bv(0bv64 == t_741);

label_0xf76:
if (bv2bool(ZF)) {
  goto label_0xf79;
}

label_0xf78:
assume false;

label_0xf79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf81:
origDEST_745 := RAX;
origCOUNT_746 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), CF, LSHIFT_64(origDEST_745, (MINUS_64(64bv64, origCOUNT_746)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_746 == 1bv64)), origDEST_745[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), AF, unconstrained_242);

label_0xf85:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf8c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf90:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xf98:
origDEST_751 := RCX;
origCOUNT_752 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), CF, LSHIFT_64(origDEST_751, (MINUS_64(64bv64, origCOUNT_752)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_752 == 1bv64)), origDEST_751[64:63], unconstrained_243));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), AF, unconstrained_244);

label_0xf9c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_245;
SF := unconstrained_246;
AF := unconstrained_247;
PF := unconstrained_248;

label_0xfa0:
if (bv2bool(CF)) {
  goto label_0xfa3;
}

label_0xfa2:
assume false;

label_0xfa3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xfab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xfb3:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0xfb6:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0xfb9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xfc1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0xfc7:
t_757 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_757)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_757, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_757, 4bv32)), t_757)), 2bv32)), (XOR_32((RSHIFT_32(t_757, 4bv32)), t_757)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_757, 4bv32)), t_757)), 2bv32)), (XOR_32((RSHIFT_32(t_757, 4bv32)), t_757)))))[1:0]));
SF := t_757[32:31];
ZF := bool2bv(0bv32 == t_757);

label_0xfca:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1039;
}

label_0xfcc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xfd4:
t1_761 := RAX;
t2_762 := 160bv64;
RAX := PLUS_64(RAX, t2_762);
CF := bool2bv(LT_64(RAX, t1_761));
OF := AND_1((bool2bv((t1_761[64:63]) == (t2_762[64:63]))), (XOR_1((t1_761[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_761)), t2_762)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfda:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0xfe2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xfea:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_249;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xff0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xff5:
t_769 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_250;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_769, 4bv64)), t_769)), 2bv64)), (XOR_64((RSHIFT_64(t_769, 4bv64)), t_769)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_769, 4bv64)), t_769)), 2bv64)), (XOR_64((RSHIFT_64(t_769, 4bv64)), t_769)))))[1:0]));
SF := t_769[64:63];
ZF := bool2bv(0bv64 == t_769);

label_0xff8:
if (bv2bool(ZF)) {
  goto label_0xffb;
}

label_0xffa:
assume false;

label_0xffb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x1003:
origDEST_773 := RAX;
origCOUNT_774 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), CF, LSHIFT_64(origDEST_773, (MINUS_64(64bv64, origCOUNT_774)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_774 == 1bv64)), origDEST_773[64:63], unconstrained_251));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_774 == 0bv64)), AF, unconstrained_252);

label_0x1007:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x100e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1012:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x101a:
origDEST_779 := RCX;
origCOUNT_780 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), CF, LSHIFT_64(origDEST_779, (MINUS_64(64bv64, origCOUNT_780)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_780 == 1bv64)), origDEST_779[64:63], unconstrained_253));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_780 == 0bv64)), AF, unconstrained_254);

label_0x101e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_255;
SF := unconstrained_256;
AF := unconstrained_257;
PF := unconstrained_258;

label_0x1022:
if (bv2bool(CF)) {
  goto label_0x1025;
}

label_0x1024:
assume false;

label_0x1025:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x102d:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x1030:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1034:
goto label_0x1509;

label_0x1039:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x103d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x1041:
t1_785 := RCX[32:0];
t2_786 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_786));
CF := bool2bv(LT_32((RCX[32:0]), t1_785));
OF := AND_1((bool2bv((t1_785[32:31]) == (t2_786[32:31]))), (XOR_1((t1_785[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_785)), t2_786)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1043:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1045:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1048:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x104c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1051:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x1055:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x105d:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x1064:
t_791 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_791)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_791, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_791, 4bv32)), t_791)), 2bv32)), (XOR_32((RSHIFT_32(t_791, 4bv32)), t_791)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_791, 4bv32)), t_791)), 2bv32)), (XOR_32((RSHIFT_32(t_791, 4bv32)), t_791)))))[1:0]));
SF := t_791[32:31];
ZF := bool2bv(0bv32 == t_791);

label_0x1066:
if (bv2bool(ZF)) {
  goto label_0x128a;
}

label_0x106c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1070:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1078:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x107c:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x1080:
t_795 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_259;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_795, 4bv32)), t_795)), 2bv32)), (XOR_32((RSHIFT_32(t_795, 4bv32)), t_795)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_795, 4bv32)), t_795)), 2bv32)), (XOR_32((RSHIFT_32(t_795, 4bv32)), t_795)))))[1:0]));
SF := t_795[32:31];
ZF := bool2bv(0bv32 == t_795);

label_0x1082:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x128a;
}

label_0x1088:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x108d:
origDEST_799 := RAX;
origCOUNT_800 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), CF, RSHIFT_64(origDEST_799, (MINUS_64(64bv64, origCOUNT_800)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_800 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_260));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_800 == 0bv64)), AF, unconstrained_261);

label_0x1091:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x1099:
t1_805 := RCX;
t2_806 := RAX;
RCX := PLUS_64(RCX, t2_806);
CF := bool2bv(LT_64(RCX, t1_805));
OF := AND_1((bool2bv((t1_805[64:63]) == (t2_806[64:63]))), (XOR_1((t1_805[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_805)), t2_806)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x109c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RCX);

label_0x10a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x10ac:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_262;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x10b2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x10b7:
t_813 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_263;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_813, 4bv64)), t_813)), 2bv64)), (XOR_64((RSHIFT_64(t_813, 4bv64)), t_813)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_813, 4bv64)), t_813)), 2bv64)), (XOR_64((RSHIFT_64(t_813, 4bv64)), t_813)))))[1:0]));
SF := t_813[64:63];
ZF := bool2bv(0bv64 == t_813);

label_0x10ba:
if (bv2bool(ZF)) {
  goto label_0x10bd;
}

label_0x10bc:
assume false;

label_0x10bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x10c5:
origDEST_817 := RAX;
origCOUNT_818 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), CF, LSHIFT_64(origDEST_817, (MINUS_64(64bv64, origCOUNT_818)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_818 == 1bv64)), origDEST_817[64:63], unconstrained_264));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_818 == 0bv64)), AF, unconstrained_265);

label_0x10c9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x10d0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x10d4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x10dc:
origDEST_823 := RCX;
origCOUNT_824 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), CF, LSHIFT_64(origDEST_823, (MINUS_64(64bv64, origCOUNT_824)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_824 == 1bv64)), origDEST_823[64:63], unconstrained_266));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), AF, unconstrained_267);

label_0x10e0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_268;
SF := unconstrained_269;
AF := unconstrained_270;
PF := unconstrained_271;

label_0x10e4:
if (bv2bool(CF)) {
  goto label_0x10e7;
}

label_0x10e6:
assume false;

label_0x10e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x10ef:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x10f2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x10f4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x10f8:
t_829 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_829[32:31]) == (1bv32[32:31]))), (XOR_1((t_829[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_829)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x10fa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x10fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1106:
t1_833 := RAX;
t2_834 := 170bv64;
RAX := PLUS_64(RAX, t2_834);
CF := bool2bv(LT_64(RAX, t1_833));
OF := AND_1((bool2bv((t1_833[64:63]) == (t2_834[64:63]))), (XOR_1((t1_833[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_833)), t2_834)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x110c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 384bv64), RAX);

label_0x1114:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1118:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x111d:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1121:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0x1129:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x1131:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_272;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1137:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x113c:
t_841 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_273;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_841, 4bv64)), t_841)), 2bv64)), (XOR_64((RSHIFT_64(t_841, 4bv64)), t_841)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_841, 4bv64)), t_841)), 2bv64)), (XOR_64((RSHIFT_64(t_841, 4bv64)), t_841)))))[1:0]));
SF := t_841[64:63];
ZF := bool2bv(0bv64 == t_841);

label_0x113f:
if (bv2bool(ZF)) {
  goto label_0x1142;
}

label_0x1141:
assume false;

label_0x1142:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x114a:
origDEST_845 := RAX;
origCOUNT_846 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), CF, LSHIFT_64(origDEST_845, (MINUS_64(64bv64, origCOUNT_846)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_846 == 1bv64)), origDEST_845[64:63], unconstrained_274));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_846 == 0bv64)), AF, unconstrained_275);

label_0x114e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1155:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1159:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x1161:
origDEST_851 := RCX;
origCOUNT_852 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), CF, LSHIFT_64(origDEST_851, (MINUS_64(64bv64, origCOUNT_852)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_852 == 1bv64)), origDEST_851[64:63], unconstrained_276));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_852 == 0bv64)), AF, unconstrained_277);

label_0x1165:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_278;
SF := unconstrained_279;
AF := unconstrained_280;
PF := unconstrained_281;

label_0x1169:
if (bv2bool(CF)) {
  goto label_0x116c;
}

label_0x116b:
assume false;

label_0x116c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x1174:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x117c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x117f:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1182:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x118a:
t1_857 := RAX;
t2_858 := 168bv64;
RAX := PLUS_64(RAX, t2_858);
CF := bool2bv(LT_64(RAX, t1_857));
OF := AND_1((bool2bv((t1_857[64:63]) == (t2_858[64:63]))), (XOR_1((t1_857[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_857)), t2_858)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1190:
mem := STORE_LE_64(mem, PLUS_64(RSP, 392bv64), RAX);

label_0x1198:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x119c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x11a1:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x11a5:
t1_863 := RAX;
t2_864 := 2bv64;
RAX := PLUS_64(RAX, t2_864);
CF := bool2bv(LT_64(RAX, t1_863));
OF := AND_1((bool2bv((t1_863[64:63]) == (t2_864[64:63]))), (XOR_1((t1_863[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_863)), t2_864)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11a9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0x11b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x11b9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_282;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x11bf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x11c4:
t_871 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_283;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_871, 4bv64)), t_871)), 2bv64)), (XOR_64((RSHIFT_64(t_871, 4bv64)), t_871)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_871, 4bv64)), t_871)), 2bv64)), (XOR_64((RSHIFT_64(t_871, 4bv64)), t_871)))))[1:0]));
SF := t_871[64:63];
ZF := bool2bv(0bv64 == t_871);

label_0x11c7:
if (bv2bool(ZF)) {
  goto label_0x11ca;
}

label_0x11c9:
assume false;

label_0x11ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x11d2:
origDEST_875 := RAX;
origCOUNT_876 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), CF, LSHIFT_64(origDEST_875, (MINUS_64(64bv64, origCOUNT_876)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_876 == 1bv64)), origDEST_875[64:63], unconstrained_284));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_876 == 0bv64)), AF, unconstrained_285);

label_0x11d6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11dd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11e1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x11e9:
origDEST_881 := RCX;
origCOUNT_882 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), CF, LSHIFT_64(origDEST_881, (MINUS_64(64bv64, origCOUNT_882)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_882 == 1bv64)), origDEST_881[64:63], unconstrained_286));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_882 == 0bv64)), AF, unconstrained_287);

label_0x11ed:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_288;
SF := unconstrained_289;
AF := unconstrained_290;
PF := unconstrained_291;

label_0x11f1:
if (bv2bool(CF)) {
  goto label_0x11f4;
}

label_0x11f3:
assume false;

label_0x11f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x11fc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x1204:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1207:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x120a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1212:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x1218:
t_887 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_887)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_887, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_887, 4bv32)), t_887)), 2bv32)), (XOR_32((RSHIFT_32(t_887, 4bv32)), t_887)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_887, 4bv32)), t_887)), 2bv32)), (XOR_32((RSHIFT_32(t_887, 4bv32)), t_887)))))[1:0]));
SF := t_887[32:31];
ZF := bool2bv(0bv32 == t_887);

label_0x121b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x128a;
}

label_0x121d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1225:
t1_891 := RAX;
t2_892 := 160bv64;
RAX := PLUS_64(RAX, t2_892);
CF := bool2bv(LT_64(RAX, t1_891));
OF := AND_1((bool2bv((t1_891[64:63]) == (t2_892[64:63]))), (XOR_1((t1_891[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_891)), t2_892)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x122b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x1233:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x123b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_292;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1241:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1246:
t_899 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_293;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_899, 4bv64)), t_899)), 2bv64)), (XOR_64((RSHIFT_64(t_899, 4bv64)), t_899)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_899, 4bv64)), t_899)), 2bv64)), (XOR_64((RSHIFT_64(t_899, 4bv64)), t_899)))))[1:0]));
SF := t_899[64:63];
ZF := bool2bv(0bv64 == t_899);

label_0x1249:
if (bv2bool(ZF)) {
  goto label_0x124c;
}

label_0x124b:
assume false;

label_0x124c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x1254:
origDEST_903 := RAX;
origCOUNT_904 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), CF, LSHIFT_64(origDEST_903, (MINUS_64(64bv64, origCOUNT_904)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_904 == 1bv64)), origDEST_903[64:63], unconstrained_294));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_904 == 0bv64)), AF, unconstrained_295);

label_0x1258:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x125f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1263:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x126b:
origDEST_909 := RCX;
origCOUNT_910 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), CF, LSHIFT_64(origDEST_909, (MINUS_64(64bv64, origCOUNT_910)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_910 == 1bv64)), origDEST_909[64:63], unconstrained_296));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_910 == 0bv64)), AF, unconstrained_297);

label_0x126f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_298;
SF := unconstrained_299;
AF := unconstrained_300;
PF := unconstrained_301;

label_0x1273:
if (bv2bool(CF)) {
  goto label_0x1276;
}

label_0x1275:
assume false;

label_0x1276:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x127e:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x1281:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1285:
goto label_0x1509;

label_0x128a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x128e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x1292:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 1bv64)[32:0]);

label_0x1296:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1299:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x129d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x12a2:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x12a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x12ae:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x12b5:
t_915 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_915)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_915, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_915, 4bv32)), t_915)), 2bv32)), (XOR_32((RSHIFT_32(t_915, 4bv32)), t_915)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_915, 4bv32)), t_915)), 2bv32)), (XOR_32((RSHIFT_32(t_915, 4bv32)), t_915)))))[1:0]));
SF := t_915[32:31];
ZF := bool2bv(0bv32 == t_915);

label_0x12b7:
if (bv2bool(ZF)) {
  goto label_0x14d8;
}

label_0x12bd:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x12c1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x12c9:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x12cd:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x12d1:
t_919 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_302;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)), 2bv32)), (XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)), 2bv32)), (XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)))))[1:0]));
SF := t_919[32:31];
ZF := bool2bv(0bv32 == t_919);

label_0x12d3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14d8;
}

label_0x12d9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x12de:
origDEST_923 := RAX;
origCOUNT_924 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), CF, RSHIFT_64(origDEST_923, (MINUS_64(64bv64, origCOUNT_924)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_924 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_303));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), AF, unconstrained_304);

label_0x12e2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x12ea:
t1_929 := RCX;
t2_930 := RAX;
RCX := PLUS_64(RCX, t2_930);
CF := bool2bv(LT_64(RCX, t1_929));
OF := AND_1((bool2bv((t1_929[64:63]) == (t2_930[64:63]))), (XOR_1((t1_929[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_929)), t2_930)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x12ed:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RCX);

label_0x12f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x12fd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_305;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1303:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1308:
t_937 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_306;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_937, 4bv64)), t_937)), 2bv64)), (XOR_64((RSHIFT_64(t_937, 4bv64)), t_937)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_937, 4bv64)), t_937)), 2bv64)), (XOR_64((RSHIFT_64(t_937, 4bv64)), t_937)))))[1:0]));
SF := t_937[64:63];
ZF := bool2bv(0bv64 == t_937);

label_0x130b:
if (bv2bool(ZF)) {
  goto label_0x130e;
}

label_0x130d:
assume false;

label_0x130e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x1316:
origDEST_941 := RAX;
origCOUNT_942 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), CF, LSHIFT_64(origDEST_941, (MINUS_64(64bv64, origCOUNT_942)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_942 == 1bv64)), origDEST_941[64:63], unconstrained_307));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_942 == 0bv64)), AF, unconstrained_308);

label_0x131a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1321:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1325:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x132d:
origDEST_947 := RCX;
origCOUNT_948 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), CF, LSHIFT_64(origDEST_947, (MINUS_64(64bv64, origCOUNT_948)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_948 == 1bv64)), origDEST_947[64:63], unconstrained_309));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), AF, unconstrained_310);

label_0x1331:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_311;
SF := unconstrained_312;
AF := unconstrained_313;
PF := unconstrained_314;

label_0x1335:
if (bv2bool(CF)) {
  goto label_0x1338;
}

label_0x1337:
assume false;

label_0x1338:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x1340:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1343:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1345:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1349:
t_953 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_953[32:31]) == (1bv32[32:31]))), (XOR_1((t_953[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_953)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x134b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x134f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1357:
t1_957 := RAX;
t2_958 := 170bv64;
RAX := PLUS_64(RAX, t2_958);
CF := bool2bv(LT_64(RAX, t1_957));
OF := AND_1((bool2bv((t1_957[64:63]) == (t2_958[64:63]))), (XOR_1((t1_957[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_957)), t2_958)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x135d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 400bv64), RAX);

label_0x1365:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1369:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x136e:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1372:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0x137a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x1382:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_315;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1388:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x138d:
t_965 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_316;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_965, 4bv64)), t_965)), 2bv64)), (XOR_64((RSHIFT_64(t_965, 4bv64)), t_965)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_965, 4bv64)), t_965)), 2bv64)), (XOR_64((RSHIFT_64(t_965, 4bv64)), t_965)))))[1:0]));
SF := t_965[64:63];
ZF := bool2bv(0bv64 == t_965);

label_0x1390:
if (bv2bool(ZF)) {
  goto label_0x1393;
}

label_0x1392:
assume false;

label_0x1393:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x139b:
origDEST_969 := RAX;
origCOUNT_970 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), CF, LSHIFT_64(origDEST_969, (MINUS_64(64bv64, origCOUNT_970)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_970 == 1bv64)), origDEST_969[64:63], unconstrained_317));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_970 == 0bv64)), AF, unconstrained_318);

label_0x139f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x13a6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x13aa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x13b2:
origDEST_975 := RCX;
origCOUNT_976 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), CF, LSHIFT_64(origDEST_975, (MINUS_64(64bv64, origCOUNT_976)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_976 == 1bv64)), origDEST_975[64:63], unconstrained_319));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), AF, unconstrained_320);

label_0x13b6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_321;
SF := unconstrained_322;
AF := unconstrained_323;
PF := unconstrained_324;

label_0x13ba:
if (bv2bool(CF)) {
  goto label_0x13bd;
}

label_0x13bc:
assume false;

label_0x13bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x13c5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x13cd:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x13d0:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x13d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x13db:
t1_981 := RAX;
t2_982 := 168bv64;
RAX := PLUS_64(RAX, t2_982);
CF := bool2bv(LT_64(RAX, t1_981));
OF := AND_1((bool2bv((t1_981[64:63]) == (t2_982[64:63]))), (XOR_1((t1_981[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_981)), t2_982)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13e1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 408bv64), RAX);

label_0x13e9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x13ed:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x13f2:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x13f6:
t1_987 := RAX;
t2_988 := 2bv64;
RAX := PLUS_64(RAX, t2_988);
CF := bool2bv(LT_64(RAX, t1_987));
OF := AND_1((bool2bv((t1_987[64:63]) == (t2_988[64:63]))), (XOR_1((t1_987[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_987)), t2_988)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0x1402:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x140a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_325;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1410:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1415:
t_995 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_326;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)), 2bv64)), (XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)), 2bv64)), (XOR_64((RSHIFT_64(t_995, 4bv64)), t_995)))))[1:0]));
SF := t_995[64:63];
ZF := bool2bv(0bv64 == t_995);

label_0x1418:
if (bv2bool(ZF)) {
  goto label_0x141b;
}

label_0x141a:
assume false;

label_0x141b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1423:
origDEST_999 := RAX;
origCOUNT_1000 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), CF, LSHIFT_64(origDEST_999, (MINUS_64(64bv64, origCOUNT_1000)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 1bv64)), origDEST_999[64:63], unconstrained_327));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1000 == 0bv64)), AF, unconstrained_328);

label_0x1427:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x142e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1432:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x143a:
origDEST_1005 := RCX;
origCOUNT_1006 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), CF, LSHIFT_64(origDEST_1005, (MINUS_64(64bv64, origCOUNT_1006)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 1bv64)), origDEST_1005[64:63], unconstrained_329));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1006 == 0bv64)), AF, unconstrained_330);

label_0x143e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_331;
SF := unconstrained_332;
AF := unconstrained_333;
PF := unconstrained_334;

label_0x1442:
if (bv2bool(CF)) {
  goto label_0x1445;
}

label_0x1444:
assume false;

label_0x1445:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x144d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x1455:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1458:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x145b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1463:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x1469:
t_1011 := MINUS_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, RSP)), t_1011)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1011, (LOAD_LE_32(mem, RSP)))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)), 2bv32)), (XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)), 2bv32)), (XOR_32((RSHIFT_32(t_1011, 4bv32)), t_1011)))))[1:0]));
SF := t_1011[32:31];
ZF := bool2bv(0bv32 == t_1011);

label_0x146c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14d8;
}

label_0x146e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x1476:
t1_1015 := RAX;
t2_1016 := 160bv64;
RAX := PLUS_64(RAX, t2_1016);
CF := bool2bv(LT_64(RAX, t1_1015));
OF := AND_1((bool2bv((t1_1015[64:63]) == (t2_1016[64:63]))), (XOR_1((t1_1015[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1015)), t2_1016)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x147c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RAX);

label_0x1484:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x148c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_335;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1492:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1497:
t_1023 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_336;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)), 2bv64)), (XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)), 2bv64)), (XOR_64((RSHIFT_64(t_1023, 4bv64)), t_1023)))))[1:0]));
SF := t_1023[64:63];
ZF := bool2bv(0bv64 == t_1023);

label_0x149a:
if (bv2bool(ZF)) {
  goto label_0x149d;
}

label_0x149c:
assume false;

label_0x149d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x14a5:
origDEST_1027 := RAX;
origCOUNT_1028 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), CF, LSHIFT_64(origDEST_1027, (MINUS_64(64bv64, origCOUNT_1028)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 1bv64)), origDEST_1027[64:63], unconstrained_337));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1028 == 0bv64)), AF, unconstrained_338);

label_0x14a9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x14b0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x14b4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x14bc:
origDEST_1033 := RCX;
origCOUNT_1034 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), CF, LSHIFT_64(origDEST_1033, (MINUS_64(64bv64, origCOUNT_1034)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 1bv64)), origDEST_1033[64:63], unconstrained_339));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1034 == 0bv64)), AF, unconstrained_340);

label_0x14c0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_341;
SF := unconstrained_342;
AF := unconstrained_343;
PF := unconstrained_344;

label_0x14c4:
if (bv2bool(CF)) {
  goto label_0x14c7;
}

label_0x14c6:
assume false;

label_0x14c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x14cf:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x14d2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x14d6:
goto label_0x1509;

label_0x14d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x14e0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 152bv64)));

label_0x14e6:
t_1039 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_1039)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1039, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1039, 4bv32)), t_1039)), 2bv32)), (XOR_32((RSHIFT_32(t_1039, 4bv32)), t_1039)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1039, 4bv32)), t_1039)), 2bv32)), (XOR_32((RSHIFT_32(t_1039, 4bv32)), t_1039)))))[1:0]));
SF := t_1039[32:31];
ZF := bool2bv(0bv32 == t_1039);

label_0x14ea:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1500;
}

label_0x14ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x14f4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 152bv64)));

label_0x14fa:
t_1043 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1043, 1bv32)), (XOR_32(t_1043, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1043)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x14fc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x1500:
goto label_0x2e0;

label_0x1505:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1509:
t1_1047 := RSP;
t2_1048 := 424bv64;
RSP := PLUS_64(RSP, t2_1048);
CF := bool2bv(LT_64(RSP, t1_1047));
OF := AND_1((bool2bv((t1_1047[64:63]) == (t2_1048[64:63]))), (XOR_1((t1_1047[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_1047)), t2_1048)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1510:

ra_1053 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_1000,origCOUNT_1006,origCOUNT_1028,origCOUNT_1034,origCOUNT_106,origCOUNT_112,origCOUNT_134,origCOUNT_140,origCOUNT_158,origCOUNT_176,origCOUNT_182,origCOUNT_204,origCOUNT_210,origCOUNT_234,origCOUNT_240,origCOUNT_262,origCOUNT_268,origCOUNT_290,origCOUNT_30,origCOUNT_308,origCOUNT_314,origCOUNT_336,origCOUNT_342,origCOUNT_366,origCOUNT_372,origCOUNT_394,origCOUNT_400,origCOUNT_418,origCOUNT_436,origCOUNT_442,origCOUNT_464,origCOUNT_470,origCOUNT_48,origCOUNT_494,origCOUNT_500,origCOUNT_522,origCOUNT_528,origCOUNT_54,origCOUNT_546,origCOUNT_564,origCOUNT_570,origCOUNT_592,origCOUNT_598,origCOUNT_622,origCOUNT_628,origCOUNT_650,origCOUNT_656,origCOUNT_670,origCOUNT_688,origCOUNT_694,origCOUNT_716,origCOUNT_722,origCOUNT_746,origCOUNT_752,origCOUNT_76,origCOUNT_774,origCOUNT_780,origCOUNT_800,origCOUNT_818,origCOUNT_82,origCOUNT_824,origCOUNT_846,origCOUNT_852,origCOUNT_876,origCOUNT_882,origCOUNT_904,origCOUNT_910,origCOUNT_924,origCOUNT_942,origCOUNT_948,origCOUNT_970,origCOUNT_976,origDEST_1005,origDEST_1027,origDEST_1033,origDEST_105,origDEST_111,origDEST_133,origDEST_139,origDEST_157,origDEST_175,origDEST_181,origDEST_203,origDEST_209,origDEST_233,origDEST_239,origDEST_261,origDEST_267,origDEST_289,origDEST_29,origDEST_307,origDEST_313,origDEST_335,origDEST_341,origDEST_365,origDEST_371,origDEST_393,origDEST_399,origDEST_417,origDEST_435,origDEST_441,origDEST_463,origDEST_469,origDEST_47,origDEST_493,origDEST_499,origDEST_521,origDEST_527,origDEST_53,origDEST_545,origDEST_563,origDEST_569,origDEST_591,origDEST_597,origDEST_621,origDEST_627,origDEST_649,origDEST_655,origDEST_669,origDEST_687,origDEST_693,origDEST_715,origDEST_721,origDEST_745,origDEST_75,origDEST_751,origDEST_773,origDEST_779,origDEST_799,origDEST_81,origDEST_817,origDEST_823,origDEST_845,origDEST_851,origDEST_875,origDEST_881,origDEST_903,origDEST_909,origDEST_923,origDEST_941,origDEST_947,origDEST_969,origDEST_975,origDEST_999,ra_1053,t1_1015,t1_1047,t1_121,t1_163,t1_191,t1_215,t1_221,t1_249,t1_295,t1_323,t1_347,t1_35,t1_353,t1_381,t1_423,t1_451,t1_475,t1_481,t1_509,t1_551,t1_579,t1_603,t1_609,t1_63,t1_637,t1_675,t1_703,t1_727,t1_733,t1_761,t1_785,t1_805,t1_833,t1_857,t1_863,t1_87,t1_891,t1_929,t1_93,t1_957,t1_981,t1_987,t2_1016,t2_1048,t2_122,t2_164,t2_192,t2_216,t2_222,t2_250,t2_296,t2_324,t2_348,t2_354,t2_36,t2_382,t2_424,t2_452,t2_476,t2_482,t2_510,t2_552,t2_580,t2_604,t2_610,t2_638,t2_64,t2_676,t2_704,t2_728,t2_734,t2_762,t2_786,t2_806,t2_834,t2_858,t2_864,t2_88,t2_892,t2_930,t2_94,t2_958,t2_982,t2_988,t_1,t_101,t_1011,t_1023,t_1039,t_1043,t_117,t_129,t_13,t_145,t_149,t_153,t_17,t_171,t_187,t_199,t_21,t_229,t_245,t_25,t_257,t_273,t_277,t_281,t_285,t_303,t_319,t_331,t_361,t_377,t_389,t_405,t_409,t_413,t_43,t_431,t_447,t_459,t_489,t_5,t_505,t_517,t_533,t_537,t_541,t_559,t_575,t_587,t_59,t_617,t_633,t_645,t_661,t_665,t_683,t_699,t_71,t_711,t_741,t_757,t_769,t_791,t_795,t_813,t_829,t_841,t_871,t_887,t_899,t_9,t_915,t_919,t_937,t_953,t_965,t_995;

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
const unconstrained_257: bv1;
const unconstrained_258: bv1;
const unconstrained_259: bv1;
const unconstrained_26: bv1;
const unconstrained_260: bv1;
const unconstrained_261: bv1;
const unconstrained_262: bv1;
const unconstrained_263: bv1;
const unconstrained_264: bv1;
const unconstrained_265: bv1;
const unconstrained_266: bv1;
const unconstrained_267: bv1;
const unconstrained_268: bv1;
const unconstrained_269: bv1;
const unconstrained_27: bv1;
const unconstrained_270: bv1;
const unconstrained_271: bv1;
const unconstrained_272: bv1;
const unconstrained_273: bv1;
const unconstrained_274: bv1;
const unconstrained_275: bv1;
const unconstrained_276: bv1;
const unconstrained_277: bv1;
const unconstrained_278: bv1;
const unconstrained_279: bv1;
const unconstrained_28: bv1;
const unconstrained_280: bv1;
const unconstrained_281: bv1;
const unconstrained_282: bv1;
const unconstrained_283: bv1;
const unconstrained_284: bv1;
const unconstrained_285: bv1;
const unconstrained_286: bv1;
const unconstrained_287: bv1;
const unconstrained_288: bv1;
const unconstrained_289: bv1;
const unconstrained_29: bv1;
const unconstrained_290: bv1;
const unconstrained_291: bv1;
const unconstrained_292: bv1;
const unconstrained_293: bv1;
const unconstrained_294: bv1;
const unconstrained_295: bv1;
const unconstrained_296: bv1;
const unconstrained_297: bv1;
const unconstrained_298: bv1;
const unconstrained_299: bv1;
const unconstrained_3: bv1;
const unconstrained_30: bv1;
const unconstrained_300: bv1;
const unconstrained_301: bv1;
const unconstrained_302: bv1;
const unconstrained_303: bv1;
const unconstrained_304: bv1;
const unconstrained_305: bv1;
const unconstrained_306: bv1;
const unconstrained_307: bv1;
const unconstrained_308: bv1;
const unconstrained_309: bv1;
const unconstrained_31: bv1;
const unconstrained_310: bv1;
const unconstrained_311: bv1;
const unconstrained_312: bv1;
const unconstrained_313: bv1;
const unconstrained_314: bv1;
const unconstrained_315: bv1;
const unconstrained_316: bv1;
const unconstrained_317: bv1;
const unconstrained_318: bv1;
const unconstrained_319: bv1;
const unconstrained_32: bv1;
const unconstrained_320: bv1;
const unconstrained_321: bv1;
const unconstrained_322: bv1;
const unconstrained_323: bv1;
const unconstrained_324: bv1;
const unconstrained_325: bv1;
const unconstrained_326: bv1;
const unconstrained_327: bv1;
const unconstrained_328: bv1;
const unconstrained_329: bv1;
const unconstrained_33: bv1;
const unconstrained_330: bv1;
const unconstrained_331: bv1;
const unconstrained_332: bv1;
const unconstrained_333: bv1;
const unconstrained_334: bv1;
const unconstrained_335: bv1;
const unconstrained_336: bv1;
const unconstrained_337: bv1;
const unconstrained_338: bv1;
const unconstrained_339: bv1;
const unconstrained_34: bv1;
const unconstrained_340: bv1;
const unconstrained_341: bv1;
const unconstrained_342: bv1;
const unconstrained_343: bv1;
const unconstrained_344: bv1;
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
var origCOUNT_1000: bv64;
var origCOUNT_1006: bv64;
var origCOUNT_1028: bv64;
var origCOUNT_1034: bv64;
var origCOUNT_106: bv64;
var origCOUNT_112: bv64;
var origCOUNT_134: bv64;
var origCOUNT_140: bv64;
var origCOUNT_158: bv64;
var origCOUNT_176: bv64;
var origCOUNT_182: bv64;
var origCOUNT_204: bv64;
var origCOUNT_210: bv64;
var origCOUNT_234: bv64;
var origCOUNT_240: bv64;
var origCOUNT_262: bv64;
var origCOUNT_268: bv64;
var origCOUNT_290: bv64;
var origCOUNT_30: bv64;
var origCOUNT_308: bv64;
var origCOUNT_314: bv64;
var origCOUNT_336: bv64;
var origCOUNT_342: bv64;
var origCOUNT_366: bv64;
var origCOUNT_372: bv64;
var origCOUNT_394: bv64;
var origCOUNT_400: bv64;
var origCOUNT_418: bv64;
var origCOUNT_436: bv64;
var origCOUNT_442: bv64;
var origCOUNT_464: bv64;
var origCOUNT_470: bv64;
var origCOUNT_48: bv64;
var origCOUNT_494: bv64;
var origCOUNT_500: bv64;
var origCOUNT_522: bv64;
var origCOUNT_528: bv64;
var origCOUNT_54: bv64;
var origCOUNT_546: bv64;
var origCOUNT_564: bv64;
var origCOUNT_570: bv64;
var origCOUNT_592: bv64;
var origCOUNT_598: bv64;
var origCOUNT_622: bv64;
var origCOUNT_628: bv64;
var origCOUNT_650: bv64;
var origCOUNT_656: bv64;
var origCOUNT_670: bv64;
var origCOUNT_688: bv64;
var origCOUNT_694: bv64;
var origCOUNT_716: bv64;
var origCOUNT_722: bv64;
var origCOUNT_746: bv64;
var origCOUNT_752: bv64;
var origCOUNT_76: bv64;
var origCOUNT_774: bv64;
var origCOUNT_780: bv64;
var origCOUNT_800: bv64;
var origCOUNT_818: bv64;
var origCOUNT_82: bv64;
var origCOUNT_824: bv64;
var origCOUNT_846: bv64;
var origCOUNT_852: bv64;
var origCOUNT_876: bv64;
var origCOUNT_882: bv64;
var origCOUNT_904: bv64;
var origCOUNT_910: bv64;
var origCOUNT_924: bv64;
var origCOUNT_942: bv64;
var origCOUNT_948: bv64;
var origCOUNT_970: bv64;
var origCOUNT_976: bv64;
var origDEST_1005: bv64;
var origDEST_1027: bv64;
var origDEST_1033: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_157: bv64;
var origDEST_175: bv64;
var origDEST_181: bv64;
var origDEST_203: bv64;
var origDEST_209: bv64;
var origDEST_233: bv64;
var origDEST_239: bv64;
var origDEST_261: bv64;
var origDEST_267: bv64;
var origDEST_289: bv64;
var origDEST_29: bv64;
var origDEST_307: bv64;
var origDEST_313: bv64;
var origDEST_335: bv64;
var origDEST_341: bv64;
var origDEST_365: bv64;
var origDEST_371: bv64;
var origDEST_393: bv64;
var origDEST_399: bv64;
var origDEST_417: bv64;
var origDEST_435: bv64;
var origDEST_441: bv64;
var origDEST_463: bv64;
var origDEST_469: bv64;
var origDEST_47: bv64;
var origDEST_493: bv64;
var origDEST_499: bv64;
var origDEST_521: bv64;
var origDEST_527: bv64;
var origDEST_53: bv64;
var origDEST_545: bv64;
var origDEST_563: bv64;
var origDEST_569: bv64;
var origDEST_591: bv64;
var origDEST_597: bv64;
var origDEST_621: bv64;
var origDEST_627: bv64;
var origDEST_649: bv64;
var origDEST_655: bv64;
var origDEST_669: bv64;
var origDEST_687: bv64;
var origDEST_693: bv64;
var origDEST_715: bv64;
var origDEST_721: bv64;
var origDEST_745: bv64;
var origDEST_75: bv64;
var origDEST_751: bv64;
var origDEST_773: bv64;
var origDEST_779: bv64;
var origDEST_799: bv64;
var origDEST_81: bv64;
var origDEST_817: bv64;
var origDEST_823: bv64;
var origDEST_845: bv64;
var origDEST_851: bv64;
var origDEST_875: bv64;
var origDEST_881: bv64;
var origDEST_903: bv64;
var origDEST_909: bv64;
var origDEST_923: bv64;
var origDEST_941: bv64;
var origDEST_947: bv64;
var origDEST_969: bv64;
var origDEST_975: bv64;
var origDEST_999: bv64;
var ra_1053: bv64;
var t1_1015: bv64;
var t1_1047: bv64;
var t1_121: bv64;
var t1_163: bv64;
var t1_191: bv64;
var t1_215: bv64;
var t1_221: bv64;
var t1_249: bv64;
var t1_295: bv64;
var t1_323: bv64;
var t1_347: bv64;
var t1_35: bv64;
var t1_353: bv64;
var t1_381: bv64;
var t1_423: bv64;
var t1_451: bv64;
var t1_475: bv64;
var t1_481: bv64;
var t1_509: bv64;
var t1_551: bv64;
var t1_579: bv64;
var t1_603: bv64;
var t1_609: bv64;
var t1_63: bv64;
var t1_637: bv64;
var t1_675: bv64;
var t1_703: bv64;
var t1_727: bv64;
var t1_733: bv64;
var t1_761: bv64;
var t1_785: bv32;
var t1_805: bv64;
var t1_833: bv64;
var t1_857: bv64;
var t1_863: bv64;
var t1_87: bv64;
var t1_891: bv64;
var t1_929: bv64;
var t1_93: bv64;
var t1_957: bv64;
var t1_981: bv64;
var t1_987: bv64;
var t2_1016: bv64;
var t2_1048: bv64;
var t2_122: bv64;
var t2_164: bv64;
var t2_192: bv64;
var t2_216: bv64;
var t2_222: bv64;
var t2_250: bv64;
var t2_296: bv64;
var t2_324: bv64;
var t2_348: bv64;
var t2_354: bv64;
var t2_36: bv64;
var t2_382: bv64;
var t2_424: bv64;
var t2_452: bv64;
var t2_476: bv64;
var t2_482: bv64;
var t2_510: bv64;
var t2_552: bv64;
var t2_580: bv64;
var t2_604: bv64;
var t2_610: bv64;
var t2_638: bv64;
var t2_64: bv64;
var t2_676: bv64;
var t2_704: bv64;
var t2_728: bv64;
var t2_734: bv64;
var t2_762: bv64;
var t2_786: bv32;
var t2_806: bv64;
var t2_834: bv64;
var t2_858: bv64;
var t2_864: bv64;
var t2_88: bv64;
var t2_892: bv64;
var t2_930: bv64;
var t2_94: bv64;
var t2_958: bv64;
var t2_982: bv64;
var t2_988: bv64;
var t_1: bv64;
var t_101: bv64;
var t_1011: bv32;
var t_1023: bv64;
var t_1039: bv32;
var t_1043: bv32;
var t_117: bv32;
var t_129: bv64;
var t_13: bv32;
var t_145: bv32;
var t_149: bv32;
var t_153: bv32;
var t_17: bv32;
var t_171: bv64;
var t_187: bv32;
var t_199: bv64;
var t_21: bv32;
var t_229: bv64;
var t_245: bv32;
var t_25: bv32;
var t_257: bv64;
var t_273: bv32;
var t_277: bv32;
var t_281: bv32;
var t_285: bv32;
var t_303: bv64;
var t_319: bv32;
var t_331: bv64;
var t_361: bv64;
var t_377: bv32;
var t_389: bv64;
var t_405: bv32;
var t_409: bv32;
var t_413: bv32;
var t_43: bv64;
var t_431: bv64;
var t_447: bv32;
var t_459: bv64;
var t_489: bv64;
var t_5: bv32;
var t_505: bv32;
var t_517: bv64;
var t_533: bv32;
var t_537: bv32;
var t_541: bv32;
var t_559: bv64;
var t_575: bv32;
var t_587: bv64;
var t_59: bv32;
var t_617: bv64;
var t_633: bv32;
var t_645: bv64;
var t_661: bv32;
var t_665: bv32;
var t_683: bv64;
var t_699: bv32;
var t_71: bv64;
var t_711: bv64;
var t_741: bv64;
var t_757: bv32;
var t_769: bv64;
var t_791: bv32;
var t_795: bv32;
var t_813: bv64;
var t_829: bv32;
var t_841: bv64;
var t_871: bv64;
var t_887: bv32;
var t_899: bv64;
var t_9: bv32;
var t_915: bv32;
var t_919: bv32;
var t_937: bv64;
var t_953: bv32;
var t_965: bv64;
var t_995: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(96bv64);
axiom policy(656bv64);
axiom policy(5408bv64);
axiom policy(6768bv64);
axiom policy(12448bv64);
axiom policy(12592bv64);
axiom policy(14480bv64);
