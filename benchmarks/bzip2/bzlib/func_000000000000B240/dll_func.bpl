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
axiom _function_addr_low == 45632bv64;
axiom _function_addr_high == 57008bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xb240:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xb245:
t_1 := RSP;
RSP := MINUS_64(RSP, 984bv64);
CF := bool2bv(LT_64(t_1, 984bv64));
OF := AND_64((XOR_64(t_1, 984bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 984bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xb24c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb254:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 20bv64))));

label_0xb258:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0xb25a:
if (bv2bool(ZF)) {
  goto label_0xce0a;
}

label_0xb260:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_2;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb262:
t_9 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0xb265:
if (bv2bool(ZF)) {
  goto label_0xce05;
}

label_0xb26b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb26d:
t_13 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0xb270:
if (bv2bool(ZF)) {
  goto label_0xb674;
}

label_0xb276:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb27e:
RAX := LOAD_LE_64(mem, RAX);

label_0xb281:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0xb285:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb28e;
}

label_0xb287:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb289:
goto label_0xdea1;

label_0xb28e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb296:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0xb29a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb2a1;
}

label_0xb29c:
goto label_0xb674;

label_0xb2a1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb2a9:
t1_25 := RAX;
t2_26 := 12bv64;
RAX := PLUS_64(RAX, t2_26);
CF := bool2bv(LT_64(RAX, t1_25));
OF := AND_1((bool2bv((t1_25[64:63]) == (t2_26[64:63]))), (XOR_1((t1_25[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_25)), t2_26)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb2ad:
mem := STORE_LE_64(mem, PLUS_64(RSP, 888bv64), RAX);

label_0xb2b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb2bd:
RAX := LOAD_LE_64(mem, RAX);

label_0xb2c0:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0xb2c4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 544bv64), RAX);

label_0xb2cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0xb2d4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb2da:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb2df:
t_33 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0xb2e2:
if (bv2bool(ZF)) {
  goto label_0xb2e5;
}

label_0xb2e4:
assume false;

label_0xb2e5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0xb2ed:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_8);

label_0xb2f1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb2f8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb2fc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0xb304:
origDEST_43 := RCX;
origCOUNT_44 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_10);

label_0xb308:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_11;
SF := unconstrained_12;
AF := unconstrained_13;
PF := unconstrained_14;

label_0xb30c:
if (bv2bool(CF)) {
  goto label_0xb30f;
}

label_0xb30e:
assume false;

label_0xb30f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 544bv64));

label_0xb317:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 888bv64));

label_0xb31f:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0xb322:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xb324:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb32c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64)));

label_0xb332:
origDEST_49 := RAX[32:0];
origCOUNT_50 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), CF, RSHIFT_32(origDEST_49, (MINUS_32(32bv32, origCOUNT_50)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv32)), AF, unconstrained_16);

label_0xb335:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb33d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3184bv64)));

label_0xb343:
origDEST_55 := RCX[32:0];
origCOUNT_56 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), CF, LSHIFT_32(origDEST_55, (MINUS_32(32bv32, origCOUNT_56)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv32)), origDEST_55[32:31], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv32)), AF, unconstrained_18);

label_0xb346:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb34e:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, 12bv64))));

label_0xb352:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xb354:
RCX := (0bv32 ++ RCX[32:0]);

label_0xb356:
RDX := PLUS_64((PLUS_64(0bv64, 45917bv64)), 0bv64)[64:0];

label_0xb35d:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb360:
mem := STORE_LE_32(mem, PLUS_64(RSP, 640bv64), RAX[32:0]);

label_0xb367:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb36f:
t1_65 := RAX;
t2_66 := 3184bv64;
RAX := PLUS_64(RAX, t2_66);
CF := bool2bv(LT_64(RAX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb375:
mem := STORE_LE_64(mem, PLUS_64(RSP, 552bv64), RAX);

label_0xb37d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0xb385:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb38b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb390:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0xb393:
if (bv2bool(ZF)) {
  goto label_0xb396;
}

label_0xb395:
assume false;

label_0xb396:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0xb39e:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_24);

label_0xb3a2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb3a9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb3ad:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0xb3b5:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_26);

label_0xb3b9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0xb3bd:
if (bv2bool(CF)) {
  goto label_0xb3c0;
}

label_0xb3bf:
assume false;

label_0xb3c0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 552bv64));

label_0xb3c8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 640bv64)));

label_0xb3cf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb3d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb3d9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0xb3dc:
t_89 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_89, 1bv32)), (XOR_32(t_89, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_89)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb3de:
mem := STORE_LE_32(mem, PLUS_64(RSP, 644bv64), RAX[32:0]);

label_0xb3e5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb3ed:
t1_93 := RAX;
t2_94 := 16bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb3f1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 560bv64), RAX);

label_0xb3f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0xb401:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb407:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb40c:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0xb40f:
if (bv2bool(ZF)) {
  goto label_0xb412;
}

label_0xb411:
assume false;

label_0xb412:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0xb41a:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_34);

label_0xb41e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb425:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb429:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0xb431:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_36);

label_0xb435:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0xb439:
if (bv2bool(CF)) {
  goto label_0xb43c;
}

label_0xb43b:
assume false;

label_0xb43c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 560bv64));

label_0xb444:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 644bv64)));

label_0xb44b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb44d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb455:
RAX := LOAD_LE_64(mem, RAX);

label_0xb458:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0xb45c:
t_117 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_117[64:63]) == (1bv64[64:63]))), (XOR_1((t_117[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_117)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb45f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 896bv64), RAX);

label_0xb467:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb46f:
RAX := LOAD_LE_64(mem, RAX);

label_0xb472:
t1_121 := RAX;
t2_122 := 24bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb476:
mem := STORE_LE_64(mem, PLUS_64(RSP, 568bv64), RAX);

label_0xb47e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0xb486:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb48c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb491:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0xb494:
if (bv2bool(ZF)) {
  goto label_0xb497;
}

label_0xb496:
assume false;

label_0xb497:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0xb49f:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_44);

label_0xb4a3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb4aa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb4ae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0xb4b6:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_46);

label_0xb4ba:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0xb4be:
if (bv2bool(CF)) {
  goto label_0xb4c1;
}

label_0xb4c0:
assume false;

label_0xb4c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 568bv64));

label_0xb4c9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 896bv64));

label_0xb4d1:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xb4d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb4dc:
RAX := LOAD_LE_64(mem, RAX);

label_0xb4df:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0xb4e2:
t_145 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_145, 1bv32)), (XOR_32(t_145, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb4e4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 648bv64), RAX[32:0]);

label_0xb4eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb4f3:
RAX := LOAD_LE_64(mem, RAX);

label_0xb4f6:
t1_149 := RAX;
t2_150 := 32bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb4fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 576bv64), RAX);

label_0xb502:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0xb50a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb510:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb515:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0xb518:
if (bv2bool(ZF)) {
  goto label_0xb51b;
}

label_0xb51a:
assume false;

label_0xb51b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0xb523:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_54);

label_0xb527:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb52e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb532:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0xb53a:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_56);

label_0xb53e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0xb542:
if (bv2bool(CF)) {
  goto label_0xb545;
}

label_0xb544:
assume false;

label_0xb545:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 576bv64));

label_0xb54d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 648bv64)));

label_0xb554:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb556:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb55e:
RAX := LOAD_LE_64(mem, RAX);

label_0xb561:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 36bv64)));

label_0xb564:
t_173 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_173[32:31]) == (1bv32[32:31]))), (XOR_1((t_173[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_173)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb566:
mem := STORE_LE_32(mem, PLUS_64(RSP, 652bv64), RAX[32:0]);

label_0xb56d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb575:
RAX := LOAD_LE_64(mem, RAX);

label_0xb578:
t1_177 := RAX;
t2_178 := 36bv64;
RAX := PLUS_64(RAX, t2_178);
CF := bool2bv(LT_64(RAX, t1_177));
OF := AND_1((bool2bv((t1_177[64:63]) == (t2_178[64:63]))), (XOR_1((t1_177[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_177)), t2_178)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb57c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 584bv64), RAX);

label_0xb584:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 584bv64));

label_0xb58c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb592:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb597:
t_185 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))))[1:0]));
SF := t_185[64:63];
ZF := bool2bv(0bv64 == t_185);

label_0xb59a:
if (bv2bool(ZF)) {
  goto label_0xb59d;
}

label_0xb59c:
assume false;

label_0xb59d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 584bv64));

label_0xb5a5:
origDEST_189 := RAX;
origCOUNT_190 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_64);

label_0xb5a9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb5b0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb5b4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 584bv64));

label_0xb5bc:
origDEST_195 := RCX;
origCOUNT_196 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), CF, LSHIFT_64(origDEST_195, (MINUS_64(64bv64, origCOUNT_196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_196 == 1bv64)), origDEST_195[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), AF, unconstrained_66);

label_0xb5c0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0xb5c4:
if (bv2bool(CF)) {
  goto label_0xb5c7;
}

label_0xb5c6:
assume false;

label_0xb5c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 584bv64));

label_0xb5cf:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 652bv64)));

label_0xb5d6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb5d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb5e0:
RAX := LOAD_LE_64(mem, RAX);

label_0xb5e3:
t_201 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), t_201)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_201, (LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))))[1:0]));
SF := t_201[32:31];
ZF := bool2bv(0bv32 == t_201);

label_0xb5e7:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb66f;
}

label_0xb5ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb5f5:
RAX := LOAD_LE_64(mem, RAX);

label_0xb5f8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 40bv64)));

label_0xb5fb:
t_205 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_205[32:31]) == (1bv32[32:31]))), (XOR_1((t_205[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_205)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb5fd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 656bv64), RAX[32:0]);

label_0xb604:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb60c:
RAX := LOAD_LE_64(mem, RAX);

label_0xb60f:
t1_209 := RAX;
t2_210 := 40bv64;
RAX := PLUS_64(RAX, t2_210);
CF := bool2bv(LT_64(RAX, t1_209));
OF := AND_1((bool2bv((t1_209[64:63]) == (t2_210[64:63]))), (XOR_1((t1_209[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_209)), t2_210)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb613:
mem := STORE_LE_64(mem, PLUS_64(RSP, 592bv64), RAX);

label_0xb61b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 592bv64));

label_0xb623:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb629:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb62e:
t_217 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))))[1:0]));
SF := t_217[64:63];
ZF := bool2bv(0bv64 == t_217);

label_0xb631:
if (bv2bool(ZF)) {
  goto label_0xb634;
}

label_0xb633:
assume false;

label_0xb634:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 592bv64));

label_0xb63c:
origDEST_221 := RAX;
origCOUNT_222 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), CF, LSHIFT_64(origDEST_221, (MINUS_64(64bv64, origCOUNT_222)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_222 == 1bv64)), origDEST_221[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), AF, unconstrained_74);

label_0xb640:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb647:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb64b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 592bv64));

label_0xb653:
origDEST_227 := RCX;
origCOUNT_228 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_76);

label_0xb657:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_77;
SF := unconstrained_78;
AF := unconstrained_79;
PF := unconstrained_80;

label_0xb65b:
if (bv2bool(CF)) {
  goto label_0xb65e;
}

label_0xb65d:
assume false;

label_0xb65e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 592bv64));

label_0xb666:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 656bv64)));

label_0xb66d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb66f:
goto label_0xb26b;

label_0xb674:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb67c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xb682:
t_233 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_233[32:31]) == (1bv32[32:31]))), (XOR_1((t_233[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_233)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb684:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb68c:
t_237 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_237)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_237, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)), 2bv32)), (XOR_32((RSHIFT_32(t_237, 4bv32)), t_237)))))[1:0]));
SF := t_237[32:31];
ZF := bool2bv(0bv32 == t_237);

label_0xb692:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb69b;
}

label_0xb694:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_81;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xb696:
goto label_0xdea1;

label_0xb69b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb6a3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xb6a9:
t_241 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_241[32:31]) == (1bv32[32:31]))), (XOR_1((t_241[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_241)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb6ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb6b3:
t_245 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_245)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_245, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)), 2bv32)), (XOR_32((RSHIFT_32(t_245, 4bv32)), t_245)))))[1:0]));
SF := t_245[32:31];
ZF := bool2bv(0bv32 == t_245);

label_0xb6b9:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xb6c2;
}

label_0xb6bb:
RAX := (RAX[64:8]) ++ 1bv8;

label_0xb6bd:
goto label_0xdea1;

label_0xb6c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb6ca:
t1_249 := RAX;
t2_250 := 16bv64;
RAX := PLUS_64(RAX, t2_250);
CF := bool2bv(LT_64(RAX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb6ce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 600bv64), RAX);

label_0xb6d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 600bv64));

label_0xb6de:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb6e4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb6e9:
t_257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_83;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))))[1:0]));
SF := t_257[64:63];
ZF := bool2bv(0bv64 == t_257);

label_0xb6ec:
if (bv2bool(ZF)) {
  goto label_0xb6ef;
}

label_0xb6ee:
assume false;

label_0xb6ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 600bv64));

label_0xb6f7:
origDEST_261 := RAX;
origCOUNT_262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_85);

label_0xb6fb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb702:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb706:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 600bv64));

label_0xb70e:
origDEST_267 := RCX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_87);

label_0xb712:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_88;
SF := unconstrained_89;
AF := unconstrained_90;
PF := unconstrained_91;

label_0xb716:
if (bv2bool(CF)) {
  goto label_0xb719;
}

label_0xb718:
assume false;

label_0xb719:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 600bv64));

label_0xb721:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0xb727:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb72f:
t1_273 := RAX;
t2_274 := 64bv64;
RAX := PLUS_64(RAX, t2_274);
CF := bool2bv(LT_64(RAX, t1_273));
OF := AND_1((bool2bv((t1_273[64:63]) == (t2_274[64:63]))), (XOR_1((t1_273[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_273)), t2_274)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb733:
mem := STORE_LE_64(mem, PLUS_64(RSP, 904bv64), RAX);

label_0xb73b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb743:
t1_279 := RAX;
t2_280 := 12bv64;
RAX := PLUS_64(RAX, t2_280);
CF := bool2bv(LT_64(RAX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb747:
mem := STORE_LE_64(mem, PLUS_64(RSP, 464bv64), RAX);

label_0xb74f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0xb757:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb75d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb762:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_93;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0xb765:
if (bv2bool(ZF)) {
  goto label_0xb768;
}

label_0xb767:
assume false;

label_0xb768:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0xb770:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_94));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_95);

label_0xb774:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb77b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb77f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0xb787:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_97);

label_0xb78b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_98;
SF := unconstrained_99;
AF := unconstrained_100;
PF := unconstrained_101;

label_0xb78f:
if (bv2bool(CF)) {
  goto label_0xb792;
}

label_0xb791:
assume false;

label_0xb792:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0xb79a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 904bv64));

label_0xb7a2:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0xb7a5:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xb7a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb7af:
t1_303 := RAX;
t2_304 := 1096bv64;
RAX := PLUS_64(RAX, t2_304);
CF := bool2bv(LT_64(RAX, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb7b5:
RDX := RAX;

label_0xb7b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb7c0:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xb7c3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 47048bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xb7c8"} true;
call arbitrary_func();

label_0xb7c8:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xb7cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb7d4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xb7d7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb7df:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xb7e6:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xb7ea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb7f2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xb7f5:
origDEST_309 := RCX[32:0];
origCOUNT_310 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), CF, LSHIFT_32(origDEST_309, (MINUS_32(32bv32, origCOUNT_310)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv32)), origDEST_309[32:31], unconstrained_102));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv32)), AF, unconstrained_103);

label_0xb7f7:
RCX := (0bv32 ++ RCX[32:0]);

label_0xb7f9:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb801:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xb808:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xb80c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 660bv64), RCX[32:0]);

label_0xb813:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb81b:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xb81e:
origDEST_315 := RDX[32:0];
origCOUNT_316 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), CF, RSHIFT_32(origDEST_315, (MINUS_32(32bv32, origCOUNT_316)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_104));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv32)), AF, unconstrained_105);

label_0xb821:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xb824:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xb827:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 660bv64)));

label_0xb82e:
origDEST_323 := RDX[32:0];
origCOUNT_324 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), CF, LSHIFT_32(origDEST_323, (MINUS_32(32bv32, origCOUNT_324)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_324 == 1bv32)), origDEST_323[32:31], unconstrained_107));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_324 == 0bv32)), AF, unconstrained_108);

label_0xb830:
RCX := (0bv32 ++ RDX[32:0]);

label_0xb832:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_109;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xb835:
origDEST_331 := RCX[32:0];
origCOUNT_332 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), CF, RSHIFT_32(origDEST_331, (MINUS_32(32bv32, origCOUNT_332)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_332 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv32)), AF, unconstrained_111);

label_0xb838:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_112;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb83a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 664bv64), RAX[32:0]);

label_0xb841:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb849:
t1_339 := RAX;
t2_340 := 60bv64;
RAX := PLUS_64(RAX, t2_340);
CF := bool2bv(LT_64(RAX, t1_339));
OF := AND_1((bool2bv((t1_339[64:63]) == (t2_340[64:63]))), (XOR_1((t1_339[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_339)), t2_340)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb84d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 616bv64), RAX);

label_0xb855:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 616bv64));

label_0xb85d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_113;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb863:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb868:
t_347 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_114;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_347, 4bv64)), t_347)), 2bv64)), (XOR_64((RSHIFT_64(t_347, 4bv64)), t_347)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_347, 4bv64)), t_347)), 2bv64)), (XOR_64((RSHIFT_64(t_347, 4bv64)), t_347)))))[1:0]));
SF := t_347[64:63];
ZF := bool2bv(0bv64 == t_347);

label_0xb86b:
if (bv2bool(ZF)) {
  goto label_0xb86e;
}

label_0xb86d:
assume false;

label_0xb86e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 616bv64));

label_0xb876:
origDEST_351 := RAX;
origCOUNT_352 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), CF, LSHIFT_64(origDEST_351, (MINUS_64(64bv64, origCOUNT_352)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_352 == 1bv64)), origDEST_351[64:63], unconstrained_115));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), AF, unconstrained_116);

label_0xb87a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb881:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb885:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 616bv64));

label_0xb88d:
origDEST_357 := RCX;
origCOUNT_358 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), CF, LSHIFT_64(origDEST_357, (MINUS_64(64bv64, origCOUNT_358)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_358 == 1bv64)), origDEST_357[64:63], unconstrained_117));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), AF, unconstrained_118);

label_0xb891:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_119;
SF := unconstrained_120;
AF := unconstrained_121;
PF := unconstrained_122;

label_0xb895:
if (bv2bool(CF)) {
  goto label_0xb898;
}

label_0xb897:
assume false;

label_0xb898:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 616bv64));

label_0xb8a0:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 664bv64)));

label_0xb8a7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb8a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb8b1:
t_363 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_363)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_363, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_363, 4bv32)), t_363)), 2bv32)), (XOR_32((RSHIFT_32(t_363, 4bv32)), t_363)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_363, 4bv32)), t_363)), 2bv32)), (XOR_32((RSHIFT_32(t_363, 4bv32)), t_363)))))[1:0]));
SF := t_363[32:31];
ZF := bool2bv(0bv32 == t_363);

label_0xb8b5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xba2b;
}

label_0xb8bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb8c3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xb8c7:
origDEST_367 := RAX;
origCOUNT_368 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, RSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_123));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_124);

label_0xb8cb:
RCX := PLUS_64((PLUS_64(0bv64, 47314bv64)), 0bv64)[64:0];

label_0xb8d2:
t1_373 := RCX;
t2_374 := RAX;
RCX := PLUS_64(RCX, t2_374);
CF := bool2bv(LT_64(RCX, t1_373));
OF := AND_1((bool2bv((t1_373[64:63]) == (t2_374[64:63]))), (XOR_1((t1_373[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_373)), t2_374)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xb8d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 912bv64), RCX);

label_0xb8dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb8e5:
t1_379 := RAX;
t2_380 := 24bv64;
RAX := PLUS_64(RAX, t2_380);
CF := bool2bv(LT_64(RAX, t1_379));
OF := AND_1((bool2bv((t1_379[64:63]) == (t2_380[64:63]))), (XOR_1((t1_379[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_379)), t2_380)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb8e9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 624bv64), RAX);

label_0xb8f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 624bv64));

label_0xb8f9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb8ff:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb904:
t_387 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_387, 4bv64)), t_387)), 2bv64)), (XOR_64((RSHIFT_64(t_387, 4bv64)), t_387)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_387, 4bv64)), t_387)), 2bv64)), (XOR_64((RSHIFT_64(t_387, 4bv64)), t_387)))))[1:0]));
SF := t_387[64:63];
ZF := bool2bv(0bv64 == t_387);

label_0xb907:
if (bv2bool(ZF)) {
  goto label_0xb90a;
}

label_0xb909:
assume false;

label_0xb90a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 624bv64));

label_0xb912:
origDEST_391 := RAX;
origCOUNT_392 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), CF, LSHIFT_64(origDEST_391, (MINUS_64(64bv64, origCOUNT_392)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_392 == 1bv64)), origDEST_391[64:63], unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_392 == 0bv64)), AF, unconstrained_128);

label_0xb916:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb91d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb921:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 624bv64));

label_0xb929:
origDEST_397 := RCX;
origCOUNT_398 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), CF, LSHIFT_64(origDEST_397, (MINUS_64(64bv64, origCOUNT_398)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_398 == 1bv64)), origDEST_397[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_398 == 0bv64)), AF, unconstrained_130);

label_0xb92d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_131;
SF := unconstrained_132;
AF := unconstrained_133;
PF := unconstrained_134;

label_0xb931:
if (bv2bool(CF)) {
  goto label_0xb934;
}

label_0xb933:
assume false;

label_0xb934:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 624bv64));

label_0xb93c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 912bv64));

label_0xb944:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xb946:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb948:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb950:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xb953:
t_403 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_403[32:31]) == (1bv32[32:31]))), (XOR_1((t_403[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_403)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb955:
mem := STORE_LE_32(mem, PLUS_64(RSP, 668bv64), RAX[32:0]);

label_0xb95c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb964:
t1_407 := RAX;
t2_408 := 28bv64;
RAX := PLUS_64(RAX, t2_408);
CF := bool2bv(LT_64(RAX, t1_407));
OF := AND_1((bool2bv((t1_407[64:63]) == (t2_408[64:63]))), (XOR_1((t1_407[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_407)), t2_408)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb968:
mem := STORE_LE_64(mem, PLUS_64(RSP, 632bv64), RAX);

label_0xb970:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 632bv64));

label_0xb978:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb97e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb983:
t_415 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_415, 4bv64)), t_415)), 2bv64)), (XOR_64((RSHIFT_64(t_415, 4bv64)), t_415)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_415, 4bv64)), t_415)), 2bv64)), (XOR_64((RSHIFT_64(t_415, 4bv64)), t_415)))))[1:0]));
SF := t_415[64:63];
ZF := bool2bv(0bv64 == t_415);

label_0xb986:
if (bv2bool(ZF)) {
  goto label_0xb989;
}

label_0xb988:
assume false;

label_0xb989:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 632bv64));

label_0xb991:
origDEST_419 := RAX;
origCOUNT_420 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), CF, LSHIFT_64(origDEST_419, (MINUS_64(64bv64, origCOUNT_420)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_420 == 1bv64)), origDEST_419[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), AF, unconstrained_138);

label_0xb995:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb99c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb9a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 632bv64));

label_0xb9a8:
origDEST_425 := RCX;
origCOUNT_426 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), CF, LSHIFT_64(origDEST_425, (MINUS_64(64bv64, origCOUNT_426)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_426 == 1bv64)), origDEST_425[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), AF, unconstrained_140);

label_0xb9ac:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_141;
SF := unconstrained_142;
AF := unconstrained_143;
PF := unconstrained_144;

label_0xb9b0:
if (bv2bool(CF)) {
  goto label_0xb9b3;
}

label_0xb9b2:
assume false;

label_0xb9b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 632bv64));

label_0xb9bb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 668bv64)));

label_0xb9c2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb9c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb9cc:
t_431 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_431)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_431, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)), 2bv32)), (XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)), 2bv32)), (XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)))))[1:0]));
SF := t_431[32:31];
ZF := bool2bv(0bv32 == t_431);

label_0xb9d3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xba2b;
}

label_0xb9d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xb9dd:
t1_435 := RAX;
t2_436 := 28bv64;
RAX := PLUS_64(RAX, t2_436);
CF := bool2bv(LT_64(RAX, t1_435));
OF := AND_1((bool2bv((t1_435[64:63]) == (t2_436[64:63]))), (XOR_1((t1_435[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_435)), t2_436)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb9e1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0xb9e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xb9eb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_145;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb9f1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb9f6:
t_443 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))))[1:0]));
SF := t_443[64:63];
ZF := bool2bv(0bv64 == t_443);

label_0xb9f9:
if (bv2bool(ZF)) {
  goto label_0xb9fc;
}

label_0xb9fb:
assume false;

label_0xb9fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xba01:
origDEST_447 := RAX;
origCOUNT_448 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), CF, LSHIFT_64(origDEST_447, (MINUS_64(64bv64, origCOUNT_448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_448 == 1bv64)), origDEST_447[64:63], unconstrained_147));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), AF, unconstrained_148);

label_0xba05:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xba0c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xba10:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xba15:
origDEST_453 := RCX;
origCOUNT_454 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), CF, LSHIFT_64(origDEST_453, (MINUS_64(64bv64, origCOUNT_454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_454 == 1bv64)), origDEST_453[64:63], unconstrained_149));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), AF, unconstrained_150);

label_0xba19:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_151;
SF := unconstrained_152;
AF := unconstrained_153;
PF := unconstrained_154;

label_0xba1d:
if (bv2bool(CF)) {
  goto label_0xba20;
}

label_0xba1f:
assume false;

label_0xba20:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xba25:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xba2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xba33:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xba36:
t_459 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_459, 1bv32)), (XOR_32(t_459, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_459)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xba38:
mem := STORE_LE_32(mem, PLUS_64(RSP, 672bv64), RAX[32:0]);

label_0xba3f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xba47:
t1_463 := RAX;
t2_464 := 24bv64;
RAX := PLUS_64(RAX, t2_464);
CF := bool2bv(LT_64(RAX, t1_463));
OF := AND_1((bool2bv((t1_463[64:63]) == (t2_464[64:63]))), (XOR_1((t1_463[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_463)), t2_464)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xba4b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0xba50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xba55:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_155;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xba5b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xba60:
t_471 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_471, 4bv64)), t_471)), 2bv64)), (XOR_64((RSHIFT_64(t_471, 4bv64)), t_471)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_471, 4bv64)), t_471)), 2bv64)), (XOR_64((RSHIFT_64(t_471, 4bv64)), t_471)))))[1:0]));
SF := t_471[64:63];
ZF := bool2bv(0bv64 == t_471);

label_0xba63:
if (bv2bool(ZF)) {
  goto label_0xba66;
}

label_0xba65:
assume false;

label_0xba66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xba6b:
origDEST_475 := RAX;
origCOUNT_476 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), CF, LSHIFT_64(origDEST_475, (MINUS_64(64bv64, origCOUNT_476)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_476 == 1bv64)), origDEST_475[64:63], unconstrained_157));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_476 == 0bv64)), AF, unconstrained_158);

label_0xba6f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xba76:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xba7a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xba7f:
origDEST_481 := RCX;
origCOUNT_482 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), CF, LSHIFT_64(origDEST_481, (MINUS_64(64bv64, origCOUNT_482)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_482 == 1bv64)), origDEST_481[64:63], unconstrained_159));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_482 == 0bv64)), AF, unconstrained_160);

label_0xba83:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_161;
SF := unconstrained_162;
AF := unconstrained_163;
PF := unconstrained_164;

label_0xba87:
if (bv2bool(CF)) {
  goto label_0xba8a;
}

label_0xba89:
assume false;

label_0xba8a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xba8f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 672bv64)));

label_0xba96:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xba98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbaa0:
t_487 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_487)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_487, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_487, 4bv32)), t_487)), 2bv32)), (XOR_32((RSHIFT_32(t_487, 4bv32)), t_487)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_487, 4bv32)), t_487)), 2bv32)), (XOR_32((RSHIFT_32(t_487, 4bv32)), t_487)))))[1:0]));
SF := t_487[32:31];
ZF := bool2bv(0bv32 == t_487);

label_0xbaa4:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbab0;
}

label_0xbaa6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0xbaae:
goto label_0xbab8;

label_0xbab0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0xbab8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbabd:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_165;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbac1:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xbac5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbacd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xbad3:
t_493 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_493[32:31]) == (1bv32[32:31]))), (XOR_1((t_493[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_493)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbad5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 676bv64), RAX[32:0]);

label_0xbadc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbae4:
t1_497 := RAX;
t2_498 := 1092bv64;
RAX := PLUS_64(RAX, t2_498);
CF := bool2bv(LT_64(RAX, t1_497));
OF := AND_1((bool2bv((t1_497[64:63]) == (t2_498[64:63]))), (XOR_1((t1_497[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_497)), t2_498)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbaea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0xbaef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xbaf4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_166;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbafa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbaff:
t_505 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_505, 4bv64)), t_505)), 2bv64)), (XOR_64((RSHIFT_64(t_505, 4bv64)), t_505)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_505, 4bv64)), t_505)), 2bv64)), (XOR_64((RSHIFT_64(t_505, 4bv64)), t_505)))))[1:0]));
SF := t_505[64:63];
ZF := bool2bv(0bv64 == t_505);

label_0xbb02:
if (bv2bool(ZF)) {
  goto label_0xbb05;
}

label_0xbb04:
assume false;

label_0xbb05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xbb0a:
origDEST_509 := RAX;
origCOUNT_510 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), CF, LSHIFT_64(origDEST_509, (MINUS_64(64bv64, origCOUNT_510)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_510 == 1bv64)), origDEST_509[64:63], unconstrained_168));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_510 == 0bv64)), AF, unconstrained_169);

label_0xbb0e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbb15:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbb19:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xbb1e:
origDEST_515 := RCX;
origCOUNT_516 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), CF, LSHIFT_64(origDEST_515, (MINUS_64(64bv64, origCOUNT_516)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_516 == 1bv64)), origDEST_515[64:63], unconstrained_170));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), AF, unconstrained_171);

label_0xbb22:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_172;
SF := unconstrained_173;
AF := unconstrained_174;
PF := unconstrained_175;

label_0xbb26:
if (bv2bool(CF)) {
  goto label_0xbb29;
}

label_0xbb28:
assume false;

label_0xbb29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xbb2e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 676bv64)));

label_0xbb35:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbb37:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbb3f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xbb45:
t_521 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_521[32:31]) == (1bv32[32:31]))), (XOR_1((t_521[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_521)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbb47:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbb4f:
t_525 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_525)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_525, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_525, 4bv32)), t_525)), 2bv32)), (XOR_32((RSHIFT_32(t_525, 4bv32)), t_525)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_525, 4bv32)), t_525)), 2bv32)), (XOR_32((RSHIFT_32(t_525, 4bv32)), t_525)))))[1:0]));
SF := t_525[32:31];
ZF := bool2bv(0bv32 == t_525);

label_0xbb55:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbb5c;
}

label_0xbb57:
goto label_0xb260;

label_0xbb5c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbb61:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbb69:
t_529 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_529)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_529, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_529, 4bv32)), t_529)), 2bv32)), (XOR_32((RSHIFT_32(t_529, 4bv32)), t_529)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_529, 4bv32)), t_529)), 2bv32)), (XOR_32((RSHIFT_32(t_529, 4bv32)), t_529)))))[1:0]));
SF := t_529[32:31];
ZF := bool2bv(0bv32 == t_529);

label_0xbb6c:
if (bv2bool(ZF)) {
  goto label_0xbbd8;
}

label_0xbb6e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbb76:
t1_533 := RAX;
t2_534 := 64bv64;
RAX := PLUS_64(RAX, t2_534);
CF := bool2bv(LT_64(RAX, t1_533));
OF := AND_1((bool2bv((t1_533[64:63]) == (t2_534[64:63]))), (XOR_1((t1_533[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_533)), t2_534)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbb7a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0xbb7f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbb84:
mem := STORE_LE_32(mem, PLUS_64(RSP, 680bv64), RAX[32:0]);

label_0xbb8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xbb90:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbb96:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbb9b:
t_541 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_541, 4bv64)), t_541)), 2bv64)), (XOR_64((RSHIFT_64(t_541, 4bv64)), t_541)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_541, 4bv64)), t_541)), 2bv64)), (XOR_64((RSHIFT_64(t_541, 4bv64)), t_541)))))[1:0]));
SF := t_541[64:63];
ZF := bool2bv(0bv64 == t_541);

label_0xbb9e:
if (bv2bool(ZF)) {
  goto label_0xbba1;
}

label_0xbba0:
assume false;

label_0xbba1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xbba6:
origDEST_545 := RAX;
origCOUNT_546 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), CF, LSHIFT_64(origDEST_545, (MINUS_64(64bv64, origCOUNT_546)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_546 == 1bv64)), origDEST_545[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), AF, unconstrained_179);

label_0xbbaa:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbbb1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbbb5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xbbba:
origDEST_551 := RCX;
origCOUNT_552 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), CF, LSHIFT_64(origDEST_551, (MINUS_64(64bv64, origCOUNT_552)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_552 == 1bv64)), origDEST_551[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_552 == 0bv64)), AF, unconstrained_181);

label_0xbbbe:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_182;
SF := unconstrained_183;
AF := unconstrained_184;
PF := unconstrained_185;

label_0xbbc2:
if (bv2bool(CF)) {
  goto label_0xbbc5;
}

label_0xbbc4:
assume false;

label_0xbbc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xbbca:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 680bv64)));

label_0xbbd1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbbd3:
goto label_0xb260;

label_0xbbd8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbbe0:
t1_557 := RAX;
t2_558 := 16bv64;
RAX := PLUS_64(RAX, t2_558);
CF := bool2bv(LT_64(RAX, t1_557));
OF := AND_1((bool2bv((t1_557[64:63]) == (t2_558[64:63]))), (XOR_1((t1_557[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_557)), t2_558)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbbe4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0xbbe9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xbbee:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbbf4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbbf9:
t_565 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_565, 4bv64)), t_565)), 2bv64)), (XOR_64((RSHIFT_64(t_565, 4bv64)), t_565)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_565, 4bv64)), t_565)), 2bv64)), (XOR_64((RSHIFT_64(t_565, 4bv64)), t_565)))))[1:0]));
SF := t_565[64:63];
ZF := bool2bv(0bv64 == t_565);

label_0xbbfc:
if (bv2bool(ZF)) {
  goto label_0xbbff;
}

label_0xbbfe:
assume false;

label_0xbbff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xbc04:
origDEST_569 := RAX;
origCOUNT_570 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), CF, LSHIFT_64(origDEST_569, (MINUS_64(64bv64, origCOUNT_570)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_570 == 1bv64)), origDEST_569[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_570 == 0bv64)), AF, unconstrained_189);

label_0xbc08:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbc0f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbc13:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xbc18:
origDEST_575 := RCX;
origCOUNT_576 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), CF, LSHIFT_64(origDEST_575, (MINUS_64(64bv64, origCOUNT_576)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_576 == 1bv64)), origDEST_575[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_576 == 0bv64)), AF, unconstrained_191);

label_0xbc1c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_192;
SF := unconstrained_193;
AF := unconstrained_194;
PF := unconstrained_195;

label_0xbc20:
if (bv2bool(CF)) {
  goto label_0xbc23;
}

label_0xbc22:
assume false;

label_0xbc23:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xbc28:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0xbc2e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc36:
t1_581 := RAX;
t2_582 := 1096bv64;
RAX := PLUS_64(RAX, t2_582);
CF := bool2bv(LT_64(RAX, t1_581));
OF := AND_1((bool2bv((t1_581[64:63]) == (t2_582[64:63]))), (XOR_1((t1_581[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_581)), t2_582)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbc3c:
RDX := RAX;

label_0xbc3f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc47:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xbc4a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 48207bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xbc4f"} true;
call arbitrary_func();

label_0xbc4f:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xbc53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc5b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xbc5e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc66:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xbc6d:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xbc71:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc79:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xbc7c:
origDEST_587 := RCX[32:0];
origCOUNT_588 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), CF, LSHIFT_32(origDEST_587, (MINUS_32(32bv32, origCOUNT_588)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_588 == 1bv32)), origDEST_587[32:31], unconstrained_196));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_588 == 0bv32)), AF, unconstrained_197);

label_0xbc7e:
RCX := (0bv32 ++ RCX[32:0]);

label_0xbc80:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbc88:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xbc8f:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xbc93:
mem := STORE_LE_32(mem, PLUS_64(RSP, 684bv64), RCX[32:0]);

label_0xbc9a:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbca2:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xbca5:
origDEST_593 := RDX[32:0];
origCOUNT_594 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), CF, RSHIFT_32(origDEST_593, (MINUS_32(32bv32, origCOUNT_594)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_594 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_198));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv32)), AF, unconstrained_199);

label_0xbca8:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_200;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xbcab:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xbcae:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 684bv64)));

label_0xbcb5:
origDEST_601 := RDX[32:0];
origCOUNT_602 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), CF, LSHIFT_32(origDEST_601, (MINUS_32(32bv32, origCOUNT_602)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_602 == 1bv32)), origDEST_601[32:31], unconstrained_201));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv32)), AF, unconstrained_202);

label_0xbcb7:
RCX := (0bv32 ++ RDX[32:0]);

label_0xbcb9:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_203;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xbcbc:
origDEST_609 := RCX[32:0];
origCOUNT_610 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), CF, RSHIFT_32(origDEST_609, (MINUS_32(32bv32, origCOUNT_610)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_610 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_204));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_610 == 0bv32)), AF, unconstrained_205);

label_0xbcbf:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_206;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbcc1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 876bv64), RAX[32:0]);

label_0xbcc8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbcd0:
t1_617 := RAX;
t2_618 := 60bv64;
RAX := PLUS_64(RAX, t2_618);
CF := bool2bv(LT_64(RAX, t1_617));
OF := AND_1((bool2bv((t1_617[64:63]) == (t2_618[64:63]))), (XOR_1((t1_617[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_617)), t2_618)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbcd4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0xbcd9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0xbcde:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbce4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbce9:
t_625 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_208;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_625, 4bv64)), t_625)), 2bv64)), (XOR_64((RSHIFT_64(t_625, 4bv64)), t_625)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_625, 4bv64)), t_625)), 2bv64)), (XOR_64((RSHIFT_64(t_625, 4bv64)), t_625)))))[1:0]));
SF := t_625[64:63];
ZF := bool2bv(0bv64 == t_625);

label_0xbcec:
if (bv2bool(ZF)) {
  goto label_0xbcef;
}

label_0xbcee:
assume false;

label_0xbcef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0xbcf4:
origDEST_629 := RAX;
origCOUNT_630 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), CF, LSHIFT_64(origDEST_629, (MINUS_64(64bv64, origCOUNT_630)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_630 == 1bv64)), origDEST_629[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), AF, unconstrained_210);

label_0xbcf8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbcff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbd03:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0xbd08:
origDEST_635 := RCX;
origCOUNT_636 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), CF, LSHIFT_64(origDEST_635, (MINUS_64(64bv64, origCOUNT_636)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_636 == 1bv64)), origDEST_635[64:63], unconstrained_211));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_636 == 0bv64)), AF, unconstrained_212);

label_0xbd0c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_213;
SF := unconstrained_214;
AF := unconstrained_215;
PF := unconstrained_216;

label_0xbd10:
if (bv2bool(CF)) {
  goto label_0xbd13;
}

label_0xbd12:
assume false;

label_0xbd13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0xbd18:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 876bv64)));

label_0xbd1f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbd21:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbd29:
t_641 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_641)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_641, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_641, 4bv32)), t_641)), 2bv32)), (XOR_32((RSHIFT_32(t_641, 4bv32)), t_641)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_641, 4bv32)), t_641)), 2bv32)), (XOR_32((RSHIFT_32(t_641, 4bv32)), t_641)))))[1:0]));
SF := t_641[32:31];
ZF := bool2bv(0bv32 == t_641);

label_0xbd2d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbe85;
}

label_0xbd33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbd3b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xbd3f:
origDEST_645 := RAX;
origCOUNT_646 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), CF, RSHIFT_64(origDEST_645, (MINUS_64(64bv64, origCOUNT_646)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_646 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_217));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), AF, unconstrained_218);

label_0xbd43:
RCX := PLUS_64((PLUS_64(0bv64, 48458bv64)), 0bv64)[64:0];

label_0xbd4a:
t1_651 := RCX;
t2_652 := RAX;
RCX := PLUS_64(RCX, t2_652);
CF := bool2bv(LT_64(RCX, t1_651));
OF := AND_1((bool2bv((t1_651[64:63]) == (t2_652[64:63]))), (XOR_1((t1_651[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_651)), t2_652)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xbd4d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 920bv64), RCX);

label_0xbd55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbd5d:
t1_657 := RAX;
t2_658 := 24bv64;
RAX := PLUS_64(RAX, t2_658);
CF := bool2bv(LT_64(RAX, t1_657));
OF := AND_1((bool2bv((t1_657[64:63]) == (t2_658[64:63]))), (XOR_1((t1_657[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_657)), t2_658)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbd61:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0xbd66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xbd6b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_219;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbd71:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbd76:
t_665 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_220;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)), 2bv64)), (XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)), 2bv64)), (XOR_64((RSHIFT_64(t_665, 4bv64)), t_665)))))[1:0]));
SF := t_665[64:63];
ZF := bool2bv(0bv64 == t_665);

label_0xbd79:
if (bv2bool(ZF)) {
  goto label_0xbd7c;
}

label_0xbd7b:
assume false;

label_0xbd7c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xbd81:
origDEST_669 := RAX;
origCOUNT_670 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), CF, LSHIFT_64(origDEST_669, (MINUS_64(64bv64, origCOUNT_670)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_670 == 1bv64)), origDEST_669[64:63], unconstrained_221));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_670 == 0bv64)), AF, unconstrained_222);

label_0xbd85:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbd8c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbd90:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xbd95:
origDEST_675 := RCX;
origCOUNT_676 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), CF, LSHIFT_64(origDEST_675, (MINUS_64(64bv64, origCOUNT_676)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_676 == 1bv64)), origDEST_675[64:63], unconstrained_223));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_676 == 0bv64)), AF, unconstrained_224);

label_0xbd99:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_225;
SF := unconstrained_226;
AF := unconstrained_227;
PF := unconstrained_228;

label_0xbd9d:
if (bv2bool(CF)) {
  goto label_0xbda0;
}

label_0xbd9f:
assume false;

label_0xbda0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xbda5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 920bv64));

label_0xbdad:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xbdaf:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbdb1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbdb9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xbdbc:
t_681 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_681[32:31]) == (1bv32[32:31]))), (XOR_1((t_681[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_681)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbdbe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 688bv64), RAX[32:0]);

label_0xbdc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbdcd:
t1_685 := RAX;
t2_686 := 28bv64;
RAX := PLUS_64(RAX, t2_686);
CF := bool2bv(LT_64(RAX, t1_685));
OF := AND_1((bool2bv((t1_685[64:63]) == (t2_686[64:63]))), (XOR_1((t1_685[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_685)), t2_686)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbdd1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0xbdd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xbddb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_229;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbde1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbde6:
t_693 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_230;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)), 2bv64)), (XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)), 2bv64)), (XOR_64((RSHIFT_64(t_693, 4bv64)), t_693)))))[1:0]));
SF := t_693[64:63];
ZF := bool2bv(0bv64 == t_693);

label_0xbde9:
if (bv2bool(ZF)) {
  goto label_0xbdec;
}

label_0xbdeb:
assume false;

label_0xbdec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xbdf1:
origDEST_697 := RAX;
origCOUNT_698 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), CF, LSHIFT_64(origDEST_697, (MINUS_64(64bv64, origCOUNT_698)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_698 == 1bv64)), origDEST_697[64:63], unconstrained_231));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_698 == 0bv64)), AF, unconstrained_232);

label_0xbdf5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbdfc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbe00:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xbe05:
origDEST_703 := RCX;
origCOUNT_704 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), CF, LSHIFT_64(origDEST_703, (MINUS_64(64bv64, origCOUNT_704)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_704 == 1bv64)), origDEST_703[64:63], unconstrained_233));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_704 == 0bv64)), AF, unconstrained_234);

label_0xbe09:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_235;
SF := unconstrained_236;
AF := unconstrained_237;
PF := unconstrained_238;

label_0xbe0d:
if (bv2bool(CF)) {
  goto label_0xbe10;
}

label_0xbe0f:
assume false;

label_0xbe10:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xbe15:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 688bv64)));

label_0xbe1c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbe1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbe26:
t_709 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_709)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_709, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)), 2bv32)), (XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)), 2bv32)), (XOR_32((RSHIFT_32(t_709, 4bv32)), t_709)))))[1:0]));
SF := t_709[32:31];
ZF := bool2bv(0bv32 == t_709);

label_0xbe2d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbe85;
}

label_0xbe2f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbe37:
t1_713 := RAX;
t2_714 := 28bv64;
RAX := PLUS_64(RAX, t2_714);
CF := bool2bv(LT_64(RAX, t1_713));
OF := AND_1((bool2bv((t1_713[64:63]) == (t2_714[64:63]))), (XOR_1((t1_713[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_713)), t2_714)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbe3b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0xbe40:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0xbe45:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_239;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbe4b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbe50:
t_721 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_240;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_721, 4bv64)), t_721)), 2bv64)), (XOR_64((RSHIFT_64(t_721, 4bv64)), t_721)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_721, 4bv64)), t_721)), 2bv64)), (XOR_64((RSHIFT_64(t_721, 4bv64)), t_721)))))[1:0]));
SF := t_721[64:63];
ZF := bool2bv(0bv64 == t_721);

label_0xbe53:
if (bv2bool(ZF)) {
  goto label_0xbe56;
}

label_0xbe55:
assume false;

label_0xbe56:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0xbe5b:
origDEST_725 := RAX;
origCOUNT_726 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), CF, LSHIFT_64(origDEST_725, (MINUS_64(64bv64, origCOUNT_726)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_726 == 1bv64)), origDEST_725[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_726 == 0bv64)), AF, unconstrained_242);

label_0xbe5f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbe66:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbe6a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0xbe6f:
origDEST_731 := RCX;
origCOUNT_732 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), CF, LSHIFT_64(origDEST_731, (MINUS_64(64bv64, origCOUNT_732)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_732 == 1bv64)), origDEST_731[64:63], unconstrained_243));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_732 == 0bv64)), AF, unconstrained_244);

label_0xbe73:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_245;
SF := unconstrained_246;
AF := unconstrained_247;
PF := unconstrained_248;

label_0xbe77:
if (bv2bool(CF)) {
  goto label_0xbe7a;
}

label_0xbe79:
assume false;

label_0xbe7a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0xbe7f:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xbe85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbe8d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xbe90:
t_737 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_737, 1bv32)), (XOR_32(t_737, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_737)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbe92:
mem := STORE_LE_32(mem, PLUS_64(RSP, 692bv64), RAX[32:0]);

label_0xbe99:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbea1:
t1_741 := RAX;
t2_742 := 24bv64;
RAX := PLUS_64(RAX, t2_742);
CF := bool2bv(LT_64(RAX, t1_741));
OF := AND_1((bool2bv((t1_741[64:63]) == (t2_742[64:63]))), (XOR_1((t1_741[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_741)), t2_742)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbea5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0xbead:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xbeb5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_249;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbebb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbec0:
t_749 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_250;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_749, 4bv64)), t_749)), 2bv64)), (XOR_64((RSHIFT_64(t_749, 4bv64)), t_749)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_749, 4bv64)), t_749)), 2bv64)), (XOR_64((RSHIFT_64(t_749, 4bv64)), t_749)))))[1:0]));
SF := t_749[64:63];
ZF := bool2bv(0bv64 == t_749);

label_0xbec3:
if (bv2bool(ZF)) {
  goto label_0xbec6;
}

label_0xbec5:
assume false;

label_0xbec6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xbece:
origDEST_753 := RAX;
origCOUNT_754 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), CF, LSHIFT_64(origDEST_753, (MINUS_64(64bv64, origCOUNT_754)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_754 == 1bv64)), origDEST_753[64:63], unconstrained_251));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_754 == 0bv64)), AF, unconstrained_252);

label_0xbed2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbed9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbedd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xbee5:
origDEST_759 := RCX;
origCOUNT_760 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), CF, LSHIFT_64(origDEST_759, (MINUS_64(64bv64, origCOUNT_760)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_760 == 1bv64)), origDEST_759[64:63], unconstrained_253));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_760 == 0bv64)), AF, unconstrained_254);

label_0xbee9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_255;
SF := unconstrained_256;
AF := unconstrained_257;
PF := unconstrained_258;

label_0xbeed:
if (bv2bool(CF)) {
  goto label_0xbef0;
}

label_0xbeef:
assume false;

label_0xbef0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xbef8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 692bv64)));

label_0xbeff:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbf01:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbf09:
t_765 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_765)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_765, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_765, 4bv32)), t_765)), 2bv32)), (XOR_32((RSHIFT_32(t_765, 4bv32)), t_765)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_765, 4bv32)), t_765)), 2bv32)), (XOR_32((RSHIFT_32(t_765, 4bv32)), t_765)))))[1:0]));
SF := t_765[32:31];
ZF := bool2bv(0bv32 == t_765);

label_0xbf0d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbf19;
}

label_0xbf0f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 1bv32);

label_0xbf17:
goto label_0xbf21;

label_0xbf19:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 0bv32);

label_0xbf21:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbf26:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_259;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbf2a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xbf2e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbf36:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xbf3c:
t_771 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_771[32:31]) == (1bv32[32:31]))), (XOR_1((t_771[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_771)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbf3e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 696bv64), RAX[32:0]);

label_0xbf45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbf4d:
t1_775 := RAX;
t2_776 := 1092bv64;
RAX := PLUS_64(RAX, t2_776);
CF := bool2bv(LT_64(RAX, t1_775));
OF := AND_1((bool2bv((t1_775[64:63]) == (t2_776[64:63]))), (XOR_1((t1_775[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_775)), t2_776)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbf53:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0xbf5b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xbf63:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_260;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbf69:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbf6e:
t_783 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_261;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_783, 4bv64)), t_783)), 2bv64)), (XOR_64((RSHIFT_64(t_783, 4bv64)), t_783)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_783, 4bv64)), t_783)), 2bv64)), (XOR_64((RSHIFT_64(t_783, 4bv64)), t_783)))))[1:0]));
SF := t_783[64:63];
ZF := bool2bv(0bv64 == t_783);

label_0xbf71:
if (bv2bool(ZF)) {
  goto label_0xbf74;
}

label_0xbf73:
assume false;

label_0xbf74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xbf7c:
origDEST_787 := RAX;
origCOUNT_788 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), CF, LSHIFT_64(origDEST_787, (MINUS_64(64bv64, origCOUNT_788)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_788 == 1bv64)), origDEST_787[64:63], unconstrained_262));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_788 == 0bv64)), AF, unconstrained_263);

label_0xbf80:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xbf87:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xbf8b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xbf93:
origDEST_793 := RCX;
origCOUNT_794 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), CF, LSHIFT_64(origDEST_793, (MINUS_64(64bv64, origCOUNT_794)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_794 == 1bv64)), origDEST_793[64:63], unconstrained_264));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_794 == 0bv64)), AF, unconstrained_265);

label_0xbf97:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_266;
SF := unconstrained_267;
AF := unconstrained_268;
PF := unconstrained_269;

label_0xbf9b:
if (bv2bool(CF)) {
  goto label_0xbf9e;
}

label_0xbf9d:
assume false;

label_0xbf9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0xbfa6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 696bv64)));

label_0xbfad:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xbfaf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbfb7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xbfbd:
t_799 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_799[32:31]) == (1bv32[32:31]))), (XOR_1((t_799[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_799)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbfbf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbfc7:
t_803 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_803)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_803, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_803, 4bv32)), t_803)), 2bv32)), (XOR_32((RSHIFT_32(t_803, 4bv32)), t_803)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_803, 4bv32)), t_803)), 2bv32)), (XOR_32((RSHIFT_32(t_803, 4bv32)), t_803)))))[1:0]));
SF := t_803[32:31];
ZF := bool2bv(0bv32 == t_803);

label_0xbfcd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xbfd4;
}

label_0xbfcf:
goto label_0xb260;

label_0xbfd4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbfd9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbfe1:
t_807 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_807)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_807, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_807, 4bv32)), t_807)), 2bv32)), (XOR_32((RSHIFT_32(t_807, 4bv32)), t_807)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_807, 4bv32)), t_807)), 2bv32)), (XOR_32((RSHIFT_32(t_807, 4bv32)), t_807)))))[1:0]));
SF := t_807[32:31];
ZF := bool2bv(0bv32 == t_807);

label_0xbfe4:
if (bv2bool(ZF)) {
  goto label_0xc05f;
}

label_0xbfe6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xbfee:
t1_811 := RAX;
t2_812 := 64bv64;
RAX := PLUS_64(RAX, t2_812);
CF := bool2bv(LT_64(RAX, t1_811));
OF := AND_1((bool2bv((t1_811[64:63]) == (t2_812[64:63]))), (XOR_1((t1_811[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_811)), t2_812)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbff2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0xbffa:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xbfff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 700bv64), RAX[32:0]);

label_0xc006:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xc00e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_270;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc014:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc019:
t_819 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_271;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_819, 4bv64)), t_819)), 2bv64)), (XOR_64((RSHIFT_64(t_819, 4bv64)), t_819)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_819, 4bv64)), t_819)), 2bv64)), (XOR_64((RSHIFT_64(t_819, 4bv64)), t_819)))))[1:0]));
SF := t_819[64:63];
ZF := bool2bv(0bv64 == t_819);

label_0xc01c:
if (bv2bool(ZF)) {
  goto label_0xc01f;
}

label_0xc01e:
assume false;

label_0xc01f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xc027:
origDEST_823 := RAX;
origCOUNT_824 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), CF, LSHIFT_64(origDEST_823, (MINUS_64(64bv64, origCOUNT_824)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_824 == 1bv64)), origDEST_823[64:63], unconstrained_272));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_824 == 0bv64)), AF, unconstrained_273);

label_0xc02b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc032:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc036:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xc03e:
origDEST_829 := RCX;
origCOUNT_830 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), CF, LSHIFT_64(origDEST_829, (MINUS_64(64bv64, origCOUNT_830)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_830 == 1bv64)), origDEST_829[64:63], unconstrained_274));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_830 == 0bv64)), AF, unconstrained_275);

label_0xc042:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_276;
SF := unconstrained_277;
AF := unconstrained_278;
PF := unconstrained_279;

label_0xc046:
if (bv2bool(CF)) {
  goto label_0xc049;
}

label_0xc048:
assume false;

label_0xc049:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xc051:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 700bv64)));

label_0xc058:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc05a:
goto label_0xb260;

label_0xc05f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc067:
t1_835 := RAX;
t2_836 := 16bv64;
RAX := PLUS_64(RAX, t2_836);
CF := bool2bv(LT_64(RAX, t1_835));
OF := AND_1((bool2bv((t1_835[64:63]) == (t2_836[64:63]))), (XOR_1((t1_835[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_835)), t2_836)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc06b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0xc073:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc07b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_280;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc081:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc086:
t_843 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_281;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_843, 4bv64)), t_843)), 2bv64)), (XOR_64((RSHIFT_64(t_843, 4bv64)), t_843)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_843, 4bv64)), t_843)), 2bv64)), (XOR_64((RSHIFT_64(t_843, 4bv64)), t_843)))))[1:0]));
SF := t_843[64:63];
ZF := bool2bv(0bv64 == t_843);

label_0xc089:
if (bv2bool(ZF)) {
  goto label_0xc08c;
}

label_0xc08b:
assume false;

label_0xc08c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc094:
origDEST_847 := RAX;
origCOUNT_848 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), CF, LSHIFT_64(origDEST_847, (MINUS_64(64bv64, origCOUNT_848)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_848 == 1bv64)), origDEST_847[64:63], unconstrained_282));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_848 == 0bv64)), AF, unconstrained_283);

label_0xc098:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc09f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc0a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc0ab:
origDEST_853 := RCX;
origCOUNT_854 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), CF, LSHIFT_64(origDEST_853, (MINUS_64(64bv64, origCOUNT_854)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_854 == 1bv64)), origDEST_853[64:63], unconstrained_284));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_854 == 0bv64)), AF, unconstrained_285);

label_0xc0af:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_286;
SF := unconstrained_287;
AF := unconstrained_288;
PF := unconstrained_289;

label_0xc0b3:
if (bv2bool(CF)) {
  goto label_0xc0b6;
}

label_0xc0b5:
assume false;

label_0xc0b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0xc0be:
mem := STORE_LE_32(mem, RAX, 3bv32);

label_0xc0c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc0cc:
t1_859 := RAX;
t2_860 := 1096bv64;
RAX := PLUS_64(RAX, t2_860);
CF := bool2bv(LT_64(RAX, t1_859));
OF := AND_1((bool2bv((t1_859[64:63]) == (t2_860[64:63]))), (XOR_1((t1_859[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_859)), t2_860)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc0d2:
RDX := RAX;

label_0xc0d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc0dd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xc0e0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 49381bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc0e5"} true;
call arbitrary_func();

label_0xc0e5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xc0e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc0f1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xc0f4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc0fc:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xc103:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xc107:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc10f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xc112:
origDEST_865 := RCX[32:0];
origCOUNT_866 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), CF, LSHIFT_32(origDEST_865, (MINUS_32(32bv32, origCOUNT_866)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_866 == 1bv32)), origDEST_865[32:31], unconstrained_290));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv32)), AF, unconstrained_291);

label_0xc114:
RCX := (0bv32 ++ RCX[32:0]);

label_0xc116:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc11e:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xc125:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xc129:
mem := STORE_LE_32(mem, PLUS_64(RSP, 704bv64), RCX[32:0]);

label_0xc130:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc138:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xc13b:
origDEST_871 := RDX[32:0];
origCOUNT_872 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), CF, RSHIFT_32(origDEST_871, (MINUS_32(32bv32, origCOUNT_872)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_872 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_292));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv32)), AF, unconstrained_293);

label_0xc13e:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_294;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xc141:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xc144:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 704bv64)));

label_0xc14b:
origDEST_879 := RDX[32:0];
origCOUNT_880 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), CF, LSHIFT_32(origDEST_879, (MINUS_32(32bv32, origCOUNT_880)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_880 == 1bv32)), origDEST_879[32:31], unconstrained_295));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_880 == 0bv32)), AF, unconstrained_296);

label_0xc14d:
RCX := (0bv32 ++ RDX[32:0]);

label_0xc14f:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_297;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xc152:
origDEST_887 := RCX[32:0];
origCOUNT_888 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), CF, RSHIFT_32(origDEST_887, (MINUS_32(32bv32, origCOUNT_888)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_888 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_298));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_888 == 0bv32)), AF, unconstrained_299);

label_0xc155:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_300;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc157:
mem := STORE_LE_32(mem, PLUS_64(RSP, 708bv64), RAX[32:0]);

label_0xc15e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc166:
t1_895 := RAX;
t2_896 := 60bv64;
RAX := PLUS_64(RAX, t2_896);
CF := bool2bv(LT_64(RAX, t1_895));
OF := AND_1((bool2bv((t1_895[64:63]) == (t2_896[64:63]))), (XOR_1((t1_895[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_895)), t2_896)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc16a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0xc172:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xc17a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_301;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc180:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc185:
t_903 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_302;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_903, 4bv64)), t_903)), 2bv64)), (XOR_64((RSHIFT_64(t_903, 4bv64)), t_903)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_903, 4bv64)), t_903)), 2bv64)), (XOR_64((RSHIFT_64(t_903, 4bv64)), t_903)))))[1:0]));
SF := t_903[64:63];
ZF := bool2bv(0bv64 == t_903);

label_0xc188:
if (bv2bool(ZF)) {
  goto label_0xc18b;
}

label_0xc18a:
assume false;

label_0xc18b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xc193:
origDEST_907 := RAX;
origCOUNT_908 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), CF, LSHIFT_64(origDEST_907, (MINUS_64(64bv64, origCOUNT_908)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_908 == 1bv64)), origDEST_907[64:63], unconstrained_303));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_908 == 0bv64)), AF, unconstrained_304);

label_0xc197:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc19e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc1a2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xc1aa:
origDEST_913 := RCX;
origCOUNT_914 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), CF, LSHIFT_64(origDEST_913, (MINUS_64(64bv64, origCOUNT_914)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_914 == 1bv64)), origDEST_913[64:63], unconstrained_305));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_914 == 0bv64)), AF, unconstrained_306);

label_0xc1ae:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_307;
SF := unconstrained_308;
AF := unconstrained_309;
PF := unconstrained_310;

label_0xc1b2:
if (bv2bool(CF)) {
  goto label_0xc1b5;
}

label_0xc1b4:
assume false;

label_0xc1b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0xc1bd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 708bv64)));

label_0xc1c4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc1c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc1ce:
t_919 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_919)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_919, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)), 2bv32)), (XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)), 2bv32)), (XOR_32((RSHIFT_32(t_919, 4bv32)), t_919)))))[1:0]));
SF := t_919[32:31];
ZF := bool2bv(0bv32 == t_919);

label_0xc1d2:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc357;
}

label_0xc1d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc1e0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xc1e4:
origDEST_923 := RAX;
origCOUNT_924 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), CF, RSHIFT_64(origDEST_923, (MINUS_64(64bv64, origCOUNT_924)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_924 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_311));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), AF, unconstrained_312);

label_0xc1e8:
RCX := PLUS_64((PLUS_64(0bv64, 49647bv64)), 0bv64)[64:0];

label_0xc1ef:
t1_929 := RCX;
t2_930 := RAX;
RCX := PLUS_64(RCX, t2_930);
CF := bool2bv(LT_64(RCX, t1_929));
OF := AND_1((bool2bv((t1_929[64:63]) == (t2_930[64:63]))), (XOR_1((t1_929[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_929)), t2_930)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xc1f2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 928bv64), RCX);

label_0xc1fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc202:
t1_935 := RAX;
t2_936 := 24bv64;
RAX := PLUS_64(RAX, t2_936);
CF := bool2bv(LT_64(RAX, t1_935));
OF := AND_1((bool2bv((t1_935[64:63]) == (t2_936[64:63]))), (XOR_1((t1_935[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_935)), t2_936)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc206:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0xc20e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xc216:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_313;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc21c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc221:
t_943 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_314;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_943, 4bv64)), t_943)), 2bv64)), (XOR_64((RSHIFT_64(t_943, 4bv64)), t_943)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_943, 4bv64)), t_943)), 2bv64)), (XOR_64((RSHIFT_64(t_943, 4bv64)), t_943)))))[1:0]));
SF := t_943[64:63];
ZF := bool2bv(0bv64 == t_943);

label_0xc224:
if (bv2bool(ZF)) {
  goto label_0xc227;
}

label_0xc226:
assume false;

label_0xc227:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xc22f:
origDEST_947 := RAX;
origCOUNT_948 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), CF, LSHIFT_64(origDEST_947, (MINUS_64(64bv64, origCOUNT_948)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_948 == 1bv64)), origDEST_947[64:63], unconstrained_315));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_948 == 0bv64)), AF, unconstrained_316);

label_0xc233:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc23a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc23e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xc246:
origDEST_953 := RCX;
origCOUNT_954 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), CF, LSHIFT_64(origDEST_953, (MINUS_64(64bv64, origCOUNT_954)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_954 == 1bv64)), origDEST_953[64:63], unconstrained_317));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_954 == 0bv64)), AF, unconstrained_318);

label_0xc24a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_319;
SF := unconstrained_320;
AF := unconstrained_321;
PF := unconstrained_322;

label_0xc24e:
if (bv2bool(CF)) {
  goto label_0xc251;
}

label_0xc250:
assume false;

label_0xc251:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0xc259:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 928bv64));

label_0xc261:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xc263:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc265:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc26d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xc270:
t_959 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_959[32:31]) == (1bv32[32:31]))), (XOR_1((t_959[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_959)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc272:
mem := STORE_LE_32(mem, PLUS_64(RSP, 712bv64), RAX[32:0]);

label_0xc279:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc281:
t1_963 := RAX;
t2_964 := 28bv64;
RAX := PLUS_64(RAX, t2_964);
CF := bool2bv(LT_64(RAX, t1_963));
OF := AND_1((bool2bv((t1_963[64:63]) == (t2_964[64:63]))), (XOR_1((t1_963[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_963)), t2_964)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc285:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0xc28d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xc295:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_323;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc29b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc2a0:
t_971 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_324;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_971, 4bv64)), t_971)), 2bv64)), (XOR_64((RSHIFT_64(t_971, 4bv64)), t_971)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_971, 4bv64)), t_971)), 2bv64)), (XOR_64((RSHIFT_64(t_971, 4bv64)), t_971)))))[1:0]));
SF := t_971[64:63];
ZF := bool2bv(0bv64 == t_971);

label_0xc2a3:
if (bv2bool(ZF)) {
  goto label_0xc2a6;
}

label_0xc2a5:
assume false;

label_0xc2a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xc2ae:
origDEST_975 := RAX;
origCOUNT_976 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), CF, LSHIFT_64(origDEST_975, (MINUS_64(64bv64, origCOUNT_976)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_976 == 1bv64)), origDEST_975[64:63], unconstrained_325));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_976 == 0bv64)), AF, unconstrained_326);

label_0xc2b2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc2b9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc2bd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xc2c5:
origDEST_981 := RCX;
origCOUNT_982 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), CF, LSHIFT_64(origDEST_981, (MINUS_64(64bv64, origCOUNT_982)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_982 == 1bv64)), origDEST_981[64:63], unconstrained_327));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_982 == 0bv64)), AF, unconstrained_328);

label_0xc2c9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_329;
SF := unconstrained_330;
AF := unconstrained_331;
PF := unconstrained_332;

label_0xc2cd:
if (bv2bool(CF)) {
  goto label_0xc2d0;
}

label_0xc2cf:
assume false;

label_0xc2d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0xc2d8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 712bv64)));

label_0xc2df:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc2e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc2e9:
t_987 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_987)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_987, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_987, 4bv32)), t_987)), 2bv32)), (XOR_32((RSHIFT_32(t_987, 4bv32)), t_987)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_987, 4bv32)), t_987)), 2bv32)), (XOR_32((RSHIFT_32(t_987, 4bv32)), t_987)))))[1:0]));
SF := t_987[32:31];
ZF := bool2bv(0bv32 == t_987);

label_0xc2f0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc357;
}

label_0xc2f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc2fa:
t1_991 := RAX;
t2_992 := 28bv64;
RAX := PLUS_64(RAX, t2_992);
CF := bool2bv(LT_64(RAX, t1_991));
OF := AND_1((bool2bv((t1_991[64:63]) == (t2_992[64:63]))), (XOR_1((t1_991[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_991)), t2_992)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc2fe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0xc306:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xc30e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_333;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc314:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc319:
t_999 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_334;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_999, 4bv64)), t_999)), 2bv64)), (XOR_64((RSHIFT_64(t_999, 4bv64)), t_999)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_999, 4bv64)), t_999)), 2bv64)), (XOR_64((RSHIFT_64(t_999, 4bv64)), t_999)))))[1:0]));
SF := t_999[64:63];
ZF := bool2bv(0bv64 == t_999);

label_0xc31c:
if (bv2bool(ZF)) {
  goto label_0xc31f;
}

label_0xc31e:
assume false;

label_0xc31f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xc327:
origDEST_1003 := RAX;
origCOUNT_1004 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), CF, LSHIFT_64(origDEST_1003, (MINUS_64(64bv64, origCOUNT_1004)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 1bv64)), origDEST_1003[64:63], unconstrained_335));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1004 == 0bv64)), AF, unconstrained_336);

label_0xc32b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc332:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc336:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xc33e:
origDEST_1009 := RCX;
origCOUNT_1010 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), CF, LSHIFT_64(origDEST_1009, (MINUS_64(64bv64, origCOUNT_1010)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 1bv64)), origDEST_1009[64:63], unconstrained_337));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1010 == 0bv64)), AF, unconstrained_338);

label_0xc342:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_339;
SF := unconstrained_340;
AF := unconstrained_341;
PF := unconstrained_342;

label_0xc346:
if (bv2bool(CF)) {
  goto label_0xc349;
}

label_0xc348:
assume false;

label_0xc349:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0xc351:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xc357:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc35f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xc362:
t_1015 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1015, 1bv32)), (XOR_32(t_1015, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1015)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc364:
mem := STORE_LE_32(mem, PLUS_64(RSP, 716bv64), RAX[32:0]);

label_0xc36b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc373:
t1_1019 := RAX;
t2_1020 := 24bv64;
RAX := PLUS_64(RAX, t2_1020);
CF := bool2bv(LT_64(RAX, t1_1019));
OF := AND_1((bool2bv((t1_1019[64:63]) == (t2_1020[64:63]))), (XOR_1((t1_1019[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1019)), t2_1020)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc377:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0xc37f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xc387:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_343;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc38d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc392:
t_1027 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_344;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1027, 4bv64)), t_1027)), 2bv64)), (XOR_64((RSHIFT_64(t_1027, 4bv64)), t_1027)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1027, 4bv64)), t_1027)), 2bv64)), (XOR_64((RSHIFT_64(t_1027, 4bv64)), t_1027)))))[1:0]));
SF := t_1027[64:63];
ZF := bool2bv(0bv64 == t_1027);

label_0xc395:
if (bv2bool(ZF)) {
  goto label_0xc398;
}

label_0xc397:
assume false;

label_0xc398:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xc3a0:
origDEST_1031 := RAX;
origCOUNT_1032 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), CF, LSHIFT_64(origDEST_1031, (MINUS_64(64bv64, origCOUNT_1032)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 1bv64)), origDEST_1031[64:63], unconstrained_345));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1032 == 0bv64)), AF, unconstrained_346);

label_0xc3a4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc3ab:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc3af:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xc3b7:
origDEST_1037 := RCX;
origCOUNT_1038 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), CF, LSHIFT_64(origDEST_1037, (MINUS_64(64bv64, origCOUNT_1038)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 1bv64)), origDEST_1037[64:63], unconstrained_347));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1038 == 0bv64)), AF, unconstrained_348);

label_0xc3bb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_349;
SF := unconstrained_350;
AF := unconstrained_351;
PF := unconstrained_352;

label_0xc3bf:
if (bv2bool(CF)) {
  goto label_0xc3c2;
}

label_0xc3c1:
assume false;

label_0xc3c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0xc3ca:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 716bv64)));

label_0xc3d1:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc3d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc3db:
t_1043 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1043)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1043, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1043, 4bv32)), t_1043)), 2bv32)), (XOR_32((RSHIFT_32(t_1043, 4bv32)), t_1043)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1043, 4bv32)), t_1043)), 2bv32)), (XOR_32((RSHIFT_32(t_1043, 4bv32)), t_1043)))))[1:0]));
SF := t_1043[32:31];
ZF := bool2bv(0bv32 == t_1043);

label_0xc3df:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc3eb;
}

label_0xc3e1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 1bv32);

label_0xc3e9:
goto label_0xc3f3;

label_0xc3eb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 0bv32);

label_0xc3f3:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xc3f8:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_353;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc3fc:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xc400:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc408:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xc40e:
t_1049 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1049[32:31]) == (1bv32[32:31]))), (XOR_1((t_1049[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1049)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc410:
mem := STORE_LE_32(mem, PLUS_64(RSP, 720bv64), RAX[32:0]);

label_0xc417:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc41f:
t1_1053 := RAX;
t2_1054 := 1092bv64;
RAX := PLUS_64(RAX, t2_1054);
CF := bool2bv(LT_64(RAX, t1_1053));
OF := AND_1((bool2bv((t1_1053[64:63]) == (t2_1054[64:63]))), (XOR_1((t1_1053[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1053)), t2_1054)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc425:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0xc42d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xc435:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_354;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc43b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc440:
t_1061 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_355;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1061, 4bv64)), t_1061)), 2bv64)), (XOR_64((RSHIFT_64(t_1061, 4bv64)), t_1061)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1061, 4bv64)), t_1061)), 2bv64)), (XOR_64((RSHIFT_64(t_1061, 4bv64)), t_1061)))))[1:0]));
SF := t_1061[64:63];
ZF := bool2bv(0bv64 == t_1061);

label_0xc443:
if (bv2bool(ZF)) {
  goto label_0xc446;
}

label_0xc445:
assume false;

label_0xc446:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xc44e:
origDEST_1065 := RAX;
origCOUNT_1066 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), CF, LSHIFT_64(origDEST_1065, (MINUS_64(64bv64, origCOUNT_1066)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 1bv64)), origDEST_1065[64:63], unconstrained_356));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1066 == 0bv64)), AF, unconstrained_357);

label_0xc452:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc459:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc45d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xc465:
origDEST_1071 := RCX;
origCOUNT_1072 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), CF, LSHIFT_64(origDEST_1071, (MINUS_64(64bv64, origCOUNT_1072)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 1bv64)), origDEST_1071[64:63], unconstrained_358));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), AF, unconstrained_359);

label_0xc469:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_360;
SF := unconstrained_361;
AF := unconstrained_362;
PF := unconstrained_363;

label_0xc46d:
if (bv2bool(CF)) {
  goto label_0xc470;
}

label_0xc46f:
assume false;

label_0xc470:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0xc478:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 720bv64)));

label_0xc47f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc481:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc489:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xc48f:
t_1077 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1077[32:31]) == (1bv32[32:31]))), (XOR_1((t_1077[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1077)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc491:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc499:
t_1081 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_1081)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1081, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1081, 4bv32)), t_1081)), 2bv32)), (XOR_32((RSHIFT_32(t_1081, 4bv32)), t_1081)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1081, 4bv32)), t_1081)), 2bv32)), (XOR_32((RSHIFT_32(t_1081, 4bv32)), t_1081)))))[1:0]));
SF := t_1081[32:31];
ZF := bool2bv(0bv32 == t_1081);

label_0xc49f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc4a6;
}

label_0xc4a1:
goto label_0xb260;

label_0xc4a6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xc4ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc4b3:
t_1085 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_1085)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1085, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1085, 4bv32)), t_1085)), 2bv32)), (XOR_32((RSHIFT_32(t_1085, 4bv32)), t_1085)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1085, 4bv32)), t_1085)), 2bv32)), (XOR_32((RSHIFT_32(t_1085, 4bv32)), t_1085)))))[1:0]));
SF := t_1085[32:31];
ZF := bool2bv(0bv32 == t_1085);

label_0xc4b6:
if (bv2bool(ZF)) {
  goto label_0xc531;
}

label_0xc4b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc4c0:
t1_1089 := RAX;
t2_1090 := 64bv64;
RAX := PLUS_64(RAX, t2_1090);
CF := bool2bv(LT_64(RAX, t1_1089));
OF := AND_1((bool2bv((t1_1089[64:63]) == (t2_1090[64:63]))), (XOR_1((t1_1089[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1089)), t2_1090)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc4c4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0xc4cc:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xc4d1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 724bv64), RAX[32:0]);

label_0xc4d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xc4e0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_364;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc4e6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc4eb:
t_1097 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_365;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1097, 4bv64)), t_1097)), 2bv64)), (XOR_64((RSHIFT_64(t_1097, 4bv64)), t_1097)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1097, 4bv64)), t_1097)), 2bv64)), (XOR_64((RSHIFT_64(t_1097, 4bv64)), t_1097)))))[1:0]));
SF := t_1097[64:63];
ZF := bool2bv(0bv64 == t_1097);

label_0xc4ee:
if (bv2bool(ZF)) {
  goto label_0xc4f1;
}

label_0xc4f0:
assume false;

label_0xc4f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xc4f9:
origDEST_1101 := RAX;
origCOUNT_1102 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), CF, LSHIFT_64(origDEST_1101, (MINUS_64(64bv64, origCOUNT_1102)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 1bv64)), origDEST_1101[64:63], unconstrained_366));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1102 == 0bv64)), AF, unconstrained_367);

label_0xc4fd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc504:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc508:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xc510:
origDEST_1107 := RCX;
origCOUNT_1108 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), CF, LSHIFT_64(origDEST_1107, (MINUS_64(64bv64, origCOUNT_1108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 1bv64)), origDEST_1107[64:63], unconstrained_368));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1108 == 0bv64)), AF, unconstrained_369);

label_0xc514:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_370;
SF := unconstrained_371;
AF := unconstrained_372;
PF := unconstrained_373;

label_0xc518:
if (bv2bool(CF)) {
  goto label_0xc51b;
}

label_0xc51a:
assume false;

label_0xc51b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0xc523:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 724bv64)));

label_0xc52a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc52c:
goto label_0xb260;

label_0xc531:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc539:
t1_1113 := RAX;
t2_1114 := 1096bv64;
RAX := PLUS_64(RAX, t2_1114);
CF := bool2bv(LT_64(RAX, t1_1113));
OF := AND_1((bool2bv((t1_1113[64:63]) == (t2_1114[64:63]))), (XOR_1((t1_1113[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1113)), t2_1114)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc53f:
RDX := RAX;

label_0xc542:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc54a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xc54d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 50514bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc552"} true;
call arbitrary_func();

label_0xc552:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xc556:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc55e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xc561:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc569:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xc570:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xc574:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc57c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xc57f:
origDEST_1119 := RCX[32:0];
origCOUNT_1120 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), CF, LSHIFT_32(origDEST_1119, (MINUS_32(32bv32, origCOUNT_1120)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 1bv32)), origDEST_1119[32:31], unconstrained_374));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1120 == 0bv32)), AF, unconstrained_375);

label_0xc581:
RCX := (0bv32 ++ RCX[32:0]);

label_0xc583:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc58b:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xc592:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xc596:
mem := STORE_LE_32(mem, PLUS_64(RSP, 728bv64), RCX[32:0]);

label_0xc59d:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc5a5:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xc5a8:
origDEST_1125 := RDX[32:0];
origCOUNT_1126 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), CF, RSHIFT_32(origDEST_1125, (MINUS_32(32bv32, origCOUNT_1126)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_376));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1126 == 0bv32)), AF, unconstrained_377);

label_0xc5ab:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_378;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xc5ae:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xc5b1:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 728bv64)));

label_0xc5b8:
origDEST_1133 := RDX[32:0];
origCOUNT_1134 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), CF, LSHIFT_32(origDEST_1133, (MINUS_32(32bv32, origCOUNT_1134)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 1bv32)), origDEST_1133[32:31], unconstrained_379));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1134 == 0bv32)), AF, unconstrained_380);

label_0xc5ba:
RCX := (0bv32 ++ RDX[32:0]);

label_0xc5bc:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_381;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xc5bf:
origDEST_1141 := RCX[32:0];
origCOUNT_1142 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), CF, RSHIFT_32(origDEST_1141, (MINUS_32(32bv32, origCOUNT_1142)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_382));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1142 == 0bv32)), AF, unconstrained_383);

label_0xc5c2:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_384;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc5c4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 732bv64), RAX[32:0]);

label_0xc5cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc5d3:
t1_1149 := RAX;
t2_1150 := 60bv64;
RAX := PLUS_64(RAX, t2_1150);
CF := bool2bv(LT_64(RAX, t1_1149));
OF := AND_1((bool2bv((t1_1149[64:63]) == (t2_1150[64:63]))), (XOR_1((t1_1149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1149)), t2_1150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc5d7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0xc5df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xc5e7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_385;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc5ed:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc5f2:
t_1157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_386;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)), 2bv64)), (XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)), 2bv64)), (XOR_64((RSHIFT_64(t_1157, 4bv64)), t_1157)))))[1:0]));
SF := t_1157[64:63];
ZF := bool2bv(0bv64 == t_1157);

label_0xc5f5:
if (bv2bool(ZF)) {
  goto label_0xc5f8;
}

label_0xc5f7:
assume false;

label_0xc5f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xc600:
origDEST_1161 := RAX;
origCOUNT_1162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), CF, LSHIFT_64(origDEST_1161, (MINUS_64(64bv64, origCOUNT_1162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 1bv64)), origDEST_1161[64:63], unconstrained_387));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1162 == 0bv64)), AF, unconstrained_388);

label_0xc604:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc60b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc60f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xc617:
origDEST_1167 := RCX;
origCOUNT_1168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), CF, LSHIFT_64(origDEST_1167, (MINUS_64(64bv64, origCOUNT_1168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 1bv64)), origDEST_1167[64:63], unconstrained_389));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), AF, unconstrained_390);

label_0xc61b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_391;
SF := unconstrained_392;
AF := unconstrained_393;
PF := unconstrained_394;

label_0xc61f:
if (bv2bool(CF)) {
  goto label_0xc622;
}

label_0xc621:
assume false;

label_0xc622:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0xc62a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 732bv64)));

label_0xc631:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc633:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc63b:
t_1173 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1173)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1173, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1173, 4bv32)), t_1173)), 2bv32)), (XOR_32((RSHIFT_32(t_1173, 4bv32)), t_1173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1173, 4bv32)), t_1173)), 2bv32)), (XOR_32((RSHIFT_32(t_1173, 4bv32)), t_1173)))))[1:0]));
SF := t_1173[32:31];
ZF := bool2bv(0bv32 == t_1173);

label_0xc63f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc7c4;
}

label_0xc645:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc64d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xc651:
origDEST_1177 := RAX;
origCOUNT_1178 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), CF, RSHIFT_64(origDEST_1177, (MINUS_64(64bv64, origCOUNT_1178)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_395));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1178 == 0bv64)), AF, unconstrained_396);

label_0xc655:
RCX := PLUS_64((PLUS_64(0bv64, 50780bv64)), 0bv64)[64:0];

label_0xc65c:
t1_1183 := RCX;
t2_1184 := RAX;
RCX := PLUS_64(RCX, t2_1184);
CF := bool2bv(LT_64(RCX, t1_1183));
OF := AND_1((bool2bv((t1_1183[64:63]) == (t2_1184[64:63]))), (XOR_1((t1_1183[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1183)), t2_1184)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xc65f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 936bv64), RCX);

label_0xc667:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc66f:
t1_1189 := RAX;
t2_1190 := 24bv64;
RAX := PLUS_64(RAX, t2_1190);
CF := bool2bv(LT_64(RAX, t1_1189));
OF := AND_1((bool2bv((t1_1189[64:63]) == (t2_1190[64:63]))), (XOR_1((t1_1189[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1189)), t2_1190)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc673:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0xc67b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xc683:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_397;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc689:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc68e:
t_1197 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_398;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1197, 4bv64)), t_1197)), 2bv64)), (XOR_64((RSHIFT_64(t_1197, 4bv64)), t_1197)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1197, 4bv64)), t_1197)), 2bv64)), (XOR_64((RSHIFT_64(t_1197, 4bv64)), t_1197)))))[1:0]));
SF := t_1197[64:63];
ZF := bool2bv(0bv64 == t_1197);

label_0xc691:
if (bv2bool(ZF)) {
  goto label_0xc694;
}

label_0xc693:
assume false;

label_0xc694:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xc69c:
origDEST_1201 := RAX;
origCOUNT_1202 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), CF, LSHIFT_64(origDEST_1201, (MINUS_64(64bv64, origCOUNT_1202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 1bv64)), origDEST_1201[64:63], unconstrained_399));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), AF, unconstrained_400);

label_0xc6a0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc6a7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc6ab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xc6b3:
origDEST_1207 := RCX;
origCOUNT_1208 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), CF, LSHIFT_64(origDEST_1207, (MINUS_64(64bv64, origCOUNT_1208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 1bv64)), origDEST_1207[64:63], unconstrained_401));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1208 == 0bv64)), AF, unconstrained_402);

label_0xc6b7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_403;
SF := unconstrained_404;
AF := unconstrained_405;
PF := unconstrained_406;

label_0xc6bb:
if (bv2bool(CF)) {
  goto label_0xc6be;
}

label_0xc6bd:
assume false;

label_0xc6be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0xc6c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 936bv64));

label_0xc6ce:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xc6d0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc6d2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc6da:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xc6dd:
t_1213 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1213[32:31]) == (1bv32[32:31]))), (XOR_1((t_1213[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1213)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc6df:
mem := STORE_LE_32(mem, PLUS_64(RSP, 736bv64), RAX[32:0]);

label_0xc6e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc6ee:
t1_1217 := RAX;
t2_1218 := 28bv64;
RAX := PLUS_64(RAX, t2_1218);
CF := bool2bv(LT_64(RAX, t1_1217));
OF := AND_1((bool2bv((t1_1217[64:63]) == (t2_1218[64:63]))), (XOR_1((t1_1217[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1217)), t2_1218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc6f2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0xc6fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc702:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_407;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc708:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc70d:
t_1225 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_408;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1225, 4bv64)), t_1225)), 2bv64)), (XOR_64((RSHIFT_64(t_1225, 4bv64)), t_1225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1225, 4bv64)), t_1225)), 2bv64)), (XOR_64((RSHIFT_64(t_1225, 4bv64)), t_1225)))))[1:0]));
SF := t_1225[64:63];
ZF := bool2bv(0bv64 == t_1225);

label_0xc710:
if (bv2bool(ZF)) {
  goto label_0xc713;
}

label_0xc712:
assume false;

label_0xc713:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc71b:
origDEST_1229 := RAX;
origCOUNT_1230 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), CF, LSHIFT_64(origDEST_1229, (MINUS_64(64bv64, origCOUNT_1230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 1bv64)), origDEST_1229[64:63], unconstrained_409));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1230 == 0bv64)), AF, unconstrained_410);

label_0xc71f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc726:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc72a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc732:
origDEST_1235 := RCX;
origCOUNT_1236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), CF, LSHIFT_64(origDEST_1235, (MINUS_64(64bv64, origCOUNT_1236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 1bv64)), origDEST_1235[64:63], unconstrained_411));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1236 == 0bv64)), AF, unconstrained_412);

label_0xc736:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_413;
SF := unconstrained_414;
AF := unconstrained_415;
PF := unconstrained_416;

label_0xc73a:
if (bv2bool(CF)) {
  goto label_0xc73d;
}

label_0xc73c:
assume false;

label_0xc73d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0xc745:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 736bv64)));

label_0xc74c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc74e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc756:
t_1241 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_1241)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1241, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1241, 4bv32)), t_1241)), 2bv32)), (XOR_32((RSHIFT_32(t_1241, 4bv32)), t_1241)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1241, 4bv32)), t_1241)), 2bv32)), (XOR_32((RSHIFT_32(t_1241, 4bv32)), t_1241)))))[1:0]));
SF := t_1241[32:31];
ZF := bool2bv(0bv32 == t_1241);

label_0xc75d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc7c4;
}

label_0xc75f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc767:
t1_1245 := RAX;
t2_1246 := 28bv64;
RAX := PLUS_64(RAX, t2_1246);
CF := bool2bv(LT_64(RAX, t1_1245));
OF := AND_1((bool2bv((t1_1245[64:63]) == (t2_1246[64:63]))), (XOR_1((t1_1245[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1245)), t2_1246)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc76b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0xc773:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc77b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_417;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc781:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc786:
t_1253 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_418;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1253, 4bv64)), t_1253)), 2bv64)), (XOR_64((RSHIFT_64(t_1253, 4bv64)), t_1253)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1253, 4bv64)), t_1253)), 2bv64)), (XOR_64((RSHIFT_64(t_1253, 4bv64)), t_1253)))))[1:0]));
SF := t_1253[64:63];
ZF := bool2bv(0bv64 == t_1253);

label_0xc789:
if (bv2bool(ZF)) {
  goto label_0xc78c;
}

label_0xc78b:
assume false;

label_0xc78c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc794:
origDEST_1257 := RAX;
origCOUNT_1258 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), CF, LSHIFT_64(origDEST_1257, (MINUS_64(64bv64, origCOUNT_1258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 1bv64)), origDEST_1257[64:63], unconstrained_419));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1258 == 0bv64)), AF, unconstrained_420);

label_0xc798:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc79f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc7a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc7ab:
origDEST_1263 := RCX;
origCOUNT_1264 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), CF, LSHIFT_64(origDEST_1263, (MINUS_64(64bv64, origCOUNT_1264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 1bv64)), origDEST_1263[64:63], unconstrained_421));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1264 == 0bv64)), AF, unconstrained_422);

label_0xc7af:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_423;
SF := unconstrained_424;
AF := unconstrained_425;
PF := unconstrained_426;

label_0xc7b3:
if (bv2bool(CF)) {
  goto label_0xc7b6;
}

label_0xc7b5:
assume false;

label_0xc7b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0xc7be:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xc7c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc7cc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xc7cf:
t_1269 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1269, 1bv32)), (XOR_32(t_1269, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1269)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc7d1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 740bv64), RAX[32:0]);

label_0xc7d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc7e0:
t1_1273 := RAX;
t2_1274 := 24bv64;
RAX := PLUS_64(RAX, t2_1274);
CF := bool2bv(LT_64(RAX, t1_1273));
OF := AND_1((bool2bv((t1_1273[64:63]) == (t2_1274[64:63]))), (XOR_1((t1_1273[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1273)), t2_1274)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc7e4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0xc7ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xc7f4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_427;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc7fa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc7ff:
t_1281 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_428;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1281, 4bv64)), t_1281)), 2bv64)), (XOR_64((RSHIFT_64(t_1281, 4bv64)), t_1281)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1281, 4bv64)), t_1281)), 2bv64)), (XOR_64((RSHIFT_64(t_1281, 4bv64)), t_1281)))))[1:0]));
SF := t_1281[64:63];
ZF := bool2bv(0bv64 == t_1281);

label_0xc802:
if (bv2bool(ZF)) {
  goto label_0xc805;
}

label_0xc804:
assume false;

label_0xc805:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xc80d:
origDEST_1285 := RAX;
origCOUNT_1286 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), CF, LSHIFT_64(origDEST_1285, (MINUS_64(64bv64, origCOUNT_1286)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 1bv64)), origDEST_1285[64:63], unconstrained_429));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1286 == 0bv64)), AF, unconstrained_430);

label_0xc811:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc818:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc81c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xc824:
origDEST_1291 := RCX;
origCOUNT_1292 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), CF, LSHIFT_64(origDEST_1291, (MINUS_64(64bv64, origCOUNT_1292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 1bv64)), origDEST_1291[64:63], unconstrained_431));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1292 == 0bv64)), AF, unconstrained_432);

label_0xc828:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_433;
SF := unconstrained_434;
AF := unconstrained_435;
PF := unconstrained_436;

label_0xc82c:
if (bv2bool(CF)) {
  goto label_0xc82f;
}

label_0xc82e:
assume false;

label_0xc82f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0xc837:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 740bv64)));

label_0xc83e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc840:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc848:
t_1297 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1297)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1297, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1297, 4bv32)), t_1297)), 2bv32)), (XOR_32((RSHIFT_32(t_1297, 4bv32)), t_1297)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1297, 4bv32)), t_1297)), 2bv32)), (XOR_32((RSHIFT_32(t_1297, 4bv32)), t_1297)))))[1:0]));
SF := t_1297[32:31];
ZF := bool2bv(0bv32 == t_1297);

label_0xc84c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc858;
}

label_0xc84e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 1bv32);

label_0xc856:
goto label_0xc860;

label_0xc858:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 0bv32);

label_0xc860:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xc865:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_437;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc869:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xc86d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc875:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xc87b:
t_1303 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1303[32:31]) == (1bv32[32:31]))), (XOR_1((t_1303[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1303)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc87d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 744bv64), RAX[32:0]);

label_0xc884:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc88c:
t1_1307 := RAX;
t2_1308 := 1092bv64;
RAX := PLUS_64(RAX, t2_1308);
CF := bool2bv(LT_64(RAX, t1_1307));
OF := AND_1((bool2bv((t1_1307[64:63]) == (t2_1308[64:63]))), (XOR_1((t1_1307[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1307)), t2_1308)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc892:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RAX);

label_0xc89a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xc8a2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_438;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc8a8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc8ad:
t_1315 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_439;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1315, 4bv64)), t_1315)), 2bv64)), (XOR_64((RSHIFT_64(t_1315, 4bv64)), t_1315)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1315, 4bv64)), t_1315)), 2bv64)), (XOR_64((RSHIFT_64(t_1315, 4bv64)), t_1315)))))[1:0]));
SF := t_1315[64:63];
ZF := bool2bv(0bv64 == t_1315);

label_0xc8b0:
if (bv2bool(ZF)) {
  goto label_0xc8b3;
}

label_0xc8b2:
assume false;

label_0xc8b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xc8bb:
origDEST_1319 := RAX;
origCOUNT_1320 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), CF, LSHIFT_64(origDEST_1319, (MINUS_64(64bv64, origCOUNT_1320)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 1bv64)), origDEST_1319[64:63], unconstrained_440));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1320 == 0bv64)), AF, unconstrained_441);

label_0xc8bf:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc8c6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc8ca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xc8d2:
origDEST_1325 := RCX;
origCOUNT_1326 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), CF, LSHIFT_64(origDEST_1325, (MINUS_64(64bv64, origCOUNT_1326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 1bv64)), origDEST_1325[64:63], unconstrained_442));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1326 == 0bv64)), AF, unconstrained_443);

label_0xc8d6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_444;
SF := unconstrained_445;
AF := unconstrained_446;
PF := unconstrained_447;

label_0xc8da:
if (bv2bool(CF)) {
  goto label_0xc8dd;
}

label_0xc8dc:
assume false;

label_0xc8dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0xc8e5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 744bv64)));

label_0xc8ec:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc8ee:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xc8f3:
t1_1331 := RAX[32:0];
t2_1332 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_1332));
CF := bool2bv(LT_32((RAX[32:0]), t1_1331));
OF := AND_1((bool2bv((t1_1331[32:31]) == (t2_1332[32:31]))), (XOR_1((t1_1331[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_1331)), t2_1332)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc8f6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 748bv64), RAX[32:0]);

label_0xc8fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc905:
t1_1337 := RAX;
t2_1338 := 16bv64;
RAX := PLUS_64(RAX, t2_1338);
CF := bool2bv(LT_64(RAX, t1_1337));
OF := AND_1((bool2bv((t1_1337[64:63]) == (t2_1338[64:63]))), (XOR_1((t1_1337[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1337)), t2_1338)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc909:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0xc911:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xc919:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_448;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc91f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc924:
t_1345 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_449;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1345, 4bv64)), t_1345)), 2bv64)), (XOR_64((RSHIFT_64(t_1345, 4bv64)), t_1345)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1345, 4bv64)), t_1345)), 2bv64)), (XOR_64((RSHIFT_64(t_1345, 4bv64)), t_1345)))))[1:0]));
SF := t_1345[64:63];
ZF := bool2bv(0bv64 == t_1345);

label_0xc927:
if (bv2bool(ZF)) {
  goto label_0xc92a;
}

label_0xc929:
assume false;

label_0xc92a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xc932:
origDEST_1349 := RAX;
origCOUNT_1350 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), CF, LSHIFT_64(origDEST_1349, (MINUS_64(64bv64, origCOUNT_1350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 1bv64)), origDEST_1349[64:63], unconstrained_450));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1350 == 0bv64)), AF, unconstrained_451);

label_0xc936:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc93d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc941:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xc949:
origDEST_1355 := RCX;
origCOUNT_1356 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), CF, LSHIFT_64(origDEST_1355, (MINUS_64(64bv64, origCOUNT_1356)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 1bv64)), origDEST_1355[64:63], unconstrained_452));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1356 == 0bv64)), AF, unconstrained_453);

label_0xc94d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_454;
SF := unconstrained_455;
AF := unconstrained_456;
PF := unconstrained_457;

label_0xc951:
if (bv2bool(CF)) {
  goto label_0xc954;
}

label_0xc953:
assume false;

label_0xc954:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0xc95c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 748bv64)));

label_0xc963:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc965:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc96d:
t1_1361 := RAX;
t2_1362 := 1096bv64;
RAX := PLUS_64(RAX, t2_1362);
CF := bool2bv(LT_64(RAX, t1_1361));
OF := AND_1((bool2bv((t1_1361[64:63]) == (t2_1362[64:63]))), (XOR_1((t1_1361[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1361)), t2_1362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc973:
RDX := RAX;

label_0xc976:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc97e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xc981:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 51590bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc986"} true;
call arbitrary_func();

label_0xc986:
mem := STORE_LE_32(mem, PLUS_64(RSP, 752bv64), RAX[32:0]);

label_0xc98d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc995:
t1_1367 := RAX;
t2_1368 := 64bv64;
RAX := PLUS_64(RAX, t2_1368);
CF := bool2bv(LT_64(RAX, t1_1367));
OF := AND_1((bool2bv((t1_1367[64:63]) == (t2_1368[64:63]))), (XOR_1((t1_1367[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1367)), t2_1368)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc999:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0xc9a1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc9a9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_458;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc9af:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xc9b4:
t_1375 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_459;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1375, 4bv64)), t_1375)), 2bv64)), (XOR_64((RSHIFT_64(t_1375, 4bv64)), t_1375)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1375, 4bv64)), t_1375)), 2bv64)), (XOR_64((RSHIFT_64(t_1375, 4bv64)), t_1375)))))[1:0]));
SF := t_1375[64:63];
ZF := bool2bv(0bv64 == t_1375);

label_0xc9b7:
if (bv2bool(ZF)) {
  goto label_0xc9ba;
}

label_0xc9b9:
assume false;

label_0xc9ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc9c2:
origDEST_1379 := RAX;
origCOUNT_1380 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), CF, LSHIFT_64(origDEST_1379, (MINUS_64(64bv64, origCOUNT_1380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 1bv64)), origDEST_1379[64:63], unconstrained_460));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1380 == 0bv64)), AF, unconstrained_461);

label_0xc9c6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc9cd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc9d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc9d9:
origDEST_1385 := RCX;
origCOUNT_1386 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), CF, LSHIFT_64(origDEST_1385, (MINUS_64(64bv64, origCOUNT_1386)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 1bv64)), origDEST_1385[64:63], unconstrained_462));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1386 == 0bv64)), AF, unconstrained_463);

label_0xc9dd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_464;
SF := unconstrained_465;
AF := unconstrained_466;
PF := unconstrained_467;

label_0xc9e1:
if (bv2bool(CF)) {
  goto label_0xc9e4;
}

label_0xc9e3:
assume false;

label_0xc9e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0xc9ec:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 752bv64)));

label_0xc9f3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc9f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xc9fd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xca00:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xca08:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xca0f:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xca13:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xca1b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xca1e:
origDEST_1391 := RCX[32:0];
origCOUNT_1392 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), CF, LSHIFT_32(origDEST_1391, (MINUS_32(32bv32, origCOUNT_1392)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 1bv32)), origDEST_1391[32:31], unconstrained_468));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1392 == 0bv32)), AF, unconstrained_469);

label_0xca20:
RCX := (0bv32 ++ RCX[32:0]);

label_0xca22:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xca2a:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xca31:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xca35:
mem := STORE_LE_32(mem, PLUS_64(RSP, 756bv64), RCX[32:0]);

label_0xca3c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xca44:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xca47:
origDEST_1397 := RDX[32:0];
origCOUNT_1398 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), CF, RSHIFT_32(origDEST_1397, (MINUS_32(32bv32, origCOUNT_1398)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_470));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1398 == 0bv32)), AF, unconstrained_471);

label_0xca4a:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_472;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xca4d:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xca50:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 756bv64)));

label_0xca57:
origDEST_1405 := RDX[32:0];
origCOUNT_1406 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), CF, LSHIFT_32(origDEST_1405, (MINUS_32(32bv32, origCOUNT_1406)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 1bv32)), origDEST_1405[32:31], unconstrained_473));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1406 == 0bv32)), AF, unconstrained_474);

label_0xca59:
RCX := (0bv32 ++ RDX[32:0]);

label_0xca5b:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_475;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xca5e:
origDEST_1413 := RCX[32:0];
origCOUNT_1414 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), CF, RSHIFT_32(origDEST_1413, (MINUS_32(32bv32, origCOUNT_1414)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_476));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1414 == 0bv32)), AF, unconstrained_477);

label_0xca61:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_478;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xca63:
mem := STORE_LE_32(mem, PLUS_64(RSP, 760bv64), RAX[32:0]);

label_0xca6a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xca72:
t1_1421 := RAX;
t2_1422 := 60bv64;
RAX := PLUS_64(RAX, t2_1422);
CF := bool2bv(LT_64(RAX, t1_1421));
OF := AND_1((bool2bv((t1_1421[64:63]) == (t2_1422[64:63]))), (XOR_1((t1_1421[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1421)), t2_1422)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xca76:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RAX);

label_0xca7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xca86:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_479;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xca8c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xca91:
t_1429 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_480;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1429, 4bv64)), t_1429)), 2bv64)), (XOR_64((RSHIFT_64(t_1429, 4bv64)), t_1429)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1429, 4bv64)), t_1429)), 2bv64)), (XOR_64((RSHIFT_64(t_1429, 4bv64)), t_1429)))))[1:0]));
SF := t_1429[64:63];
ZF := bool2bv(0bv64 == t_1429);

label_0xca94:
if (bv2bool(ZF)) {
  goto label_0xca97;
}

label_0xca96:
assume false;

label_0xca97:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xca9f:
origDEST_1433 := RAX;
origCOUNT_1434 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), CF, LSHIFT_64(origDEST_1433, (MINUS_64(64bv64, origCOUNT_1434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 1bv64)), origDEST_1433[64:63], unconstrained_481));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1434 == 0bv64)), AF, unconstrained_482);

label_0xcaa3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcaaa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcaae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xcab6:
origDEST_1439 := RCX;
origCOUNT_1440 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), CF, LSHIFT_64(origDEST_1439, (MINUS_64(64bv64, origCOUNT_1440)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 1bv64)), origDEST_1439[64:63], unconstrained_483));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1440 == 0bv64)), AF, unconstrained_484);

label_0xcaba:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_485;
SF := unconstrained_486;
AF := unconstrained_487;
PF := unconstrained_488;

label_0xcabe:
if (bv2bool(CF)) {
  goto label_0xcac1;
}

label_0xcac0:
assume false;

label_0xcac1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0xcac9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 760bv64)));

label_0xcad0:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcad2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcada:
t_1445 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1445)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1445, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1445, 4bv32)), t_1445)), 2bv32)), (XOR_32((RSHIFT_32(t_1445, 4bv32)), t_1445)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1445, 4bv32)), t_1445)), 2bv32)), (XOR_32((RSHIFT_32(t_1445, 4bv32)), t_1445)))))[1:0]));
SF := t_1445[32:31];
ZF := bool2bv(0bv32 == t_1445);

label_0xcade:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xcc63;
}

label_0xcae4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcaec:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)))));

label_0xcaf0:
origDEST_1449 := RAX;
origCOUNT_1450 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), CF, RSHIFT_64(origDEST_1449, (MINUS_64(64bv64, origCOUNT_1450)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_489));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1450 == 0bv64)), AF, unconstrained_490);

label_0xcaf4:
RCX := PLUS_64((PLUS_64(0bv64, 51963bv64)), 0bv64)[64:0];

label_0xcafb:
t1_1455 := RCX;
t2_1456 := RAX;
RCX := PLUS_64(RCX, t2_1456);
CF := bool2bv(LT_64(RCX, t1_1455));
OF := AND_1((bool2bv((t1_1455[64:63]) == (t2_1456[64:63]))), (XOR_1((t1_1455[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1455)), t2_1456)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xcafe:
mem := STORE_LE_64(mem, PLUS_64(RSP, 944bv64), RCX);

label_0xcb06:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcb0e:
t1_1461 := RAX;
t2_1462 := 24bv64;
RAX := PLUS_64(RAX, t2_1462);
CF := bool2bv(LT_64(RAX, t1_1461));
OF := AND_1((bool2bv((t1_1461[64:63]) == (t2_1462[64:63]))), (XOR_1((t1_1461[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1461)), t2_1462)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcb12:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0xcb1a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xcb22:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_491;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcb28:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcb2d:
t_1469 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_492;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)), 2bv64)), (XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)), 2bv64)), (XOR_64((RSHIFT_64(t_1469, 4bv64)), t_1469)))))[1:0]));
SF := t_1469[64:63];
ZF := bool2bv(0bv64 == t_1469);

label_0xcb30:
if (bv2bool(ZF)) {
  goto label_0xcb33;
}

label_0xcb32:
assume false;

label_0xcb33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xcb3b:
origDEST_1473 := RAX;
origCOUNT_1474 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), CF, LSHIFT_64(origDEST_1473, (MINUS_64(64bv64, origCOUNT_1474)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 1bv64)), origDEST_1473[64:63], unconstrained_493));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1474 == 0bv64)), AF, unconstrained_494);

label_0xcb3f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcb46:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcb4a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xcb52:
origDEST_1479 := RCX;
origCOUNT_1480 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), CF, LSHIFT_64(origDEST_1479, (MINUS_64(64bv64, origCOUNT_1480)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 1bv64)), origDEST_1479[64:63], unconstrained_495));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1480 == 0bv64)), AF, unconstrained_496);

label_0xcb56:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_497;
SF := unconstrained_498;
AF := unconstrained_499;
PF := unconstrained_500;

label_0xcb5a:
if (bv2bool(CF)) {
  goto label_0xcb5d;
}

label_0xcb5c:
assume false;

label_0xcb5d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0xcb65:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 944bv64));

label_0xcb6d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xcb6f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcb71:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcb79:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xcb7c:
t_1485 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1485[32:31]) == (1bv32[32:31]))), (XOR_1((t_1485[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1485)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcb7e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 764bv64), RAX[32:0]);

label_0xcb85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcb8d:
t1_1489 := RAX;
t2_1490 := 28bv64;
RAX := PLUS_64(RAX, t2_1490);
CF := bool2bv(LT_64(RAX, t1_1489));
OF := AND_1((bool2bv((t1_1489[64:63]) == (t2_1490[64:63]))), (XOR_1((t1_1489[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1489)), t2_1490)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcb91:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0xcb99:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xcba1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_501;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcba7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcbac:
t_1497 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_502;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1497, 4bv64)), t_1497)), 2bv64)), (XOR_64((RSHIFT_64(t_1497, 4bv64)), t_1497)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1497, 4bv64)), t_1497)), 2bv64)), (XOR_64((RSHIFT_64(t_1497, 4bv64)), t_1497)))))[1:0]));
SF := t_1497[64:63];
ZF := bool2bv(0bv64 == t_1497);

label_0xcbaf:
if (bv2bool(ZF)) {
  goto label_0xcbb2;
}

label_0xcbb1:
assume false;

label_0xcbb2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xcbba:
origDEST_1501 := RAX;
origCOUNT_1502 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), CF, LSHIFT_64(origDEST_1501, (MINUS_64(64bv64, origCOUNT_1502)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 1bv64)), origDEST_1501[64:63], unconstrained_503));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1502 == 0bv64)), AF, unconstrained_504);

label_0xcbbe:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcbc5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcbc9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xcbd1:
origDEST_1507 := RCX;
origCOUNT_1508 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), CF, LSHIFT_64(origDEST_1507, (MINUS_64(64bv64, origCOUNT_1508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 1bv64)), origDEST_1507[64:63], unconstrained_505));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1508 == 0bv64)), AF, unconstrained_506);

label_0xcbd5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_507;
SF := unconstrained_508;
AF := unconstrained_509;
PF := unconstrained_510;

label_0xcbd9:
if (bv2bool(CF)) {
  goto label_0xcbdc;
}

label_0xcbdb:
assume false;

label_0xcbdc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0xcbe4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 764bv64)));

label_0xcbeb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcbed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcbf5:
t_1513 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), 512bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))), t_1513)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1513, (LOAD_LE_32(mem, PLUS_64(RAX, 28bv64))))), 512bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1513, 4bv32)), t_1513)), 2bv32)), (XOR_32((RSHIFT_32(t_1513, 4bv32)), t_1513)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1513, 4bv32)), t_1513)), 2bv32)), (XOR_32((RSHIFT_32(t_1513, 4bv32)), t_1513)))))[1:0]));
SF := t_1513[32:31];
ZF := bool2bv(0bv32 == t_1513);

label_0xcbfc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xcc63;
}

label_0xcbfe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcc06:
t1_1517 := RAX;
t2_1518 := 28bv64;
RAX := PLUS_64(RAX, t2_1518);
CF := bool2bv(LT_64(RAX, t1_1517));
OF := AND_1((bool2bv((t1_1517[64:63]) == (t2_1518[64:63]))), (XOR_1((t1_1517[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1517)), t2_1518)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcc0a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0xcc12:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xcc1a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_511;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcc20:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcc25:
t_1525 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_512;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1525, 4bv64)), t_1525)), 2bv64)), (XOR_64((RSHIFT_64(t_1525, 4bv64)), t_1525)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1525, 4bv64)), t_1525)), 2bv64)), (XOR_64((RSHIFT_64(t_1525, 4bv64)), t_1525)))))[1:0]));
SF := t_1525[64:63];
ZF := bool2bv(0bv64 == t_1525);

label_0xcc28:
if (bv2bool(ZF)) {
  goto label_0xcc2b;
}

label_0xcc2a:
assume false;

label_0xcc2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xcc33:
origDEST_1529 := RAX;
origCOUNT_1530 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), CF, LSHIFT_64(origDEST_1529, (MINUS_64(64bv64, origCOUNT_1530)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 1bv64)), origDEST_1529[64:63], unconstrained_513));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1530 == 0bv64)), AF, unconstrained_514);

label_0xcc37:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcc3e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcc42:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xcc4a:
origDEST_1535 := RCX;
origCOUNT_1536 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), CF, LSHIFT_64(origDEST_1535, (MINUS_64(64bv64, origCOUNT_1536)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 1bv64)), origDEST_1535[64:63], unconstrained_515));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1536 == 0bv64)), AF, unconstrained_516);

label_0xcc4e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_517;
SF := unconstrained_518;
AF := unconstrained_519;
PF := unconstrained_520;

label_0xcc52:
if (bv2bool(CF)) {
  goto label_0xcc55;
}

label_0xcc54:
assume false;

label_0xcc55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0xcc5d:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0xcc63:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcc6b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 24bv64)));

label_0xcc6e:
t_1541 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1541, 1bv32)), (XOR_32(t_1541, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1541)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcc70:
mem := STORE_LE_32(mem, PLUS_64(RSP, 768bv64), RAX[32:0]);

label_0xcc77:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcc7f:
t1_1545 := RAX;
t2_1546 := 24bv64;
RAX := PLUS_64(RAX, t2_1546);
CF := bool2bv(LT_64(RAX, t1_1545));
OF := AND_1((bool2bv((t1_1545[64:63]) == (t2_1546[64:63]))), (XOR_1((t1_1545[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1545)), t2_1546)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcc83:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RAX);

label_0xcc8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xcc93:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_521;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcc99:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcc9e:
t_1553 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_522;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1553, 4bv64)), t_1553)), 2bv64)), (XOR_64((RSHIFT_64(t_1553, 4bv64)), t_1553)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1553, 4bv64)), t_1553)), 2bv64)), (XOR_64((RSHIFT_64(t_1553, 4bv64)), t_1553)))))[1:0]));
SF := t_1553[64:63];
ZF := bool2bv(0bv64 == t_1553);

label_0xcca1:
if (bv2bool(ZF)) {
  goto label_0xcca4;
}

label_0xcca3:
assume false;

label_0xcca4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xccac:
origDEST_1557 := RAX;
origCOUNT_1558 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), CF, LSHIFT_64(origDEST_1557, (MINUS_64(64bv64, origCOUNT_1558)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 1bv64)), origDEST_1557[64:63], unconstrained_523));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1558 == 0bv64)), AF, unconstrained_524);

label_0xccb0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xccb7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xccbb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xccc3:
origDEST_1563 := RCX;
origCOUNT_1564 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), CF, LSHIFT_64(origDEST_1563, (MINUS_64(64bv64, origCOUNT_1564)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 1bv64)), origDEST_1563[64:63], unconstrained_525));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1564 == 0bv64)), AF, unconstrained_526);

label_0xccc7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_527;
SF := unconstrained_528;
AF := unconstrained_529;
PF := unconstrained_530;

label_0xcccb:
if (bv2bool(CF)) {
  goto label_0xccce;
}

label_0xcccd:
assume false;

label_0xccce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0xccd6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 768bv64)));

label_0xccdd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xccdf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcce7:
t_1569 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_1569)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1569, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1569, 4bv32)), t_1569)), 2bv32)), (XOR_32((RSHIFT_32(t_1569, 4bv32)), t_1569)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1569, 4bv32)), t_1569)), 2bv32)), (XOR_32((RSHIFT_32(t_1569, 4bv32)), t_1569)))))[1:0]));
SF := t_1569[32:31];
ZF := bool2bv(0bv32 == t_1569);

label_0xcceb:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xccf7;
}

label_0xcced:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 1bv32);

label_0xccf5:
goto label_0xccff;

label_0xccf7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 0bv32);

label_0xccff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcd07:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0xcd0b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64bv64)));

label_0xcd0e:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_531;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcd10:
mem := STORE_LE_32(mem, PLUS_64(RSP, 772bv64), RAX[32:0]);

label_0xcd17:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcd1f:
t1_1575 := RAX;
t2_1576 := 64bv64;
RAX := PLUS_64(RAX, t2_1576);
CF := bool2bv(LT_64(RAX, t1_1575));
OF := AND_1((bool2bv((t1_1575[64:63]) == (t2_1576[64:63]))), (XOR_1((t1_1575[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1575)), t2_1576)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcd23:
mem := STORE_LE_64(mem, PLUS_64(RSP, 320bv64), RAX);

label_0xcd2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xcd33:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_532;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcd39:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcd3e:
t_1583 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_533;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1583, 4bv64)), t_1583)), 2bv64)), (XOR_64((RSHIFT_64(t_1583, 4bv64)), t_1583)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1583, 4bv64)), t_1583)), 2bv64)), (XOR_64((RSHIFT_64(t_1583, 4bv64)), t_1583)))))[1:0]));
SF := t_1583[64:63];
ZF := bool2bv(0bv64 == t_1583);

label_0xcd41:
if (bv2bool(ZF)) {
  goto label_0xcd44;
}

label_0xcd43:
assume false;

label_0xcd44:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xcd4c:
origDEST_1587 := RAX;
origCOUNT_1588 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), CF, LSHIFT_64(origDEST_1587, (MINUS_64(64bv64, origCOUNT_1588)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 1bv64)), origDEST_1587[64:63], unconstrained_534));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1588 == 0bv64)), AF, unconstrained_535);

label_0xcd50:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcd57:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcd5b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xcd63:
origDEST_1593 := RCX;
origCOUNT_1594 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), CF, LSHIFT_64(origDEST_1593, (MINUS_64(64bv64, origCOUNT_1594)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 1bv64)), origDEST_1593[64:63], unconstrained_536));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1594 == 0bv64)), AF, unconstrained_537);

label_0xcd67:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_538;
SF := unconstrained_539;
AF := unconstrained_540;
PF := unconstrained_541;

label_0xcd6b:
if (bv2bool(CF)) {
  goto label_0xcd6e;
}

label_0xcd6d:
assume false;

label_0xcd6e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0xcd76:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 772bv64)));

label_0xcd7d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcd7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcd87:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xcd8d:
t_1599 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1599[32:31]) == (1bv32[32:31]))), (XOR_1((t_1599[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1599)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcd8f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 776bv64), RAX[32:0]);

label_0xcd96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcd9e:
t1_1603 := RAX;
t2_1604 := 1092bv64;
RAX := PLUS_64(RAX, t2_1604);
CF := bool2bv(LT_64(RAX, t1_1603));
OF := AND_1((bool2bv((t1_1603[64:63]) == (t2_1604[64:63]))), (XOR_1((t1_1603[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1603)), t2_1604)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcda4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 328bv64), RAX);

label_0xcdac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xcdb4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_542;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcdba:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcdbf:
t_1611 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_543;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1611, 4bv64)), t_1611)), 2bv64)), (XOR_64((RSHIFT_64(t_1611, 4bv64)), t_1611)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1611, 4bv64)), t_1611)), 2bv64)), (XOR_64((RSHIFT_64(t_1611, 4bv64)), t_1611)))))[1:0]));
SF := t_1611[64:63];
ZF := bool2bv(0bv64 == t_1611);

label_0xcdc2:
if (bv2bool(ZF)) {
  goto label_0xcdc5;
}

label_0xcdc4:
assume false;

label_0xcdc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xcdcd:
origDEST_1615 := RAX;
origCOUNT_1616 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), CF, LSHIFT_64(origDEST_1615, (MINUS_64(64bv64, origCOUNT_1616)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 1bv64)), origDEST_1615[64:63], unconstrained_544));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1616 == 0bv64)), AF, unconstrained_545);

label_0xcdd1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcdd8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcddc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xcde4:
origDEST_1621 := RCX;
origCOUNT_1622 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), CF, LSHIFT_64(origDEST_1621, (MINUS_64(64bv64, origCOUNT_1622)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 1bv64)), origDEST_1621[64:63], unconstrained_546));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1622 == 0bv64)), AF, unconstrained_547);

label_0xcde8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_548;
SF := unconstrained_549;
AF := unconstrained_550;
PF := unconstrained_551;

label_0xcdec:
if (bv2bool(CF)) {
  goto label_0xcdef;
}

label_0xcdee:
assume false;

label_0xcdef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0xcdf7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 776bv64)));

label_0xcdfe:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xce00:
goto label_0xb260;

label_0xce05:
goto label_0xdea1;

label_0xce0a:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_552;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xce0c:
t_1627 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_1627)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1627, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1627, 4bv32)), t_1627)), 2bv32)), (XOR_32((RSHIFT_32(t_1627, 4bv32)), t_1627)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1627, 4bv32)), t_1627)), 2bv32)), (XOR_32((RSHIFT_32(t_1627, 4bv32)), t_1627)))))[1:0]));
SF := t_1627[32:31];
ZF := bool2bv(0bv32 == t_1627);

label_0xce0f:
if (bv2bool(ZF)) {
  goto label_0xdea1;
}

label_0xce15:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_553;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xce17:
t_1631 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_1631)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1631, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1631, 4bv32)), t_1631)), 2bv32)), (XOR_32((RSHIFT_32(t_1631, 4bv32)), t_1631)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1631, 4bv32)), t_1631)), 2bv32)), (XOR_32((RSHIFT_32(t_1631, 4bv32)), t_1631)))))[1:0]));
SF := t_1631[32:31];
ZF := bool2bv(0bv32 == t_1631);

label_0xce1a:
if (bv2bool(ZF)) {
  goto label_0xd21e;
}

label_0xce20:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xce28:
RAX := LOAD_LE_64(mem, RAX);

label_0xce2b:
t_1635 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))), t_1635)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1635, (LOAD_LE_32(mem, PLUS_64(RAX, 32bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1635, 4bv32)), t_1635)), 2bv32)), (XOR_32((RSHIFT_32(t_1635, 4bv32)), t_1635)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1635, 4bv32)), t_1635)), 2bv32)), (XOR_32((RSHIFT_32(t_1635, 4bv32)), t_1635)))))[1:0]));
SF := t_1635[32:31];
ZF := bool2bv(0bv32 == t_1635);

label_0xce2f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xce38;
}

label_0xce31:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_554;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xce33:
goto label_0xdea1;

label_0xce38:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xce40:
t_1639 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_1639)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1639, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1639, 4bv32)), t_1639)), 2bv32)), (XOR_32((RSHIFT_32(t_1639, 4bv32)), t_1639)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1639, 4bv32)), t_1639)), 2bv32)), (XOR_32((RSHIFT_32(t_1639, 4bv32)), t_1639)))))[1:0]));
SF := t_1639[32:31];
ZF := bool2bv(0bv32 == t_1639);

label_0xce44:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xce4b;
}

label_0xce46:
goto label_0xd21e;

label_0xce4b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xce53:
t1_1643 := RAX;
t2_1644 := 12bv64;
RAX := PLUS_64(RAX, t2_1644);
CF := bool2bv(LT_64(RAX, t1_1643));
OF := AND_1((bool2bv((t1_1643[64:63]) == (t2_1644[64:63]))), (XOR_1((t1_1643[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1643)), t2_1644)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xce57:
mem := STORE_LE_64(mem, PLUS_64(RSP, 952bv64), RAX);

label_0xce5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xce67:
RAX := LOAD_LE_64(mem, RAX);

label_0xce6a:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0xce6e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RAX);

label_0xce76:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xce7e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_555;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xce84:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xce89:
t_1651 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_556;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)), 2bv64)), (XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)), 2bv64)), (XOR_64((RSHIFT_64(t_1651, 4bv64)), t_1651)))))[1:0]));
SF := t_1651[64:63];
ZF := bool2bv(0bv64 == t_1651);

label_0xce8c:
if (bv2bool(ZF)) {
  goto label_0xce8f;
}

label_0xce8e:
assume false;

label_0xce8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xce97:
origDEST_1655 := RAX;
origCOUNT_1656 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), CF, LSHIFT_64(origDEST_1655, (MINUS_64(64bv64, origCOUNT_1656)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 1bv64)), origDEST_1655[64:63], unconstrained_557));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1656 == 0bv64)), AF, unconstrained_558);

label_0xce9b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcea2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcea6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xceae:
origDEST_1661 := RCX;
origCOUNT_1662 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), CF, LSHIFT_64(origDEST_1661, (MINUS_64(64bv64, origCOUNT_1662)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 1bv64)), origDEST_1661[64:63], unconstrained_559));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1662 == 0bv64)), AF, unconstrained_560);

label_0xceb2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_561;
SF := unconstrained_562;
AF := unconstrained_563;
PF := unconstrained_564;

label_0xceb6:
if (bv2bool(CF)) {
  goto label_0xceb9;
}

label_0xceb8:
assume false;

label_0xceb9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0xcec1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 952bv64));

label_0xcec9:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0xcecc:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xcece:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xced6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64)));

label_0xcedc:
origDEST_1667 := RAX[32:0];
origCOUNT_1668 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), CF, RSHIFT_32(origDEST_1667, (MINUS_32(32bv32, origCOUNT_1668)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_565));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1668 == 0bv32)), AF, unconstrained_566);

label_0xcedf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcee7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3184bv64)));

label_0xceed:
origDEST_1673 := RCX[32:0];
origCOUNT_1674 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), CF, LSHIFT_32(origDEST_1673, (MINUS_32(32bv32, origCOUNT_1674)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 1bv32)), origDEST_1673[32:31], unconstrained_567));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1674 == 0bv32)), AF, unconstrained_568);

label_0xcef0:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcef8:
RDX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, 12bv64))));

label_0xcefc:
RCX := (0bv32 ++ XOR_32((RCX[32:0]), (RDX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_569;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xcefe:
RCX := (0bv32 ++ RCX[32:0]);

label_0xcf00:
RDX := PLUS_64((PLUS_64(0bv64, 52999bv64)), 0bv64)[64:0];

label_0xcf07:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_570;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcf0a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 780bv64), RAX[32:0]);

label_0xcf11:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcf19:
t1_1683 := RAX;
t2_1684 := 3184bv64;
RAX := PLUS_64(RAX, t2_1684);
CF := bool2bv(LT_64(RAX, t1_1683));
OF := AND_1((bool2bv((t1_1683[64:63]) == (t2_1684[64:63]))), (XOR_1((t1_1683[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1683)), t2_1684)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcf1f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 344bv64), RAX);

label_0xcf27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xcf2f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_571;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcf35:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcf3a:
t_1691 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_572;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1691, 4bv64)), t_1691)), 2bv64)), (XOR_64((RSHIFT_64(t_1691, 4bv64)), t_1691)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1691, 4bv64)), t_1691)), 2bv64)), (XOR_64((RSHIFT_64(t_1691, 4bv64)), t_1691)))))[1:0]));
SF := t_1691[64:63];
ZF := bool2bv(0bv64 == t_1691);

label_0xcf3d:
if (bv2bool(ZF)) {
  goto label_0xcf40;
}

label_0xcf3f:
assume false;

label_0xcf40:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xcf48:
origDEST_1695 := RAX;
origCOUNT_1696 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), CF, LSHIFT_64(origDEST_1695, (MINUS_64(64bv64, origCOUNT_1696)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 1bv64)), origDEST_1695[64:63], unconstrained_573));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1696 == 0bv64)), AF, unconstrained_574);

label_0xcf4c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcf53:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcf57:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xcf5f:
origDEST_1701 := RCX;
origCOUNT_1702 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), CF, LSHIFT_64(origDEST_1701, (MINUS_64(64bv64, origCOUNT_1702)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 1bv64)), origDEST_1701[64:63], unconstrained_575));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1702 == 0bv64)), AF, unconstrained_576);

label_0xcf63:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_577;
SF := unconstrained_578;
AF := unconstrained_579;
PF := unconstrained_580;

label_0xcf67:
if (bv2bool(CF)) {
  goto label_0xcf6a;
}

label_0xcf69:
assume false;

label_0xcf6a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0xcf72:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 780bv64)));

label_0xcf79:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcf7b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcf83:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0xcf86:
t_1707 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1707, 1bv32)), (XOR_32(t_1707, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1707)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xcf88:
mem := STORE_LE_32(mem, PLUS_64(RSP, 784bv64), RAX[32:0]);

label_0xcf8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcf97:
t1_1711 := RAX;
t2_1712 := 16bv64;
RAX := PLUS_64(RAX, t2_1712);
CF := bool2bv(LT_64(RAX, t1_1711));
OF := AND_1((bool2bv((t1_1711[64:63]) == (t2_1712[64:63]))), (XOR_1((t1_1711[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1711)), t2_1712)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcf9b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RAX);

label_0xcfa3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0xcfab:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_581;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcfb1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcfb6:
t_1719 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_582;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1719, 4bv64)), t_1719)), 2bv64)), (XOR_64((RSHIFT_64(t_1719, 4bv64)), t_1719)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1719, 4bv64)), t_1719)), 2bv64)), (XOR_64((RSHIFT_64(t_1719, 4bv64)), t_1719)))))[1:0]));
SF := t_1719[64:63];
ZF := bool2bv(0bv64 == t_1719);

label_0xcfb9:
if (bv2bool(ZF)) {
  goto label_0xcfbc;
}

label_0xcfbb:
assume false;

label_0xcfbc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0xcfc4:
origDEST_1723 := RAX;
origCOUNT_1724 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), CF, LSHIFT_64(origDEST_1723, (MINUS_64(64bv64, origCOUNT_1724)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 1bv64)), origDEST_1723[64:63], unconstrained_583));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1724 == 0bv64)), AF, unconstrained_584);

label_0xcfc8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcfcf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcfd3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0xcfdb:
origDEST_1729 := RCX;
origCOUNT_1730 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), CF, LSHIFT_64(origDEST_1729, (MINUS_64(64bv64, origCOUNT_1730)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 1bv64)), origDEST_1729[64:63], unconstrained_585));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1730 == 0bv64)), AF, unconstrained_586);

label_0xcfdf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_587;
SF := unconstrained_588;
AF := unconstrained_589;
PF := unconstrained_590;

label_0xcfe3:
if (bv2bool(CF)) {
  goto label_0xcfe6;
}

label_0xcfe5:
assume false;

label_0xcfe6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0xcfee:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 784bv64)));

label_0xcff5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xcff7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xcfff:
RAX := LOAD_LE_64(mem, RAX);

label_0xd002:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 24bv64));

label_0xd006:
t_1735 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_1735[64:63]) == (1bv64[64:63]))), (XOR_1((t_1735[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_1735)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd009:
mem := STORE_LE_64(mem, PLUS_64(RSP, 960bv64), RAX);

label_0xd011:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd019:
RAX := LOAD_LE_64(mem, RAX);

label_0xd01c:
t1_1739 := RAX;
t2_1740 := 24bv64;
RAX := PLUS_64(RAX, t2_1740);
CF := bool2bv(LT_64(RAX, t1_1739));
OF := AND_1((bool2bv((t1_1739[64:63]) == (t2_1740[64:63]))), (XOR_1((t1_1739[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1739)), t2_1740)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd020:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0xd028:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0xd030:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_591;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd036:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd03b:
t_1747 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_592;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1747, 4bv64)), t_1747)), 2bv64)), (XOR_64((RSHIFT_64(t_1747, 4bv64)), t_1747)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1747, 4bv64)), t_1747)), 2bv64)), (XOR_64((RSHIFT_64(t_1747, 4bv64)), t_1747)))))[1:0]));
SF := t_1747[64:63];
ZF := bool2bv(0bv64 == t_1747);

label_0xd03e:
if (bv2bool(ZF)) {
  goto label_0xd041;
}

label_0xd040:
assume false;

label_0xd041:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0xd049:
origDEST_1751 := RAX;
origCOUNT_1752 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), CF, LSHIFT_64(origDEST_1751, (MINUS_64(64bv64, origCOUNT_1752)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 1bv64)), origDEST_1751[64:63], unconstrained_593));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1752 == 0bv64)), AF, unconstrained_594);

label_0xd04d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd054:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd058:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0xd060:
origDEST_1757 := RCX;
origCOUNT_1758 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), CF, LSHIFT_64(origDEST_1757, (MINUS_64(64bv64, origCOUNT_1758)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 1bv64)), origDEST_1757[64:63], unconstrained_595));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1758 == 0bv64)), AF, unconstrained_596);

label_0xd064:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_597;
SF := unconstrained_598;
AF := unconstrained_599;
PF := unconstrained_600;

label_0xd068:
if (bv2bool(CF)) {
  goto label_0xd06b;
}

label_0xd06a:
assume false;

label_0xd06b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0xd073:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 960bv64));

label_0xd07b:
mem := STORE_LE_64(mem, RAX, RCX);

label_0xd07e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd086:
RAX := LOAD_LE_64(mem, RAX);

label_0xd089:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0xd08c:
t_1763 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1763, 1bv32)), (XOR_32(t_1763, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1763)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd08e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 788bv64), RAX[32:0]);

label_0xd095:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd09d:
RAX := LOAD_LE_64(mem, RAX);

label_0xd0a0:
t1_1767 := RAX;
t2_1768 := 32bv64;
RAX := PLUS_64(RAX, t2_1768);
CF := bool2bv(LT_64(RAX, t1_1767));
OF := AND_1((bool2bv((t1_1767[64:63]) == (t2_1768[64:63]))), (XOR_1((t1_1767[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1767)), t2_1768)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd0a4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RAX);

label_0xd0ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xd0b4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_601;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd0ba:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd0bf:
t_1775 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_602;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1775, 4bv64)), t_1775)), 2bv64)), (XOR_64((RSHIFT_64(t_1775, 4bv64)), t_1775)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1775, 4bv64)), t_1775)), 2bv64)), (XOR_64((RSHIFT_64(t_1775, 4bv64)), t_1775)))))[1:0]));
SF := t_1775[64:63];
ZF := bool2bv(0bv64 == t_1775);

label_0xd0c2:
if (bv2bool(ZF)) {
  goto label_0xd0c5;
}

label_0xd0c4:
assume false;

label_0xd0c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xd0cd:
origDEST_1779 := RAX;
origCOUNT_1780 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), CF, LSHIFT_64(origDEST_1779, (MINUS_64(64bv64, origCOUNT_1780)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 1bv64)), origDEST_1779[64:63], unconstrained_603));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1780 == 0bv64)), AF, unconstrained_604);

label_0xd0d1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd0d8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd0dc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xd0e4:
origDEST_1785 := RCX;
origCOUNT_1786 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), CF, LSHIFT_64(origDEST_1785, (MINUS_64(64bv64, origCOUNT_1786)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 1bv64)), origDEST_1785[64:63], unconstrained_605));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1786 == 0bv64)), AF, unconstrained_606);

label_0xd0e8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_607;
SF := unconstrained_608;
AF := unconstrained_609;
PF := unconstrained_610;

label_0xd0ec:
if (bv2bool(CF)) {
  goto label_0xd0ef;
}

label_0xd0ee:
assume false;

label_0xd0ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0xd0f7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 788bv64)));

label_0xd0fe:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd100:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd108:
RAX := LOAD_LE_64(mem, RAX);

label_0xd10b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 36bv64)));

label_0xd10e:
t_1791 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1791[32:31]) == (1bv32[32:31]))), (XOR_1((t_1791[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1791)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd110:
mem := STORE_LE_32(mem, PLUS_64(RSP, 792bv64), RAX[32:0]);

label_0xd117:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd11f:
RAX := LOAD_LE_64(mem, RAX);

label_0xd122:
t1_1795 := RAX;
t2_1796 := 36bv64;
RAX := PLUS_64(RAX, t2_1796);
CF := bool2bv(LT_64(RAX, t1_1795));
OF := AND_1((bool2bv((t1_1795[64:63]) == (t2_1796[64:63]))), (XOR_1((t1_1795[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1795)), t2_1796)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd126:
mem := STORE_LE_64(mem, PLUS_64(RSP, 376bv64), RAX);

label_0xd12e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xd136:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_611;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd13c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd141:
t_1803 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_612;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1803, 4bv64)), t_1803)), 2bv64)), (XOR_64((RSHIFT_64(t_1803, 4bv64)), t_1803)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1803, 4bv64)), t_1803)), 2bv64)), (XOR_64((RSHIFT_64(t_1803, 4bv64)), t_1803)))))[1:0]));
SF := t_1803[64:63];
ZF := bool2bv(0bv64 == t_1803);

label_0xd144:
if (bv2bool(ZF)) {
  goto label_0xd147;
}

label_0xd146:
assume false;

label_0xd147:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xd14f:
origDEST_1807 := RAX;
origCOUNT_1808 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), CF, LSHIFT_64(origDEST_1807, (MINUS_64(64bv64, origCOUNT_1808)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 1bv64)), origDEST_1807[64:63], unconstrained_613));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1808 == 0bv64)), AF, unconstrained_614);

label_0xd153:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd15a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd15e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xd166:
origDEST_1813 := RCX;
origCOUNT_1814 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), CF, LSHIFT_64(origDEST_1813, (MINUS_64(64bv64, origCOUNT_1814)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 1bv64)), origDEST_1813[64:63], unconstrained_615));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1814 == 0bv64)), AF, unconstrained_616);

label_0xd16a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_617;
SF := unconstrained_618;
AF := unconstrained_619;
PF := unconstrained_620;

label_0xd16e:
if (bv2bool(CF)) {
  goto label_0xd171;
}

label_0xd170:
assume false;

label_0xd171:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0xd179:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 792bv64)));

label_0xd180:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd182:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd18a:
RAX := LOAD_LE_64(mem, RAX);

label_0xd18d:
t_1819 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))), t_1819)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1819, (LOAD_LE_32(mem, PLUS_64(RAX, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1819, 4bv32)), t_1819)), 2bv32)), (XOR_32((RSHIFT_32(t_1819, 4bv32)), t_1819)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1819, 4bv32)), t_1819)), 2bv32)), (XOR_32((RSHIFT_32(t_1819, 4bv32)), t_1819)))))[1:0]));
SF := t_1819[32:31];
ZF := bool2bv(0bv32 == t_1819);

label_0xd191:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xd219;
}

label_0xd197:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd19f:
RAX := LOAD_LE_64(mem, RAX);

label_0xd1a2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 40bv64)));

label_0xd1a5:
t_1823 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1823[32:31]) == (1bv32[32:31]))), (XOR_1((t_1823[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1823)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd1a7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 796bv64), RAX[32:0]);

label_0xd1ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd1b6:
RAX := LOAD_LE_64(mem, RAX);

label_0xd1b9:
t1_1827 := RAX;
t2_1828 := 40bv64;
RAX := PLUS_64(RAX, t2_1828);
CF := bool2bv(LT_64(RAX, t1_1827));
OF := AND_1((bool2bv((t1_1827[64:63]) == (t2_1828[64:63]))), (XOR_1((t1_1827[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1827)), t2_1828)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd1bd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 384bv64), RAX);

label_0xd1c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0xd1cd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_621;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd1d3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd1d8:
t_1835 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_622;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1835, 4bv64)), t_1835)), 2bv64)), (XOR_64((RSHIFT_64(t_1835, 4bv64)), t_1835)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1835, 4bv64)), t_1835)), 2bv64)), (XOR_64((RSHIFT_64(t_1835, 4bv64)), t_1835)))))[1:0]));
SF := t_1835[64:63];
ZF := bool2bv(0bv64 == t_1835);

label_0xd1db:
if (bv2bool(ZF)) {
  goto label_0xd1de;
}

label_0xd1dd:
assume false;

label_0xd1de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0xd1e6:
origDEST_1839 := RAX;
origCOUNT_1840 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), CF, LSHIFT_64(origDEST_1839, (MINUS_64(64bv64, origCOUNT_1840)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 1bv64)), origDEST_1839[64:63], unconstrained_623));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1840 == 0bv64)), AF, unconstrained_624);

label_0xd1ea:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd1f1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd1f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0xd1fd:
origDEST_1845 := RCX;
origCOUNT_1846 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), CF, LSHIFT_64(origDEST_1845, (MINUS_64(64bv64, origCOUNT_1846)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 1bv64)), origDEST_1845[64:63], unconstrained_625));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1846 == 0bv64)), AF, unconstrained_626);

label_0xd201:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_627;
SF := unconstrained_628;
AF := unconstrained_629;
PF := unconstrained_630;

label_0xd205:
if (bv2bool(CF)) {
  goto label_0xd208;
}

label_0xd207:
assume false;

label_0xd208:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0xd210:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 796bv64)));

label_0xd217:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd219:
goto label_0xce15;

label_0xd21e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd226:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xd22c:
t_1851 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1851[32:31]) == (1bv32[32:31]))), (XOR_1((t_1851[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1851)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd22e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd236:
t_1855 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_1855)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1855, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1855, 4bv32)), t_1855)), 2bv32)), (XOR_32((RSHIFT_32(t_1855, 4bv32)), t_1855)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1855, 4bv32)), t_1855)), 2bv32)), (XOR_32((RSHIFT_32(t_1855, 4bv32)), t_1855)))))[1:0]));
SF := t_1855[32:31];
ZF := bool2bv(0bv32 == t_1855);

label_0xd23c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xd245;
}

label_0xd23e:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_631;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xd240:
goto label_0xdea1;

label_0xd245:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd24d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xd253:
t_1859 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1859[32:31]) == (1bv32[32:31]))), (XOR_1((t_1859[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1859)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd255:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd25d:
t_1863 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_1863)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1863, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1863, 4bv32)), t_1863)), 2bv32)), (XOR_32((RSHIFT_32(t_1863, 4bv32)), t_1863)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1863, 4bv32)), t_1863)), 2bv32)), (XOR_32((RSHIFT_32(t_1863, 4bv32)), t_1863)))))[1:0]));
SF := t_1863[32:31];
ZF := bool2bv(0bv32 == t_1863);

label_0xd263:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xd26c;
}

label_0xd265:
RAX := (RAX[64:8]) ++ 1bv8;

label_0xd267:
goto label_0xdea1;

label_0xd26c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd274:
t1_1867 := RAX;
t2_1868 := 16bv64;
RAX := PLUS_64(RAX, t2_1868);
CF := bool2bv(LT_64(RAX, t1_1867));
OF := AND_1((bool2bv((t1_1867[64:63]) == (t2_1868[64:63]))), (XOR_1((t1_1867[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1867)), t2_1868)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd278:
mem := STORE_LE_64(mem, PLUS_64(RSP, 392bv64), RAX);

label_0xd280:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0xd288:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_632;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd28e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd293:
t_1875 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_633;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1875, 4bv64)), t_1875)), 2bv64)), (XOR_64((RSHIFT_64(t_1875, 4bv64)), t_1875)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1875, 4bv64)), t_1875)), 2bv64)), (XOR_64((RSHIFT_64(t_1875, 4bv64)), t_1875)))))[1:0]));
SF := t_1875[64:63];
ZF := bool2bv(0bv64 == t_1875);

label_0xd296:
if (bv2bool(ZF)) {
  goto label_0xd299;
}

label_0xd298:
assume false;

label_0xd299:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0xd2a1:
origDEST_1879 := RAX;
origCOUNT_1880 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), CF, LSHIFT_64(origDEST_1879, (MINUS_64(64bv64, origCOUNT_1880)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 1bv64)), origDEST_1879[64:63], unconstrained_634));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1880 == 0bv64)), AF, unconstrained_635);

label_0xd2a5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd2ac:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd2b0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0xd2b8:
origDEST_1885 := RCX;
origCOUNT_1886 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), CF, LSHIFT_64(origDEST_1885, (MINUS_64(64bv64, origCOUNT_1886)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 1bv64)), origDEST_1885[64:63], unconstrained_636));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1886 == 0bv64)), AF, unconstrained_637);

label_0xd2bc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_638;
SF := unconstrained_639;
AF := unconstrained_640;
PF := unconstrained_641;

label_0xd2c0:
if (bv2bool(CF)) {
  goto label_0xd2c3;
}

label_0xd2c2:
assume false;

label_0xd2c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0xd2cb:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0xd2d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd2d9:
t1_1891 := RAX;
t2_1892 := 64bv64;
RAX := PLUS_64(RAX, t2_1892);
CF := bool2bv(LT_64(RAX, t1_1891));
OF := AND_1((bool2bv((t1_1891[64:63]) == (t2_1892[64:63]))), (XOR_1((t1_1891[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1891)), t2_1892)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd2dd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 968bv64), RAX);

label_0xd2e5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd2ed:
t1_1897 := RAX;
t2_1898 := 12bv64;
RAX := PLUS_64(RAX, t2_1898);
CF := bool2bv(LT_64(RAX, t1_1897));
OF := AND_1((bool2bv((t1_1897[64:63]) == (t2_1898[64:63]))), (XOR_1((t1_1897[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1897)), t2_1898)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd2f1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 400bv64), RAX);

label_0xd2f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xd301:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_642;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd307:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd30c:
t_1905 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_643;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1905, 4bv64)), t_1905)), 2bv64)), (XOR_64((RSHIFT_64(t_1905, 4bv64)), t_1905)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1905, 4bv64)), t_1905)), 2bv64)), (XOR_64((RSHIFT_64(t_1905, 4bv64)), t_1905)))))[1:0]));
SF := t_1905[64:63];
ZF := bool2bv(0bv64 == t_1905);

label_0xd30f:
if (bv2bool(ZF)) {
  goto label_0xd312;
}

label_0xd311:
assume false;

label_0xd312:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xd31a:
origDEST_1909 := RAX;
origCOUNT_1910 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), CF, LSHIFT_64(origDEST_1909, (MINUS_64(64bv64, origCOUNT_1910)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 1bv64)), origDEST_1909[64:63], unconstrained_644));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1910 == 0bv64)), AF, unconstrained_645);

label_0xd31e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd325:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd329:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xd331:
origDEST_1915 := RCX;
origCOUNT_1916 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), CF, LSHIFT_64(origDEST_1915, (MINUS_64(64bv64, origCOUNT_1916)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 1bv64)), origDEST_1915[64:63], unconstrained_646));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1916 == 0bv64)), AF, unconstrained_647);

label_0xd335:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_648;
SF := unconstrained_649;
AF := unconstrained_650;
PF := unconstrained_651;

label_0xd339:
if (bv2bool(CF)) {
  goto label_0xd33c;
}

label_0xd33b:
assume false;

label_0xd33c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0xd344:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 968bv64));

label_0xd34c:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0xd34f:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0xd351:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd359:
t1_1921 := RAX;
t2_1922 := 1096bv64;
RAX := PLUS_64(RAX, t2_1922);
CF := bool2bv(LT_64(RAX, t1_1921));
OF := AND_1((bool2bv((t1_1921[64:63]) == (t2_1922[64:63]))), (XOR_1((t1_1921[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1921)), t2_1922)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd35f:
RDX := RAX;

label_0xd362:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd36a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd36d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 54130bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd372"} true;
call arbitrary_func();

label_0xd372:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xd376:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd37e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd381:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd389:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xd390:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xd394:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd39c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xd39f:
origDEST_1927 := RCX[32:0];
origCOUNT_1928 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), CF, LSHIFT_32(origDEST_1927, (MINUS_32(32bv32, origCOUNT_1928)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 1bv32)), origDEST_1927[32:31], unconstrained_652));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1928 == 0bv32)), AF, unconstrained_653);

label_0xd3a1:
RCX := (0bv32 ++ RCX[32:0]);

label_0xd3a3:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd3ab:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xd3b2:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xd3b6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 800bv64), RCX[32:0]);

label_0xd3bd:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd3c5:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xd3c8:
origDEST_1933 := RDX[32:0];
origCOUNT_1934 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), CF, RSHIFT_32(origDEST_1933, (MINUS_32(32bv32, origCOUNT_1934)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_654));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1934 == 0bv32)), AF, unconstrained_655);

label_0xd3cb:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_656;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xd3ce:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xd3d1:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 800bv64)));

label_0xd3d8:
origDEST_1941 := RDX[32:0];
origCOUNT_1942 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), CF, LSHIFT_32(origDEST_1941, (MINUS_32(32bv32, origCOUNT_1942)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 1bv32)), origDEST_1941[32:31], unconstrained_657));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1942 == 0bv32)), AF, unconstrained_658);

label_0xd3da:
RCX := (0bv32 ++ RDX[32:0]);

label_0xd3dc:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_659;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xd3df:
origDEST_1949 := RCX[32:0];
origCOUNT_1950 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), CF, RSHIFT_32(origDEST_1949, (MINUS_32(32bv32, origCOUNT_1950)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_660));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1950 == 0bv32)), AF, unconstrained_661);

label_0xd3e2:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_662;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd3e4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 804bv64), RAX[32:0]);

label_0xd3eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd3f3:
t1_1957 := RAX;
t2_1958 := 60bv64;
RAX := PLUS_64(RAX, t2_1958);
CF := bool2bv(LT_64(RAX, t1_1957));
OF := AND_1((bool2bv((t1_1957[64:63]) == (t2_1958[64:63]))), (XOR_1((t1_1957[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1957)), t2_1958)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd3f7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 408bv64), RAX);

label_0xd3ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0xd407:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_663;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd40d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd412:
t_1965 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_664;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1965, 4bv64)), t_1965)), 2bv64)), (XOR_64((RSHIFT_64(t_1965, 4bv64)), t_1965)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1965, 4bv64)), t_1965)), 2bv64)), (XOR_64((RSHIFT_64(t_1965, 4bv64)), t_1965)))))[1:0]));
SF := t_1965[64:63];
ZF := bool2bv(0bv64 == t_1965);

label_0xd415:
if (bv2bool(ZF)) {
  goto label_0xd418;
}

label_0xd417:
assume false;

label_0xd418:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0xd420:
origDEST_1969 := RAX;
origCOUNT_1970 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), CF, LSHIFT_64(origDEST_1969, (MINUS_64(64bv64, origCOUNT_1970)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 1bv64)), origDEST_1969[64:63], unconstrained_665));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1970 == 0bv64)), AF, unconstrained_666);

label_0xd424:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd42b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd42f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0xd437:
origDEST_1975 := RCX;
origCOUNT_1976 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), CF, LSHIFT_64(origDEST_1975, (MINUS_64(64bv64, origCOUNT_1976)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 1bv64)), origDEST_1975[64:63], unconstrained_667));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1976 == 0bv64)), AF, unconstrained_668);

label_0xd43b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_669;
SF := unconstrained_670;
AF := unconstrained_671;
PF := unconstrained_672;

label_0xd43f:
if (bv2bool(CF)) {
  goto label_0xd442;
}

label_0xd441:
assume false;

label_0xd442:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0xd44a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 804bv64)));

label_0xd451:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd453:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd45b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xd461:
t_1981 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1981[32:31]) == (1bv32[32:31]))), (XOR_1((t_1981[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1981)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd463:
mem := STORE_LE_32(mem, PLUS_64(RSP, 808bv64), RAX[32:0]);

label_0xd46a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd472:
t1_1985 := RAX;
t2_1986 := 1092bv64;
RAX := PLUS_64(RAX, t2_1986);
CF := bool2bv(LT_64(RAX, t1_1985));
OF := AND_1((bool2bv((t1_1985[64:63]) == (t2_1986[64:63]))), (XOR_1((t1_1985[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1985)), t2_1986)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd478:
mem := STORE_LE_64(mem, PLUS_64(RSP, 416bv64), RAX);

label_0xd480:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xd488:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_673;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd48e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd493:
t_1993 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_674;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1993, 4bv64)), t_1993)), 2bv64)), (XOR_64((RSHIFT_64(t_1993, 4bv64)), t_1993)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1993, 4bv64)), t_1993)), 2bv64)), (XOR_64((RSHIFT_64(t_1993, 4bv64)), t_1993)))))[1:0]));
SF := t_1993[64:63];
ZF := bool2bv(0bv64 == t_1993);

label_0xd496:
if (bv2bool(ZF)) {
  goto label_0xd499;
}

label_0xd498:
assume false;

label_0xd499:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xd4a1:
origDEST_1997 := RAX;
origCOUNT_1998 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), CF, LSHIFT_64(origDEST_1997, (MINUS_64(64bv64, origCOUNT_1998)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 1bv64)), origDEST_1997[64:63], unconstrained_675));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1998 == 0bv64)), AF, unconstrained_676);

label_0xd4a5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd4ac:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd4b0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xd4b8:
origDEST_2003 := RCX;
origCOUNT_2004 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), CF, LSHIFT_64(origDEST_2003, (MINUS_64(64bv64, origCOUNT_2004)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 1bv64)), origDEST_2003[64:63], unconstrained_677));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2004 == 0bv64)), AF, unconstrained_678);

label_0xd4bc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_679;
SF := unconstrained_680;
AF := unconstrained_681;
PF := unconstrained_682;

label_0xd4c0:
if (bv2bool(CF)) {
  goto label_0xd4c3;
}

label_0xd4c2:
assume false;

label_0xd4c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0xd4cb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 808bv64)));

label_0xd4d2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd4d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd4dc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xd4e2:
t_2009 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2009[32:31]) == (1bv32[32:31]))), (XOR_1((t_2009[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2009)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd4e4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd4ec:
t_2013 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_2013)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2013, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2013, 4bv32)), t_2013)), 2bv32)), (XOR_32((RSHIFT_32(t_2013, 4bv32)), t_2013)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2013, 4bv32)), t_2013)), 2bv32)), (XOR_32((RSHIFT_32(t_2013, 4bv32)), t_2013)))))[1:0]));
SF := t_2013[32:31];
ZF := bool2bv(0bv32 == t_2013);

label_0xd4f2:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xd4f9;
}

label_0xd4f4:
goto label_0xce0a;

label_0xd4f9:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xd4fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd506:
t_2017 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_2017)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2017, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2017, 4bv32)), t_2017)), 2bv32)), (XOR_32((RSHIFT_32(t_2017, 4bv32)), t_2017)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2017, 4bv32)), t_2017)), 2bv32)), (XOR_32((RSHIFT_32(t_2017, 4bv32)), t_2017)))))[1:0]));
SF := t_2017[32:31];
ZF := bool2bv(0bv32 == t_2017);

label_0xd509:
if (bv2bool(ZF)) {
  goto label_0xd584;
}

label_0xd50b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd513:
t1_2021 := RAX;
t2_2022 := 64bv64;
RAX := PLUS_64(RAX, t2_2022);
CF := bool2bv(LT_64(RAX, t1_2021));
OF := AND_1((bool2bv((t1_2021[64:63]) == (t2_2022[64:63]))), (XOR_1((t1_2021[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2021)), t2_2022)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd517:
mem := STORE_LE_64(mem, PLUS_64(RSP, 424bv64), RAX);

label_0xd51f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xd524:
mem := STORE_LE_32(mem, PLUS_64(RSP, 812bv64), RAX[32:0]);

label_0xd52b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xd533:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_683;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd539:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd53e:
t_2029 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_684;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2029, 4bv64)), t_2029)), 2bv64)), (XOR_64((RSHIFT_64(t_2029, 4bv64)), t_2029)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2029, 4bv64)), t_2029)), 2bv64)), (XOR_64((RSHIFT_64(t_2029, 4bv64)), t_2029)))))[1:0]));
SF := t_2029[64:63];
ZF := bool2bv(0bv64 == t_2029);

label_0xd541:
if (bv2bool(ZF)) {
  goto label_0xd544;
}

label_0xd543:
assume false;

label_0xd544:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xd54c:
origDEST_2033 := RAX;
origCOUNT_2034 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), CF, LSHIFT_64(origDEST_2033, (MINUS_64(64bv64, origCOUNT_2034)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 1bv64)), origDEST_2033[64:63], unconstrained_685));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2034 == 0bv64)), AF, unconstrained_686);

label_0xd550:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd557:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd55b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xd563:
origDEST_2039 := RCX;
origCOUNT_2040 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), CF, LSHIFT_64(origDEST_2039, (MINUS_64(64bv64, origCOUNT_2040)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 1bv64)), origDEST_2039[64:63], unconstrained_687));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2040 == 0bv64)), AF, unconstrained_688);

label_0xd567:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_689;
SF := unconstrained_690;
AF := unconstrained_691;
PF := unconstrained_692;

label_0xd56b:
if (bv2bool(CF)) {
  goto label_0xd56e;
}

label_0xd56d:
assume false;

label_0xd56e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0xd576:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 812bv64)));

label_0xd57d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd57f:
goto label_0xce0a;

label_0xd584:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd58c:
t1_2045 := RAX;
t2_2046 := 16bv64;
RAX := PLUS_64(RAX, t2_2046);
CF := bool2bv(LT_64(RAX, t1_2045));
OF := AND_1((bool2bv((t1_2045[64:63]) == (t2_2046[64:63]))), (XOR_1((t1_2045[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2045)), t2_2046)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd590:
mem := STORE_LE_64(mem, PLUS_64(RSP, 432bv64), RAX);

label_0xd598:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd5a0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_693;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd5a6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd5ab:
t_2053 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_694;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2053, 4bv64)), t_2053)), 2bv64)), (XOR_64((RSHIFT_64(t_2053, 4bv64)), t_2053)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2053, 4bv64)), t_2053)), 2bv64)), (XOR_64((RSHIFT_64(t_2053, 4bv64)), t_2053)))))[1:0]));
SF := t_2053[64:63];
ZF := bool2bv(0bv64 == t_2053);

label_0xd5ae:
if (bv2bool(ZF)) {
  goto label_0xd5b1;
}

label_0xd5b0:
assume false;

label_0xd5b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd5b9:
origDEST_2057 := RAX;
origCOUNT_2058 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), CF, LSHIFT_64(origDEST_2057, (MINUS_64(64bv64, origCOUNT_2058)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 1bv64)), origDEST_2057[64:63], unconstrained_695));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2058 == 0bv64)), AF, unconstrained_696);

label_0xd5bd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd5c4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd5c8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd5d0:
origDEST_2063 := RCX;
origCOUNT_2064 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), CF, LSHIFT_64(origDEST_2063, (MINUS_64(64bv64, origCOUNT_2064)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 1bv64)), origDEST_2063[64:63], unconstrained_697));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2064 == 0bv64)), AF, unconstrained_698);

label_0xd5d4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_699;
SF := unconstrained_700;
AF := unconstrained_701;
PF := unconstrained_702;

label_0xd5d8:
if (bv2bool(CF)) {
  goto label_0xd5db;
}

label_0xd5da:
assume false;

label_0xd5db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0xd5e3:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0xd5e9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd5f1:
t1_2069 := RAX;
t2_2070 := 1096bv64;
RAX := PLUS_64(RAX, t2_2070);
CF := bool2bv(LT_64(RAX, t1_2069));
OF := AND_1((bool2bv((t1_2069[64:63]) == (t2_2070[64:63]))), (XOR_1((t1_2069[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2069)), t2_2070)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd5f7:
RDX := RAX;

label_0xd5fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd602:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd605:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 54794bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd60a"} true;
call arbitrary_func();

label_0xd60a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xd60e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd616:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd619:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd621:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xd628:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xd62c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd634:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xd637:
origDEST_2075 := RCX[32:0];
origCOUNT_2076 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), CF, LSHIFT_32(origDEST_2075, (MINUS_32(32bv32, origCOUNT_2076)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 1bv32)), origDEST_2075[32:31], unconstrained_703));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2076 == 0bv32)), AF, unconstrained_704);

label_0xd639:
RCX := (0bv32 ++ RCX[32:0]);

label_0xd63b:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd643:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xd64a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xd64e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 816bv64), RCX[32:0]);

label_0xd655:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd65d:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xd660:
origDEST_2081 := RDX[32:0];
origCOUNT_2082 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), CF, RSHIFT_32(origDEST_2081, (MINUS_32(32bv32, origCOUNT_2082)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_705));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2082 == 0bv32)), AF, unconstrained_706);

label_0xd663:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_707;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xd666:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xd669:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 816bv64)));

label_0xd670:
origDEST_2089 := RDX[32:0];
origCOUNT_2090 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), CF, LSHIFT_32(origDEST_2089, (MINUS_32(32bv32, origCOUNT_2090)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 1bv32)), origDEST_2089[32:31], unconstrained_708));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2090 == 0bv32)), AF, unconstrained_709);

label_0xd672:
RCX := (0bv32 ++ RDX[32:0]);

label_0xd674:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_710;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xd677:
origDEST_2097 := RCX[32:0];
origCOUNT_2098 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), CF, RSHIFT_32(origDEST_2097, (MINUS_32(32bv32, origCOUNT_2098)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_711));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2098 == 0bv32)), AF, unconstrained_712);

label_0xd67a:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_713;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd67c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 820bv64), RAX[32:0]);

label_0xd683:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd68b:
t1_2105 := RAX;
t2_2106 := 60bv64;
RAX := PLUS_64(RAX, t2_2106);
CF := bool2bv(LT_64(RAX, t1_2105));
OF := AND_1((bool2bv((t1_2105[64:63]) == (t2_2106[64:63]))), (XOR_1((t1_2105[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2105)), t2_2106)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd68f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 440bv64), RAX);

label_0xd697:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0xd69f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_714;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd6a5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd6aa:
t_2113 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_715;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2113, 4bv64)), t_2113)), 2bv64)), (XOR_64((RSHIFT_64(t_2113, 4bv64)), t_2113)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2113, 4bv64)), t_2113)), 2bv64)), (XOR_64((RSHIFT_64(t_2113, 4bv64)), t_2113)))))[1:0]));
SF := t_2113[64:63];
ZF := bool2bv(0bv64 == t_2113);

label_0xd6ad:
if (bv2bool(ZF)) {
  goto label_0xd6b0;
}

label_0xd6af:
assume false;

label_0xd6b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0xd6b8:
origDEST_2117 := RAX;
origCOUNT_2118 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), CF, LSHIFT_64(origDEST_2117, (MINUS_64(64bv64, origCOUNT_2118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 1bv64)), origDEST_2117[64:63], unconstrained_716));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2118 == 0bv64)), AF, unconstrained_717);

label_0xd6bc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd6c3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd6c7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0xd6cf:
origDEST_2123 := RCX;
origCOUNT_2124 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), CF, LSHIFT_64(origDEST_2123, (MINUS_64(64bv64, origCOUNT_2124)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 1bv64)), origDEST_2123[64:63], unconstrained_718));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2124 == 0bv64)), AF, unconstrained_719);

label_0xd6d3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_720;
SF := unconstrained_721;
AF := unconstrained_722;
PF := unconstrained_723;

label_0xd6d7:
if (bv2bool(CF)) {
  goto label_0xd6da;
}

label_0xd6d9:
assume false;

label_0xd6da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0xd6e2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 820bv64)));

label_0xd6e9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd6eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd6f3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xd6f9:
t_2129 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2129[32:31]) == (1bv32[32:31]))), (XOR_1((t_2129[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2129)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd6fb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 824bv64), RAX[32:0]);

label_0xd702:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd70a:
t1_2133 := RAX;
t2_2134 := 1092bv64;
RAX := PLUS_64(RAX, t2_2134);
CF := bool2bv(LT_64(RAX, t1_2133));
OF := AND_1((bool2bv((t1_2133[64:63]) == (t2_2134[64:63]))), (XOR_1((t1_2133[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2133)), t2_2134)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd710:
mem := STORE_LE_64(mem, PLUS_64(RSP, 448bv64), RAX);

label_0xd718:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0xd720:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_724;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd726:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd72b:
t_2141 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_725;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2141, 4bv64)), t_2141)), 2bv64)), (XOR_64((RSHIFT_64(t_2141, 4bv64)), t_2141)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2141, 4bv64)), t_2141)), 2bv64)), (XOR_64((RSHIFT_64(t_2141, 4bv64)), t_2141)))))[1:0]));
SF := t_2141[64:63];
ZF := bool2bv(0bv64 == t_2141);

label_0xd72e:
if (bv2bool(ZF)) {
  goto label_0xd731;
}

label_0xd730:
assume false;

label_0xd731:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0xd739:
origDEST_2145 := RAX;
origCOUNT_2146 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), CF, LSHIFT_64(origDEST_2145, (MINUS_64(64bv64, origCOUNT_2146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 1bv64)), origDEST_2145[64:63], unconstrained_726));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2146 == 0bv64)), AF, unconstrained_727);

label_0xd73d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd744:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd748:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0xd750:
origDEST_2151 := RCX;
origCOUNT_2152 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), CF, LSHIFT_64(origDEST_2151, (MINUS_64(64bv64, origCOUNT_2152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 1bv64)), origDEST_2151[64:63], unconstrained_728));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2152 == 0bv64)), AF, unconstrained_729);

label_0xd754:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_730;
SF := unconstrained_731;
AF := unconstrained_732;
PF := unconstrained_733;

label_0xd758:
if (bv2bool(CF)) {
  goto label_0xd75b;
}

label_0xd75a:
assume false;

label_0xd75b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0xd763:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 824bv64)));

label_0xd76a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd76c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd774:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xd77a:
t_2157 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2157[32:31]) == (1bv32[32:31]))), (XOR_1((t_2157[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2157)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd77c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd784:
t_2161 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_2161)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2161, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2161, 4bv32)), t_2161)), 2bv32)), (XOR_32((RSHIFT_32(t_2161, 4bv32)), t_2161)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2161, 4bv32)), t_2161)), 2bv32)), (XOR_32((RSHIFT_32(t_2161, 4bv32)), t_2161)))))[1:0]));
SF := t_2161[32:31];
ZF := bool2bv(0bv32 == t_2161);

label_0xd78a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xd791;
}

label_0xd78c:
goto label_0xce0a;

label_0xd791:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xd796:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd79e:
t_2165 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_2165)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2165, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2165, 4bv32)), t_2165)), 2bv32)), (XOR_32((RSHIFT_32(t_2165, 4bv32)), t_2165)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2165, 4bv32)), t_2165)), 2bv32)), (XOR_32((RSHIFT_32(t_2165, 4bv32)), t_2165)))))[1:0]));
SF := t_2165[32:31];
ZF := bool2bv(0bv32 == t_2165);

label_0xd7a1:
if (bv2bool(ZF)) {
  goto label_0xd81c;
}

label_0xd7a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd7ab:
t1_2169 := RAX;
t2_2170 := 64bv64;
RAX := PLUS_64(RAX, t2_2170);
CF := bool2bv(LT_64(RAX, t1_2169));
OF := AND_1((bool2bv((t1_2169[64:63]) == (t2_2170[64:63]))), (XOR_1((t1_2169[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2169)), t2_2170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd7af:
mem := STORE_LE_64(mem, PLUS_64(RSP, 456bv64), RAX);

label_0xd7b7:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xd7bc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 828bv64), RAX[32:0]);

label_0xd7c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xd7cb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_734;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd7d1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd7d6:
t_2177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_735;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2177, 4bv64)), t_2177)), 2bv64)), (XOR_64((RSHIFT_64(t_2177, 4bv64)), t_2177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2177, 4bv64)), t_2177)), 2bv64)), (XOR_64((RSHIFT_64(t_2177, 4bv64)), t_2177)))))[1:0]));
SF := t_2177[64:63];
ZF := bool2bv(0bv64 == t_2177);

label_0xd7d9:
if (bv2bool(ZF)) {
  goto label_0xd7dc;
}

label_0xd7db:
assume false;

label_0xd7dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xd7e4:
origDEST_2181 := RAX;
origCOUNT_2182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), CF, LSHIFT_64(origDEST_2181, (MINUS_64(64bv64, origCOUNT_2182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 1bv64)), origDEST_2181[64:63], unconstrained_736));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2182 == 0bv64)), AF, unconstrained_737);

label_0xd7e8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd7ef:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd7f3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xd7fb:
origDEST_2187 := RCX;
origCOUNT_2188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), CF, LSHIFT_64(origDEST_2187, (MINUS_64(64bv64, origCOUNT_2188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 1bv64)), origDEST_2187[64:63], unconstrained_738));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2188 == 0bv64)), AF, unconstrained_739);

label_0xd7ff:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_740;
SF := unconstrained_741;
AF := unconstrained_742;
PF := unconstrained_743;

label_0xd803:
if (bv2bool(CF)) {
  goto label_0xd806;
}

label_0xd805:
assume false;

label_0xd806:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0xd80e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 828bv64)));

label_0xd815:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd817:
goto label_0xce0a;

label_0xd81c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd824:
t1_2193 := RAX;
t2_2194 := 16bv64;
RAX := PLUS_64(RAX, t2_2194);
CF := bool2bv(LT_64(RAX, t1_2193));
OF := AND_1((bool2bv((t1_2193[64:63]) == (t2_2194[64:63]))), (XOR_1((t1_2193[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2193)), t2_2194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd828:
mem := STORE_LE_64(mem, PLUS_64(RSP, 472bv64), RAX);

label_0xd830:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0xd838:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_744;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd83e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd843:
t_2201 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_745;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2201, 4bv64)), t_2201)), 2bv64)), (XOR_64((RSHIFT_64(t_2201, 4bv64)), t_2201)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2201, 4bv64)), t_2201)), 2bv64)), (XOR_64((RSHIFT_64(t_2201, 4bv64)), t_2201)))))[1:0]));
SF := t_2201[64:63];
ZF := bool2bv(0bv64 == t_2201);

label_0xd846:
if (bv2bool(ZF)) {
  goto label_0xd849;
}

label_0xd848:
assume false;

label_0xd849:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0xd851:
origDEST_2205 := RAX;
origCOUNT_2206 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), CF, LSHIFT_64(origDEST_2205, (MINUS_64(64bv64, origCOUNT_2206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 1bv64)), origDEST_2205[64:63], unconstrained_746));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2206 == 0bv64)), AF, unconstrained_747);

label_0xd855:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd85c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd860:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0xd868:
origDEST_2211 := RCX;
origCOUNT_2212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), CF, LSHIFT_64(origDEST_2211, (MINUS_64(64bv64, origCOUNT_2212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 1bv64)), origDEST_2211[64:63], unconstrained_748));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2212 == 0bv64)), AF, unconstrained_749);

label_0xd86c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_750;
SF := unconstrained_751;
AF := unconstrained_752;
PF := unconstrained_753;

label_0xd870:
if (bv2bool(CF)) {
  goto label_0xd873;
}

label_0xd872:
assume false;

label_0xd873:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0xd87b:
mem := STORE_LE_32(mem, RAX, 3bv32);

label_0xd881:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd889:
t1_2217 := RAX;
t2_2218 := 1096bv64;
RAX := PLUS_64(RAX, t2_2218);
CF := bool2bv(LT_64(RAX, t1_2217));
OF := AND_1((bool2bv((t1_2217[64:63]) == (t2_2218[64:63]))), (XOR_1((t1_2217[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2217)), t2_2218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd88f:
RDX := RAX;

label_0xd892:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd89a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd89d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 55458bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd8a2"} true;
call arbitrary_func();

label_0xd8a2:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xd8a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd8ae:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xd8b1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd8b9:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xd8c0:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xd8c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd8cc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xd8cf:
origDEST_2223 := RCX[32:0];
origCOUNT_2224 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), CF, LSHIFT_32(origDEST_2223, (MINUS_32(32bv32, origCOUNT_2224)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 1bv32)), origDEST_2223[32:31], unconstrained_754));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2224 == 0bv32)), AF, unconstrained_755);

label_0xd8d1:
RCX := (0bv32 ++ RCX[32:0]);

label_0xd8d3:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd8db:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xd8e2:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xd8e6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 832bv64), RCX[32:0]);

label_0xd8ed:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd8f5:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xd8f8:
origDEST_2229 := RDX[32:0];
origCOUNT_2230 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), CF, RSHIFT_32(origDEST_2229, (MINUS_32(32bv32, origCOUNT_2230)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_756));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2230 == 0bv32)), AF, unconstrained_757);

label_0xd8fb:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_758;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xd8fe:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xd901:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 832bv64)));

label_0xd908:
origDEST_2237 := RDX[32:0];
origCOUNT_2238 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), CF, LSHIFT_32(origDEST_2237, (MINUS_32(32bv32, origCOUNT_2238)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 1bv32)), origDEST_2237[32:31], unconstrained_759));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2238 == 0bv32)), AF, unconstrained_760);

label_0xd90a:
RCX := (0bv32 ++ RDX[32:0]);

label_0xd90c:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_761;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xd90f:
origDEST_2245 := RCX[32:0];
origCOUNT_2246 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), CF, RSHIFT_32(origDEST_2245, (MINUS_32(32bv32, origCOUNT_2246)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_762));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2246 == 0bv32)), AF, unconstrained_763);

label_0xd912:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_764;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd914:
mem := STORE_LE_32(mem, PLUS_64(RSP, 836bv64), RAX[32:0]);

label_0xd91b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd923:
t1_2253 := RAX;
t2_2254 := 60bv64;
RAX := PLUS_64(RAX, t2_2254);
CF := bool2bv(LT_64(RAX, t1_2253));
OF := AND_1((bool2bv((t1_2253[64:63]) == (t2_2254[64:63]))), (XOR_1((t1_2253[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2253)), t2_2254)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd927:
mem := STORE_LE_64(mem, PLUS_64(RSP, 480bv64), RAX);

label_0xd92f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0xd937:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_765;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd93d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd942:
t_2261 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_766;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2261, 4bv64)), t_2261)), 2bv64)), (XOR_64((RSHIFT_64(t_2261, 4bv64)), t_2261)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2261, 4bv64)), t_2261)), 2bv64)), (XOR_64((RSHIFT_64(t_2261, 4bv64)), t_2261)))))[1:0]));
SF := t_2261[64:63];
ZF := bool2bv(0bv64 == t_2261);

label_0xd945:
if (bv2bool(ZF)) {
  goto label_0xd948;
}

label_0xd947:
assume false;

label_0xd948:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0xd950:
origDEST_2265 := RAX;
origCOUNT_2266 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), CF, LSHIFT_64(origDEST_2265, (MINUS_64(64bv64, origCOUNT_2266)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 1bv64)), origDEST_2265[64:63], unconstrained_767));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2266 == 0bv64)), AF, unconstrained_768);

label_0xd954:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd95b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd95f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0xd967:
origDEST_2271 := RCX;
origCOUNT_2272 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), CF, LSHIFT_64(origDEST_2271, (MINUS_64(64bv64, origCOUNT_2272)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 1bv64)), origDEST_2271[64:63], unconstrained_769));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2272 == 0bv64)), AF, unconstrained_770);

label_0xd96b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_771;
SF := unconstrained_772;
AF := unconstrained_773;
PF := unconstrained_774;

label_0xd96f:
if (bv2bool(CF)) {
  goto label_0xd972;
}

label_0xd971:
assume false;

label_0xd972:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 480bv64));

label_0xd97a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 836bv64)));

label_0xd981:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xd983:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd98b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xd991:
t_2277 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2277[32:31]) == (1bv32[32:31]))), (XOR_1((t_2277[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2277)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd993:
mem := STORE_LE_32(mem, PLUS_64(RSP, 880bv64), RAX[32:0]);

label_0xd99a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xd9a2:
t1_2281 := RAX;
t2_2282 := 1092bv64;
RAX := PLUS_64(RAX, t2_2282);
CF := bool2bv(LT_64(RAX, t1_2281));
OF := AND_1((bool2bv((t1_2281[64:63]) == (t2_2282[64:63]))), (XOR_1((t1_2281[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2281)), t2_2282)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd9a8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 608bv64), RAX);

label_0xd9b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 608bv64));

label_0xd9b8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_775;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd9be:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd9c3:
t_2289 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_776;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2289, 4bv64)), t_2289)), 2bv64)), (XOR_64((RSHIFT_64(t_2289, 4bv64)), t_2289)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2289, 4bv64)), t_2289)), 2bv64)), (XOR_64((RSHIFT_64(t_2289, 4bv64)), t_2289)))))[1:0]));
SF := t_2289[64:63];
ZF := bool2bv(0bv64 == t_2289);

label_0xd9c6:
if (bv2bool(ZF)) {
  goto label_0xd9c9;
}

label_0xd9c8:
assume false;

label_0xd9c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 608bv64));

label_0xd9d1:
origDEST_2293 := RAX;
origCOUNT_2294 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), CF, LSHIFT_64(origDEST_2293, (MINUS_64(64bv64, origCOUNT_2294)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 1bv64)), origDEST_2293[64:63], unconstrained_777));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2294 == 0bv64)), AF, unconstrained_778);

label_0xd9d5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd9dc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd9e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 608bv64));

label_0xd9e8:
origDEST_2299 := RCX;
origCOUNT_2300 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), CF, LSHIFT_64(origDEST_2299, (MINUS_64(64bv64, origCOUNT_2300)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 1bv64)), origDEST_2299[64:63], unconstrained_779));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2300 == 0bv64)), AF, unconstrained_780);

label_0xd9ec:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_781;
SF := unconstrained_782;
AF := unconstrained_783;
PF := unconstrained_784;

label_0xd9f0:
if (bv2bool(CF)) {
  goto label_0xd9f3;
}

label_0xd9f2:
assume false;

label_0xd9f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 608bv64));

label_0xd9fb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 880bv64)));

label_0xda02:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xda04:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xda0c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0xda12:
t_2305 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2305[32:31]) == (1bv32[32:31]))), (XOR_1((t_2305[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2305)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xda14:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xda1c:
t_2309 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_2309)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2309, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2309, 4bv32)), t_2309)), 2bv32)), (XOR_32((RSHIFT_32(t_2309, 4bv32)), t_2309)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2309, 4bv32)), t_2309)), 2bv32)), (XOR_32((RSHIFT_32(t_2309, 4bv32)), t_2309)))))[1:0]));
SF := t_2309[32:31];
ZF := bool2bv(0bv32 == t_2309);

label_0xda22:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xda29;
}

label_0xda24:
goto label_0xce0a;

label_0xda29:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xda2e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xda36:
t_2313 := MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))));
CF := bool2bv(LT_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64)))));
OF := AND_32((XOR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))), (XOR_32((RAX[32:0]), t_2313)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_2313, (RAX[32:0]))), (LOAD_LE_32(mem, PLUS_64(RCX, 64bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2313, 4bv32)), t_2313)), 2bv32)), (XOR_32((RSHIFT_32(t_2313, 4bv32)), t_2313)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_2313, 4bv32)), t_2313)), 2bv32)), (XOR_32((RSHIFT_32(t_2313, 4bv32)), t_2313)))))[1:0]));
SF := t_2313[32:31];
ZF := bool2bv(0bv32 == t_2313);

label_0xda39:
if (bv2bool(ZF)) {
  goto label_0xdab4;
}

label_0xda3b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xda43:
t1_2317 := RAX;
t2_2318 := 64bv64;
RAX := PLUS_64(RAX, t2_2318);
CF := bool2bv(LT_64(RAX, t1_2317));
OF := AND_1((bool2bv((t1_2317[64:63]) == (t2_2318[64:63]))), (XOR_1((t1_2317[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2317)), t2_2318)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xda47:
mem := STORE_LE_64(mem, PLUS_64(RSP, 488bv64), RAX);

label_0xda4f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xda54:
mem := STORE_LE_32(mem, PLUS_64(RSP, 840bv64), RAX[32:0]);

label_0xda5b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0xda63:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_785;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xda69:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xda6e:
t_2325 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_786;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2325, 4bv64)), t_2325)), 2bv64)), (XOR_64((RSHIFT_64(t_2325, 4bv64)), t_2325)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2325, 4bv64)), t_2325)), 2bv64)), (XOR_64((RSHIFT_64(t_2325, 4bv64)), t_2325)))))[1:0]));
SF := t_2325[64:63];
ZF := bool2bv(0bv64 == t_2325);

label_0xda71:
if (bv2bool(ZF)) {
  goto label_0xda74;
}

label_0xda73:
assume false;

label_0xda74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0xda7c:
origDEST_2329 := RAX;
origCOUNT_2330 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), CF, LSHIFT_64(origDEST_2329, (MINUS_64(64bv64, origCOUNT_2330)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 1bv64)), origDEST_2329[64:63], unconstrained_787));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2330 == 0bv64)), AF, unconstrained_788);

label_0xda80:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xda87:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xda8b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0xda93:
origDEST_2335 := RCX;
origCOUNT_2336 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), CF, LSHIFT_64(origDEST_2335, (MINUS_64(64bv64, origCOUNT_2336)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 1bv64)), origDEST_2335[64:63], unconstrained_789));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2336 == 0bv64)), AF, unconstrained_790);

label_0xda97:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_791;
SF := unconstrained_792;
AF := unconstrained_793;
PF := unconstrained_794;

label_0xda9b:
if (bv2bool(CF)) {
  goto label_0xda9e;
}

label_0xda9d:
assume false;

label_0xda9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 488bv64));

label_0xdaa6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 840bv64)));

label_0xdaad:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xdaaf:
goto label_0xce0a;

label_0xdab4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdabc:
t1_2341 := RAX;
t2_2342 := 1096bv64;
RAX := PLUS_64(RAX, t2_2342);
CF := bool2bv(LT_64(RAX, t1_2341));
OF := AND_1((bool2bv((t1_2341[64:63]) == (t2_2342[64:63]))), (XOR_1((t1_2341[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2341)), t2_2342)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdac2:
RDX := RAX;

label_0xdac5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdacd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xdad0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 56021bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xdad5"} true;
call arbitrary_func();

label_0xdad5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xdad9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdae1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xdae4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdaec:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xdaf3:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xdaf7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdaff:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xdb02:
origDEST_2347 := RCX[32:0];
origCOUNT_2348 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), CF, LSHIFT_32(origDEST_2347, (MINUS_32(32bv32, origCOUNT_2348)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 1bv32)), origDEST_2347[32:31], unconstrained_795));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2348 == 0bv32)), AF, unconstrained_796);

label_0xdb04:
RCX := (0bv32 ++ RCX[32:0]);

label_0xdb06:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdb0e:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xdb15:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xdb19:
mem := STORE_LE_32(mem, PLUS_64(RSP, 844bv64), RCX[32:0]);

label_0xdb20:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdb28:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xdb2b:
origDEST_2353 := RDX[32:0];
origCOUNT_2354 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), CF, RSHIFT_32(origDEST_2353, (MINUS_32(32bv32, origCOUNT_2354)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_797));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2354 == 0bv32)), AF, unconstrained_798);

label_0xdb2e:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_799;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xdb31:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xdb34:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 844bv64)));

label_0xdb3b:
origDEST_2361 := RDX[32:0];
origCOUNT_2362 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), CF, LSHIFT_32(origDEST_2361, (MINUS_32(32bv32, origCOUNT_2362)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 1bv32)), origDEST_2361[32:31], unconstrained_800));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2362 == 0bv32)), AF, unconstrained_801);

label_0xdb3d:
RCX := (0bv32 ++ RDX[32:0]);

label_0xdb3f:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_802;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xdb42:
origDEST_2369 := RCX[32:0];
origCOUNT_2370 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), CF, RSHIFT_32(origDEST_2369, (MINUS_32(32bv32, origCOUNT_2370)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_803));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2370 == 0bv32)), AF, unconstrained_804);

label_0xdb45:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_805;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdb47:
mem := STORE_LE_32(mem, PLUS_64(RSP, 848bv64), RAX[32:0]);

label_0xdb4e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdb56:
t1_2377 := RAX;
t2_2378 := 60bv64;
RAX := PLUS_64(RAX, t2_2378);
CF := bool2bv(LT_64(RAX, t1_2377));
OF := AND_1((bool2bv((t1_2377[64:63]) == (t2_2378[64:63]))), (XOR_1((t1_2377[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2377)), t2_2378)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdb5a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 496bv64), RAX);

label_0xdb62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0xdb6a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_806;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdb70:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xdb75:
t_2385 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_807;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2385, 4bv64)), t_2385)), 2bv64)), (XOR_64((RSHIFT_64(t_2385, 4bv64)), t_2385)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2385, 4bv64)), t_2385)), 2bv64)), (XOR_64((RSHIFT_64(t_2385, 4bv64)), t_2385)))))[1:0]));
SF := t_2385[64:63];
ZF := bool2bv(0bv64 == t_2385);

label_0xdb78:
if (bv2bool(ZF)) {
  goto label_0xdb7b;
}

label_0xdb7a:
assume false;

label_0xdb7b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0xdb83:
origDEST_2389 := RAX;
origCOUNT_2390 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), CF, LSHIFT_64(origDEST_2389, (MINUS_64(64bv64, origCOUNT_2390)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 1bv64)), origDEST_2389[64:63], unconstrained_808));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2390 == 0bv64)), AF, unconstrained_809);

label_0xdb87:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xdb8e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xdb92:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0xdb9a:
origDEST_2395 := RCX;
origCOUNT_2396 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), CF, LSHIFT_64(origDEST_2395, (MINUS_64(64bv64, origCOUNT_2396)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 1bv64)), origDEST_2395[64:63], unconstrained_810));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2396 == 0bv64)), AF, unconstrained_811);

label_0xdb9e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_812;
SF := unconstrained_813;
AF := unconstrained_814;
PF := unconstrained_815;

label_0xdba2:
if (bv2bool(CF)) {
  goto label_0xdba5;
}

label_0xdba4:
assume false;

label_0xdba5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0xdbad:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 848bv64)));

label_0xdbb4:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xdbb6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdbbe:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xdbc4:
t_2401 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2401[32:31]) == (1bv32[32:31]))), (XOR_1((t_2401[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2401)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdbc6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 852bv64), RAX[32:0]);

label_0xdbcd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdbd5:
t1_2405 := RAX;
t2_2406 := 1092bv64;
RAX := PLUS_64(RAX, t2_2406);
CF := bool2bv(LT_64(RAX, t1_2405));
OF := AND_1((bool2bv((t1_2405[64:63]) == (t2_2406[64:63]))), (XOR_1((t1_2405[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2405)), t2_2406)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdbdb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 504bv64), RAX);

label_0xdbe3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0xdbeb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_816;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdbf1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xdbf6:
t_2413 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_817;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2413, 4bv64)), t_2413)), 2bv64)), (XOR_64((RSHIFT_64(t_2413, 4bv64)), t_2413)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2413, 4bv64)), t_2413)), 2bv64)), (XOR_64((RSHIFT_64(t_2413, 4bv64)), t_2413)))))[1:0]));
SF := t_2413[64:63];
ZF := bool2bv(0bv64 == t_2413);

label_0xdbf9:
if (bv2bool(ZF)) {
  goto label_0xdbfc;
}

label_0xdbfb:
assume false;

label_0xdbfc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0xdc04:
origDEST_2417 := RAX;
origCOUNT_2418 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), CF, LSHIFT_64(origDEST_2417, (MINUS_64(64bv64, origCOUNT_2418)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 1bv64)), origDEST_2417[64:63], unconstrained_818));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2418 == 0bv64)), AF, unconstrained_819);

label_0xdc08:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xdc0f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xdc13:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0xdc1b:
origDEST_2423 := RCX;
origCOUNT_2424 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), CF, LSHIFT_64(origDEST_2423, (MINUS_64(64bv64, origCOUNT_2424)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 1bv64)), origDEST_2423[64:63], unconstrained_820));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2424 == 0bv64)), AF, unconstrained_821);

label_0xdc1f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_822;
SF := unconstrained_823;
AF := unconstrained_824;
PF := unconstrained_825;

label_0xdc23:
if (bv2bool(CF)) {
  goto label_0xdc26;
}

label_0xdc25:
assume false;

label_0xdc26:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0xdc2e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 852bv64)));

label_0xdc35:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xdc37:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xdc3c:
t1_2429 := RAX[32:0];
t2_2430 := 4bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_2430));
CF := bool2bv(LT_32((RAX[32:0]), t1_2429));
OF := AND_1((bool2bv((t1_2429[32:31]) == (t2_2430[32:31]))), (XOR_1((t1_2429[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_2429)), t2_2430)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdc3f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 856bv64), RAX[32:0]);

label_0xdc46:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdc4e:
t1_2435 := RAX;
t2_2436 := 16bv64;
RAX := PLUS_64(RAX, t2_2436);
CF := bool2bv(LT_64(RAX, t1_2435));
OF := AND_1((bool2bv((t1_2435[64:63]) == (t2_2436[64:63]))), (XOR_1((t1_2435[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2435)), t2_2436)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdc52:
mem := STORE_LE_64(mem, PLUS_64(RSP, 512bv64), RAX);

label_0xdc5a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0xdc62:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_826;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdc68:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xdc6d:
t_2443 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_827;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2443, 4bv64)), t_2443)), 2bv64)), (XOR_64((RSHIFT_64(t_2443, 4bv64)), t_2443)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2443, 4bv64)), t_2443)), 2bv64)), (XOR_64((RSHIFT_64(t_2443, 4bv64)), t_2443)))))[1:0]));
SF := t_2443[64:63];
ZF := bool2bv(0bv64 == t_2443);

label_0xdc70:
if (bv2bool(ZF)) {
  goto label_0xdc73;
}

label_0xdc72:
assume false;

label_0xdc73:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0xdc7b:
origDEST_2447 := RAX;
origCOUNT_2448 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), CF, LSHIFT_64(origDEST_2447, (MINUS_64(64bv64, origCOUNT_2448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 1bv64)), origDEST_2447[64:63], unconstrained_828));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2448 == 0bv64)), AF, unconstrained_829);

label_0xdc7f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xdc86:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xdc8a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0xdc92:
origDEST_2453 := RCX;
origCOUNT_2454 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), CF, LSHIFT_64(origDEST_2453, (MINUS_64(64bv64, origCOUNT_2454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 1bv64)), origDEST_2453[64:63], unconstrained_830));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2454 == 0bv64)), AF, unconstrained_831);

label_0xdc96:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_832;
SF := unconstrained_833;
AF := unconstrained_834;
PF := unconstrained_835;

label_0xdc9a:
if (bv2bool(CF)) {
  goto label_0xdc9d;
}

label_0xdc9c:
assume false;

label_0xdc9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 512bv64));

label_0xdca5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 856bv64)));

label_0xdcac:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xdcae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdcb6:
t1_2459 := RAX;
t2_2460 := 1096bv64;
RAX := PLUS_64(RAX, t2_2460);
CF := bool2bv(LT_64(RAX, t1_2459));
OF := AND_1((bool2bv((t1_2459[64:63]) == (t2_2460[64:63]))), (XOR_1((t1_2459[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2459)), t2_2460)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdcbc:
RDX := RAX;

label_0xdcbf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdcc7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xdcca:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 56527bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xdccf"} true;
call arbitrary_func();

label_0xdccf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 860bv64), RAX[32:0]);

label_0xdcd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdcde:
t1_2465 := RAX;
t2_2466 := 64bv64;
RAX := PLUS_64(RAX, t2_2466);
CF := bool2bv(LT_64(RAX, t1_2465));
OF := AND_1((bool2bv((t1_2465[64:63]) == (t2_2466[64:63]))), (XOR_1((t1_2465[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2465)), t2_2466)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdce2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 520bv64), RAX);

label_0xdcea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0xdcf2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_836;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdcf8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xdcfd:
t_2473 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_837;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2473, 4bv64)), t_2473)), 2bv64)), (XOR_64((RSHIFT_64(t_2473, 4bv64)), t_2473)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2473, 4bv64)), t_2473)), 2bv64)), (XOR_64((RSHIFT_64(t_2473, 4bv64)), t_2473)))))[1:0]));
SF := t_2473[64:63];
ZF := bool2bv(0bv64 == t_2473);

label_0xdd00:
if (bv2bool(ZF)) {
  goto label_0xdd03;
}

label_0xdd02:
assume false;

label_0xdd03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0xdd0b:
origDEST_2477 := RAX;
origCOUNT_2478 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), CF, LSHIFT_64(origDEST_2477, (MINUS_64(64bv64, origCOUNT_2478)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 1bv64)), origDEST_2477[64:63], unconstrained_838));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2478 == 0bv64)), AF, unconstrained_839);

label_0xdd0f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xdd16:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xdd1a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0xdd22:
origDEST_2483 := RCX;
origCOUNT_2484 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), CF, LSHIFT_64(origDEST_2483, (MINUS_64(64bv64, origCOUNT_2484)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 1bv64)), origDEST_2483[64:63], unconstrained_840));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2484 == 0bv64)), AF, unconstrained_841);

label_0xdd26:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_842;
SF := unconstrained_843;
AF := unconstrained_844;
PF := unconstrained_845;

label_0xdd2a:
if (bv2bool(CF)) {
  goto label_0xdd2d;
}

label_0xdd2c:
assume false;

label_0xdd2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0xdd35:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 860bv64)));

label_0xdd3c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xdd3e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdd46:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 60bv64)));

label_0xdd49:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdd51:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 3160bv64));

label_0xdd58:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0xdd5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdd64:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 60bv64)));

label_0xdd67:
origDEST_2489 := RCX[32:0];
origCOUNT_2490 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), CF, LSHIFT_32(origDEST_2489, (MINUS_32(32bv32, origCOUNT_2490)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 1bv32)), origDEST_2489[32:31], unconstrained_846));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2490 == 0bv32)), AF, unconstrained_847);

label_0xdd69:
RCX := (0bv32 ++ RCX[32:0]);

label_0xdd6b:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdd73:
RDX := LOAD_LE_64(mem, PLUS_64(RDX, 3168bv64));

label_0xdd7a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RDX, RCX))));

label_0xdd7e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 864bv64), RCX[32:0]);

label_0xdd85:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xdd8d:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, 60bv64)));

label_0xdd90:
origDEST_2495 := RDX[32:0];
origCOUNT_2496 := AND_32(2bv32, (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ LSHIFT_32((RDX[32:0]), (AND_32(2bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), CF, RSHIFT_32(origDEST_2495, (MINUS_32(32bv32, origCOUNT_2496)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 1bv32)), XOR_1((RDX[32:0][32:31]), CF), unconstrained_848));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2496 == 0bv32)), AF, unconstrained_849);

label_0xdd93:
RDX := (0bv32 ++ AND_32((RDX[32:0]), 4bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_850;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0xdd96:
RCX := (0bv32 ++ (0bv24 ++ RDX[32:0][8:0]));

label_0xdd99:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 864bv64)));

label_0xdda0:
origDEST_2503 := RDX[32:0];
origCOUNT_2504 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RDX := (0bv32 ++ RSHIFT_32((RDX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), CF, LSHIFT_32(origDEST_2503, (MINUS_32(32bv32, origCOUNT_2504)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 1bv32)), origDEST_2503[32:31], unconstrained_851));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), SF, RDX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), ZF, bool2bv(0bv32 == (RDX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2504 == 0bv32)), AF, unconstrained_852);

label_0xdda2:
RCX := (0bv32 ++ RDX[32:0]);

label_0xdda4:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 15bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_853;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xdda7:
origDEST_2511 := RCX[32:0];
origCOUNT_2512 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ LSHIFT_32((RCX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), CF, RSHIFT_32(origDEST_2511, (MINUS_32(32bv32, origCOUNT_2512)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 1bv32)), XOR_1((RCX[32:0][32:31]), CF), unconstrained_854));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2512 == 0bv32)), AF, unconstrained_855);

label_0xddaa:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_856;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xddac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 868bv64), RAX[32:0]);

label_0xddb3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xddbb:
t1_2519 := RAX;
t2_2520 := 60bv64;
RAX := PLUS_64(RAX, t2_2520);
CF := bool2bv(LT_64(RAX, t1_2519));
OF := AND_1((bool2bv((t1_2519[64:63]) == (t2_2520[64:63]))), (XOR_1((t1_2519[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2519)), t2_2520)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xddbf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 528bv64), RAX);

label_0xddc7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0xddcf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_857;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xddd5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xddda:
t_2527 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_858;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2527, 4bv64)), t_2527)), 2bv64)), (XOR_64((RSHIFT_64(t_2527, 4bv64)), t_2527)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2527, 4bv64)), t_2527)), 2bv64)), (XOR_64((RSHIFT_64(t_2527, 4bv64)), t_2527)))))[1:0]));
SF := t_2527[64:63];
ZF := bool2bv(0bv64 == t_2527);

label_0xdddd:
if (bv2bool(ZF)) {
  goto label_0xdde0;
}

label_0xdddf:
assume false;

label_0xdde0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0xdde8:
origDEST_2531 := RAX;
origCOUNT_2532 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), CF, LSHIFT_64(origDEST_2531, (MINUS_64(64bv64, origCOUNT_2532)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 1bv64)), origDEST_2531[64:63], unconstrained_859));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2532 == 0bv64)), AF, unconstrained_860);

label_0xddec:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xddf3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xddf7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0xddff:
origDEST_2537 := RCX;
origCOUNT_2538 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), CF, LSHIFT_64(origDEST_2537, (MINUS_64(64bv64, origCOUNT_2538)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 1bv64)), origDEST_2537[64:63], unconstrained_861));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2538 == 0bv64)), AF, unconstrained_862);

label_0xde03:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_863;
SF := unconstrained_864;
AF := unconstrained_865;
PF := unconstrained_866;

label_0xde07:
if (bv2bool(CF)) {
  goto label_0xde0a;
}

label_0xde09:
assume false;

label_0xde0a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 528bv64));

label_0xde12:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 868bv64)));

label_0xde19:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xde1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xde23:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 1092bv64)));

label_0xde29:
t_2543 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_2543[32:31]) == (1bv32[32:31]))), (XOR_1((t_2543[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_2543)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xde2b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 872bv64), RAX[32:0]);

label_0xde32:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 992bv64));

label_0xde3a:
t1_2547 := RAX;
t2_2548 := 1092bv64;
RAX := PLUS_64(RAX, t2_2548);
CF := bool2bv(LT_64(RAX, t1_2547));
OF := AND_1((bool2bv((t1_2547[64:63]) == (t2_2548[64:63]))), (XOR_1((t1_2547[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_2547)), t2_2548)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xde40:
mem := STORE_LE_64(mem, PLUS_64(RSP, 536bv64), RAX);

label_0xde48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0xde50:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_867;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xde56:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xde5b:
t_2555 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_868;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2555, 4bv64)), t_2555)), 2bv64)), (XOR_64((RSHIFT_64(t_2555, 4bv64)), t_2555)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_2555, 4bv64)), t_2555)), 2bv64)), (XOR_64((RSHIFT_64(t_2555, 4bv64)), t_2555)))))[1:0]));
SF := t_2555[64:63];
ZF := bool2bv(0bv64 == t_2555);

label_0xde5e:
if (bv2bool(ZF)) {
  goto label_0xde61;
}

label_0xde60:
assume false;

label_0xde61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0xde69:
origDEST_2559 := RAX;
origCOUNT_2560 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), CF, LSHIFT_64(origDEST_2559, (MINUS_64(64bv64, origCOUNT_2560)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 1bv64)), origDEST_2559[64:63], unconstrained_869));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2560 == 0bv64)), AF, unconstrained_870);

label_0xde6d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xde74:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xde78:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0xde80:
origDEST_2565 := RCX;
origCOUNT_2566 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), CF, LSHIFT_64(origDEST_2565, (MINUS_64(64bv64, origCOUNT_2566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 1bv64)), origDEST_2565[64:63], unconstrained_871));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_2566 == 0bv64)), AF, unconstrained_872);

label_0xde84:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_873;
SF := unconstrained_874;
AF := unconstrained_875;
PF := unconstrained_876;

label_0xde88:
if (bv2bool(CF)) {
  goto label_0xde8b;
}

label_0xde8a:
assume false;

label_0xde8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 536bv64));

label_0xde93:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 872bv64)));

label_0xde9a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xde9c:
goto label_0xce0a;

label_0xdea1:
t1_2571 := RSP;
t2_2572 := 984bv64;
RSP := PLUS_64(RSP, t2_2572);
CF := bool2bv(LT_64(RSP, t1_2571));
OF := AND_1((bool2bv((t1_2571[64:63]) == (t2_2572[64:63]))), (XOR_1((t1_2571[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_2571)), t2_2572)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xdea8:

ra_2577 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_1004,origCOUNT_1010,origCOUNT_1032,origCOUNT_1038,origCOUNT_106,origCOUNT_1066,origCOUNT_1072,origCOUNT_1102,origCOUNT_1108,origCOUNT_112,origCOUNT_1120,origCOUNT_1126,origCOUNT_1134,origCOUNT_1142,origCOUNT_1162,origCOUNT_1168,origCOUNT_1178,origCOUNT_1202,origCOUNT_1208,origCOUNT_1230,origCOUNT_1236,origCOUNT_1258,origCOUNT_1264,origCOUNT_1286,origCOUNT_1292,origCOUNT_1320,origCOUNT_1326,origCOUNT_134,origCOUNT_1350,origCOUNT_1356,origCOUNT_1380,origCOUNT_1386,origCOUNT_1392,origCOUNT_1398,origCOUNT_140,origCOUNT_1406,origCOUNT_1414,origCOUNT_1434,origCOUNT_1440,origCOUNT_1450,origCOUNT_1474,origCOUNT_1480,origCOUNT_1502,origCOUNT_1508,origCOUNT_1530,origCOUNT_1536,origCOUNT_1558,origCOUNT_1564,origCOUNT_1588,origCOUNT_1594,origCOUNT_1616,origCOUNT_162,origCOUNT_1622,origCOUNT_1656,origCOUNT_1662,origCOUNT_1668,origCOUNT_1674,origCOUNT_168,origCOUNT_1696,origCOUNT_1702,origCOUNT_1724,origCOUNT_1730,origCOUNT_1752,origCOUNT_1758,origCOUNT_1780,origCOUNT_1786,origCOUNT_1808,origCOUNT_1814,origCOUNT_1840,origCOUNT_1846,origCOUNT_1880,origCOUNT_1886,origCOUNT_190,origCOUNT_1910,origCOUNT_1916,origCOUNT_1928,origCOUNT_1934,origCOUNT_1942,origCOUNT_1950,origCOUNT_196,origCOUNT_1970,origCOUNT_1976,origCOUNT_1998,origCOUNT_2004,origCOUNT_2034,origCOUNT_2040,origCOUNT_2058,origCOUNT_2064,origCOUNT_2076,origCOUNT_2082,origCOUNT_2090,origCOUNT_2098,origCOUNT_2118,origCOUNT_2124,origCOUNT_2146,origCOUNT_2152,origCOUNT_2182,origCOUNT_2188,origCOUNT_2206,origCOUNT_2212,origCOUNT_222,origCOUNT_2224,origCOUNT_2230,origCOUNT_2238,origCOUNT_2246,origCOUNT_2266,origCOUNT_2272,origCOUNT_228,origCOUNT_2294,origCOUNT_2300,origCOUNT_2330,origCOUNT_2336,origCOUNT_2348,origCOUNT_2354,origCOUNT_2362,origCOUNT_2370,origCOUNT_2390,origCOUNT_2396,origCOUNT_2418,origCOUNT_2424,origCOUNT_2448,origCOUNT_2454,origCOUNT_2478,origCOUNT_2484,origCOUNT_2490,origCOUNT_2496,origCOUNT_2504,origCOUNT_2512,origCOUNT_2532,origCOUNT_2538,origCOUNT_2560,origCOUNT_2566,origCOUNT_262,origCOUNT_268,origCOUNT_292,origCOUNT_298,origCOUNT_310,origCOUNT_316,origCOUNT_324,origCOUNT_332,origCOUNT_352,origCOUNT_358,origCOUNT_368,origCOUNT_38,origCOUNT_392,origCOUNT_398,origCOUNT_420,origCOUNT_426,origCOUNT_44,origCOUNT_448,origCOUNT_454,origCOUNT_476,origCOUNT_482,origCOUNT_50,origCOUNT_510,origCOUNT_516,origCOUNT_546,origCOUNT_552,origCOUNT_56,origCOUNT_570,origCOUNT_576,origCOUNT_588,origCOUNT_594,origCOUNT_602,origCOUNT_610,origCOUNT_630,origCOUNT_636,origCOUNT_646,origCOUNT_670,origCOUNT_676,origCOUNT_698,origCOUNT_704,origCOUNT_726,origCOUNT_732,origCOUNT_754,origCOUNT_760,origCOUNT_78,origCOUNT_788,origCOUNT_794,origCOUNT_824,origCOUNT_830,origCOUNT_84,origCOUNT_848,origCOUNT_854,origCOUNT_866,origCOUNT_872,origCOUNT_880,origCOUNT_888,origCOUNT_908,origCOUNT_914,origCOUNT_924,origCOUNT_948,origCOUNT_954,origCOUNT_976,origCOUNT_982,origDEST_1003,origDEST_1009,origDEST_1031,origDEST_1037,origDEST_105,origDEST_1065,origDEST_1071,origDEST_1101,origDEST_1107,origDEST_111,origDEST_1119,origDEST_1125,origDEST_1133,origDEST_1141,origDEST_1161,origDEST_1167,origDEST_1177,origDEST_1201,origDEST_1207,origDEST_1229,origDEST_1235,origDEST_1257,origDEST_1263,origDEST_1285,origDEST_1291,origDEST_1319,origDEST_1325,origDEST_133,origDEST_1349,origDEST_1355,origDEST_1379,origDEST_1385,origDEST_139,origDEST_1391,origDEST_1397,origDEST_1405,origDEST_1413,origDEST_1433,origDEST_1439,origDEST_1449,origDEST_1473,origDEST_1479,origDEST_1501,origDEST_1507,origDEST_1529,origDEST_1535,origDEST_1557,origDEST_1563,origDEST_1587,origDEST_1593,origDEST_161,origDEST_1615,origDEST_1621,origDEST_1655,origDEST_1661,origDEST_1667,origDEST_167,origDEST_1673,origDEST_1695,origDEST_1701,origDEST_1723,origDEST_1729,origDEST_1751,origDEST_1757,origDEST_1779,origDEST_1785,origDEST_1807,origDEST_1813,origDEST_1839,origDEST_1845,origDEST_1879,origDEST_1885,origDEST_189,origDEST_1909,origDEST_1915,origDEST_1927,origDEST_1933,origDEST_1941,origDEST_1949,origDEST_195,origDEST_1969,origDEST_1975,origDEST_1997,origDEST_2003,origDEST_2033,origDEST_2039,origDEST_2057,origDEST_2063,origDEST_2075,origDEST_2081,origDEST_2089,origDEST_2097,origDEST_2117,origDEST_2123,origDEST_2145,origDEST_2151,origDEST_2181,origDEST_2187,origDEST_2205,origDEST_221,origDEST_2211,origDEST_2223,origDEST_2229,origDEST_2237,origDEST_2245,origDEST_2265,origDEST_227,origDEST_2271,origDEST_2293,origDEST_2299,origDEST_2329,origDEST_2335,origDEST_2347,origDEST_2353,origDEST_2361,origDEST_2369,origDEST_2389,origDEST_2395,origDEST_2417,origDEST_2423,origDEST_2447,origDEST_2453,origDEST_2477,origDEST_2483,origDEST_2489,origDEST_2495,origDEST_2503,origDEST_2511,origDEST_2531,origDEST_2537,origDEST_2559,origDEST_2565,origDEST_261,origDEST_267,origDEST_291,origDEST_297,origDEST_309,origDEST_315,origDEST_323,origDEST_331,origDEST_351,origDEST_357,origDEST_367,origDEST_37,origDEST_391,origDEST_397,origDEST_419,origDEST_425,origDEST_43,origDEST_447,origDEST_453,origDEST_475,origDEST_481,origDEST_49,origDEST_509,origDEST_515,origDEST_545,origDEST_55,origDEST_551,origDEST_569,origDEST_575,origDEST_587,origDEST_593,origDEST_601,origDEST_609,origDEST_629,origDEST_635,origDEST_645,origDEST_669,origDEST_675,origDEST_697,origDEST_703,origDEST_725,origDEST_731,origDEST_753,origDEST_759,origDEST_77,origDEST_787,origDEST_793,origDEST_823,origDEST_829,origDEST_83,origDEST_847,origDEST_853,origDEST_865,origDEST_871,origDEST_879,origDEST_887,origDEST_907,origDEST_913,origDEST_923,origDEST_947,origDEST_953,origDEST_975,origDEST_981,ra_2577,t1_1019,t1_1053,t1_1089,t1_1113,t1_1149,t1_1183,t1_1189,t1_121,t1_1217,t1_1245,t1_1273,t1_1307,t1_1331,t1_1337,t1_1361,t1_1367,t1_1421,t1_1455,t1_1461,t1_1489,t1_149,t1_1517,t1_1545,t1_1575,t1_1603,t1_1643,t1_1683,t1_1711,t1_1739,t1_1767,t1_177,t1_1795,t1_1827,t1_1867,t1_1891,t1_1897,t1_1921,t1_1957,t1_1985,t1_2021,t1_2045,t1_2069,t1_209,t1_2105,t1_2133,t1_2169,t1_2193,t1_2217,t1_2253,t1_2281,t1_2317,t1_2341,t1_2377,t1_2405,t1_2429,t1_2435,t1_2459,t1_2465,t1_249,t1_25,t1_2519,t1_2547,t1_2571,t1_273,t1_279,t1_303,t1_339,t1_373,t1_379,t1_407,t1_435,t1_463,t1_497,t1_533,t1_557,t1_581,t1_617,t1_65,t1_651,t1_657,t1_685,t1_713,t1_741,t1_775,t1_811,t1_835,t1_859,t1_895,t1_929,t1_93,t1_935,t1_963,t1_991,t2_1020,t2_1054,t2_1090,t2_1114,t2_1150,t2_1184,t2_1190,t2_1218,t2_122,t2_1246,t2_1274,t2_1308,t2_1332,t2_1338,t2_1362,t2_1368,t2_1422,t2_1456,t2_1462,t2_1490,t2_150,t2_1518,t2_1546,t2_1576,t2_1604,t2_1644,t2_1684,t2_1712,t2_1740,t2_1768,t2_178,t2_1796,t2_1828,t2_1868,t2_1892,t2_1898,t2_1922,t2_1958,t2_1986,t2_2022,t2_2046,t2_2070,t2_210,t2_2106,t2_2134,t2_2170,t2_2194,t2_2218,t2_2254,t2_2282,t2_2318,t2_2342,t2_2378,t2_2406,t2_2430,t2_2436,t2_2460,t2_2466,t2_250,t2_2520,t2_2548,t2_2572,t2_26,t2_274,t2_280,t2_304,t2_340,t2_374,t2_380,t2_408,t2_436,t2_464,t2_498,t2_534,t2_558,t2_582,t2_618,t2_652,t2_658,t2_66,t2_686,t2_714,t2_742,t2_776,t2_812,t2_836,t2_860,t2_896,t2_930,t2_936,t2_94,t2_964,t2_992,t_1,t_101,t_1015,t_1027,t_1043,t_1049,t_1061,t_1077,t_1081,t_1085,t_1097,t_1157,t_117,t_1173,t_1197,t_1213,t_1225,t_1241,t_1253,t_1269,t_1281,t_129,t_1297,t_13,t_1303,t_1315,t_1345,t_1375,t_1429,t_1445,t_145,t_1469,t_1485,t_1497,t_1513,t_1525,t_1541,t_1553,t_1569,t_157,t_1583,t_1599,t_1611,t_1627,t_1631,t_1635,t_1639,t_1651,t_1691,t_17,t_1707,t_1719,t_173,t_1735,t_1747,t_1763,t_1775,t_1791,t_1803,t_1819,t_1823,t_1835,t_185,t_1851,t_1855,t_1859,t_1863,t_1875,t_1905,t_1965,t_1981,t_1993,t_2009,t_201,t_2013,t_2017,t_2029,t_205,t_2053,t_21,t_2113,t_2129,t_2141,t_2157,t_2161,t_2165,t_217,t_2177,t_2201,t_2261,t_2277,t_2289,t_2305,t_2309,t_2313,t_2325,t_233,t_237,t_2385,t_2401,t_241,t_2413,t_2443,t_245,t_2473,t_2527,t_2543,t_2555,t_257,t_287,t_33,t_347,t_363,t_387,t_403,t_415,t_431,t_443,t_459,t_471,t_487,t_493,t_5,t_505,t_521,t_525,t_529,t_541,t_565,t_625,t_641,t_665,t_681,t_693,t_709,t_721,t_73,t_737,t_749,t_765,t_771,t_783,t_799,t_803,t_807,t_819,t_843,t_89,t_9,t_903,t_919,t_943,t_959,t_971,t_987,t_999;

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
const unconstrained_345: bv1;
const unconstrained_346: bv1;
const unconstrained_347: bv1;
const unconstrained_348: bv1;
const unconstrained_349: bv1;
const unconstrained_35: bv1;
const unconstrained_350: bv1;
const unconstrained_351: bv1;
const unconstrained_352: bv1;
const unconstrained_353: bv1;
const unconstrained_354: bv1;
const unconstrained_355: bv1;
const unconstrained_356: bv1;
const unconstrained_357: bv1;
const unconstrained_358: bv1;
const unconstrained_359: bv1;
const unconstrained_36: bv1;
const unconstrained_360: bv1;
const unconstrained_361: bv1;
const unconstrained_362: bv1;
const unconstrained_363: bv1;
const unconstrained_364: bv1;
const unconstrained_365: bv1;
const unconstrained_366: bv1;
const unconstrained_367: bv1;
const unconstrained_368: bv1;
const unconstrained_369: bv1;
const unconstrained_37: bv1;
const unconstrained_370: bv1;
const unconstrained_371: bv1;
const unconstrained_372: bv1;
const unconstrained_373: bv1;
const unconstrained_374: bv1;
const unconstrained_375: bv1;
const unconstrained_376: bv1;
const unconstrained_377: bv1;
const unconstrained_378: bv1;
const unconstrained_379: bv1;
const unconstrained_38: bv1;
const unconstrained_380: bv1;
const unconstrained_381: bv1;
const unconstrained_382: bv1;
const unconstrained_383: bv1;
const unconstrained_384: bv1;
const unconstrained_385: bv1;
const unconstrained_386: bv1;
const unconstrained_387: bv1;
const unconstrained_388: bv1;
const unconstrained_389: bv1;
const unconstrained_39: bv1;
const unconstrained_390: bv1;
const unconstrained_391: bv1;
const unconstrained_392: bv1;
const unconstrained_393: bv1;
const unconstrained_394: bv1;
const unconstrained_395: bv1;
const unconstrained_396: bv1;
const unconstrained_397: bv1;
const unconstrained_398: bv1;
const unconstrained_399: bv1;
const unconstrained_4: bv1;
const unconstrained_40: bv1;
const unconstrained_400: bv1;
const unconstrained_401: bv1;
const unconstrained_402: bv1;
const unconstrained_403: bv1;
const unconstrained_404: bv1;
const unconstrained_405: bv1;
const unconstrained_406: bv1;
const unconstrained_407: bv1;
const unconstrained_408: bv1;
const unconstrained_409: bv1;
const unconstrained_41: bv1;
const unconstrained_410: bv1;
const unconstrained_411: bv1;
const unconstrained_412: bv1;
const unconstrained_413: bv1;
const unconstrained_414: bv1;
const unconstrained_415: bv1;
const unconstrained_416: bv1;
const unconstrained_417: bv1;
const unconstrained_418: bv1;
const unconstrained_419: bv1;
const unconstrained_42: bv1;
const unconstrained_420: bv1;
const unconstrained_421: bv1;
const unconstrained_422: bv1;
const unconstrained_423: bv1;
const unconstrained_424: bv1;
const unconstrained_425: bv1;
const unconstrained_426: bv1;
const unconstrained_427: bv1;
const unconstrained_428: bv1;
const unconstrained_429: bv1;
const unconstrained_43: bv1;
const unconstrained_430: bv1;
const unconstrained_431: bv1;
const unconstrained_432: bv1;
const unconstrained_433: bv1;
const unconstrained_434: bv1;
const unconstrained_435: bv1;
const unconstrained_436: bv1;
const unconstrained_437: bv1;
const unconstrained_438: bv1;
const unconstrained_439: bv1;
const unconstrained_44: bv1;
const unconstrained_440: bv1;
const unconstrained_441: bv1;
const unconstrained_442: bv1;
const unconstrained_443: bv1;
const unconstrained_444: bv1;
const unconstrained_445: bv1;
const unconstrained_446: bv1;
const unconstrained_447: bv1;
const unconstrained_448: bv1;
const unconstrained_449: bv1;
const unconstrained_45: bv1;
const unconstrained_450: bv1;
const unconstrained_451: bv1;
const unconstrained_452: bv1;
const unconstrained_453: bv1;
const unconstrained_454: bv1;
const unconstrained_455: bv1;
const unconstrained_456: bv1;
const unconstrained_457: bv1;
const unconstrained_458: bv1;
const unconstrained_459: bv1;
const unconstrained_46: bv1;
const unconstrained_460: bv1;
const unconstrained_461: bv1;
const unconstrained_462: bv1;
const unconstrained_463: bv1;
const unconstrained_464: bv1;
const unconstrained_465: bv1;
const unconstrained_466: bv1;
const unconstrained_467: bv1;
const unconstrained_468: bv1;
const unconstrained_469: bv1;
const unconstrained_47: bv1;
const unconstrained_470: bv1;
const unconstrained_471: bv1;
const unconstrained_472: bv1;
const unconstrained_473: bv1;
const unconstrained_474: bv1;
const unconstrained_475: bv1;
const unconstrained_476: bv1;
const unconstrained_477: bv1;
const unconstrained_478: bv1;
const unconstrained_479: bv1;
const unconstrained_48: bv1;
const unconstrained_480: bv1;
const unconstrained_481: bv1;
const unconstrained_482: bv1;
const unconstrained_483: bv1;
const unconstrained_484: bv1;
const unconstrained_485: bv1;
const unconstrained_486: bv1;
const unconstrained_487: bv1;
const unconstrained_488: bv1;
const unconstrained_489: bv1;
const unconstrained_49: bv1;
const unconstrained_490: bv1;
const unconstrained_491: bv1;
const unconstrained_492: bv1;
const unconstrained_493: bv1;
const unconstrained_494: bv1;
const unconstrained_495: bv1;
const unconstrained_496: bv1;
const unconstrained_497: bv1;
const unconstrained_498: bv1;
const unconstrained_499: bv1;
const unconstrained_5: bv1;
const unconstrained_50: bv1;
const unconstrained_500: bv1;
const unconstrained_501: bv1;
const unconstrained_502: bv1;
const unconstrained_503: bv1;
const unconstrained_504: bv1;
const unconstrained_505: bv1;
const unconstrained_506: bv1;
const unconstrained_507: bv1;
const unconstrained_508: bv1;
const unconstrained_509: bv1;
const unconstrained_51: bv1;
const unconstrained_510: bv1;
const unconstrained_511: bv1;
const unconstrained_512: bv1;
const unconstrained_513: bv1;
const unconstrained_514: bv1;
const unconstrained_515: bv1;
const unconstrained_516: bv1;
const unconstrained_517: bv1;
const unconstrained_518: bv1;
const unconstrained_519: bv1;
const unconstrained_52: bv1;
const unconstrained_520: bv1;
const unconstrained_521: bv1;
const unconstrained_522: bv1;
const unconstrained_523: bv1;
const unconstrained_524: bv1;
const unconstrained_525: bv1;
const unconstrained_526: bv1;
const unconstrained_527: bv1;
const unconstrained_528: bv1;
const unconstrained_529: bv1;
const unconstrained_53: bv1;
const unconstrained_530: bv1;
const unconstrained_531: bv1;
const unconstrained_532: bv1;
const unconstrained_533: bv1;
const unconstrained_534: bv1;
const unconstrained_535: bv1;
const unconstrained_536: bv1;
const unconstrained_537: bv1;
const unconstrained_538: bv1;
const unconstrained_539: bv1;
const unconstrained_54: bv1;
const unconstrained_540: bv1;
const unconstrained_541: bv1;
const unconstrained_542: bv1;
const unconstrained_543: bv1;
const unconstrained_544: bv1;
const unconstrained_545: bv1;
const unconstrained_546: bv1;
const unconstrained_547: bv1;
const unconstrained_548: bv1;
const unconstrained_549: bv1;
const unconstrained_55: bv1;
const unconstrained_550: bv1;
const unconstrained_551: bv1;
const unconstrained_552: bv1;
const unconstrained_553: bv1;
const unconstrained_554: bv1;
const unconstrained_555: bv1;
const unconstrained_556: bv1;
const unconstrained_557: bv1;
const unconstrained_558: bv1;
const unconstrained_559: bv1;
const unconstrained_56: bv1;
const unconstrained_560: bv1;
const unconstrained_561: bv1;
const unconstrained_562: bv1;
const unconstrained_563: bv1;
const unconstrained_564: bv1;
const unconstrained_565: bv1;
const unconstrained_566: bv1;
const unconstrained_567: bv1;
const unconstrained_568: bv1;
const unconstrained_569: bv1;
const unconstrained_57: bv1;
const unconstrained_570: bv1;
const unconstrained_571: bv1;
const unconstrained_572: bv1;
const unconstrained_573: bv1;
const unconstrained_574: bv1;
const unconstrained_575: bv1;
const unconstrained_576: bv1;
const unconstrained_577: bv1;
const unconstrained_578: bv1;
const unconstrained_579: bv1;
const unconstrained_58: bv1;
const unconstrained_580: bv1;
const unconstrained_581: bv1;
const unconstrained_582: bv1;
const unconstrained_583: bv1;
const unconstrained_584: bv1;
const unconstrained_585: bv1;
const unconstrained_586: bv1;
const unconstrained_587: bv1;
const unconstrained_588: bv1;
const unconstrained_589: bv1;
const unconstrained_59: bv1;
const unconstrained_590: bv1;
const unconstrained_591: bv1;
const unconstrained_592: bv1;
const unconstrained_593: bv1;
const unconstrained_594: bv1;
const unconstrained_595: bv1;
const unconstrained_596: bv1;
const unconstrained_597: bv1;
const unconstrained_598: bv1;
const unconstrained_599: bv1;
const unconstrained_6: bv1;
const unconstrained_60: bv1;
const unconstrained_600: bv1;
const unconstrained_601: bv1;
const unconstrained_602: bv1;
const unconstrained_603: bv1;
const unconstrained_604: bv1;
const unconstrained_605: bv1;
const unconstrained_606: bv1;
const unconstrained_607: bv1;
const unconstrained_608: bv1;
const unconstrained_609: bv1;
const unconstrained_61: bv1;
const unconstrained_610: bv1;
const unconstrained_611: bv1;
const unconstrained_612: bv1;
const unconstrained_613: bv1;
const unconstrained_614: bv1;
const unconstrained_615: bv1;
const unconstrained_616: bv1;
const unconstrained_617: bv1;
const unconstrained_618: bv1;
const unconstrained_619: bv1;
const unconstrained_62: bv1;
const unconstrained_620: bv1;
const unconstrained_621: bv1;
const unconstrained_622: bv1;
const unconstrained_623: bv1;
const unconstrained_624: bv1;
const unconstrained_625: bv1;
const unconstrained_626: bv1;
const unconstrained_627: bv1;
const unconstrained_628: bv1;
const unconstrained_629: bv1;
const unconstrained_63: bv1;
const unconstrained_630: bv1;
const unconstrained_631: bv1;
const unconstrained_632: bv1;
const unconstrained_633: bv1;
const unconstrained_634: bv1;
const unconstrained_635: bv1;
const unconstrained_636: bv1;
const unconstrained_637: bv1;
const unconstrained_638: bv1;
const unconstrained_639: bv1;
const unconstrained_64: bv1;
const unconstrained_640: bv1;
const unconstrained_641: bv1;
const unconstrained_642: bv1;
const unconstrained_643: bv1;
const unconstrained_644: bv1;
const unconstrained_645: bv1;
const unconstrained_646: bv1;
const unconstrained_647: bv1;
const unconstrained_648: bv1;
const unconstrained_649: bv1;
const unconstrained_65: bv1;
const unconstrained_650: bv1;
const unconstrained_651: bv1;
const unconstrained_652: bv1;
const unconstrained_653: bv1;
const unconstrained_654: bv1;
const unconstrained_655: bv1;
const unconstrained_656: bv1;
const unconstrained_657: bv1;
const unconstrained_658: bv1;
const unconstrained_659: bv1;
const unconstrained_66: bv1;
const unconstrained_660: bv1;
const unconstrained_661: bv1;
const unconstrained_662: bv1;
const unconstrained_663: bv1;
const unconstrained_664: bv1;
const unconstrained_665: bv1;
const unconstrained_666: bv1;
const unconstrained_667: bv1;
const unconstrained_668: bv1;
const unconstrained_669: bv1;
const unconstrained_67: bv1;
const unconstrained_670: bv1;
const unconstrained_671: bv1;
const unconstrained_672: bv1;
const unconstrained_673: bv1;
const unconstrained_674: bv1;
const unconstrained_675: bv1;
const unconstrained_676: bv1;
const unconstrained_677: bv1;
const unconstrained_678: bv1;
const unconstrained_679: bv1;
const unconstrained_68: bv1;
const unconstrained_680: bv1;
const unconstrained_681: bv1;
const unconstrained_682: bv1;
const unconstrained_683: bv1;
const unconstrained_684: bv1;
const unconstrained_685: bv1;
const unconstrained_686: bv1;
const unconstrained_687: bv1;
const unconstrained_688: bv1;
const unconstrained_689: bv1;
const unconstrained_69: bv1;
const unconstrained_690: bv1;
const unconstrained_691: bv1;
const unconstrained_692: bv1;
const unconstrained_693: bv1;
const unconstrained_694: bv1;
const unconstrained_695: bv1;
const unconstrained_696: bv1;
const unconstrained_697: bv1;
const unconstrained_698: bv1;
const unconstrained_699: bv1;
const unconstrained_7: bv1;
const unconstrained_70: bv1;
const unconstrained_700: bv1;
const unconstrained_701: bv1;
const unconstrained_702: bv1;
const unconstrained_703: bv1;
const unconstrained_704: bv1;
const unconstrained_705: bv1;
const unconstrained_706: bv1;
const unconstrained_707: bv1;
const unconstrained_708: bv1;
const unconstrained_709: bv1;
const unconstrained_71: bv1;
const unconstrained_710: bv1;
const unconstrained_711: bv1;
const unconstrained_712: bv1;
const unconstrained_713: bv1;
const unconstrained_714: bv1;
const unconstrained_715: bv1;
const unconstrained_716: bv1;
const unconstrained_717: bv1;
const unconstrained_718: bv1;
const unconstrained_719: bv1;
const unconstrained_72: bv1;
const unconstrained_720: bv1;
const unconstrained_721: bv1;
const unconstrained_722: bv1;
const unconstrained_723: bv1;
const unconstrained_724: bv1;
const unconstrained_725: bv1;
const unconstrained_726: bv1;
const unconstrained_727: bv1;
const unconstrained_728: bv1;
const unconstrained_729: bv1;
const unconstrained_73: bv1;
const unconstrained_730: bv1;
const unconstrained_731: bv1;
const unconstrained_732: bv1;
const unconstrained_733: bv1;
const unconstrained_734: bv1;
const unconstrained_735: bv1;
const unconstrained_736: bv1;
const unconstrained_737: bv1;
const unconstrained_738: bv1;
const unconstrained_739: bv1;
const unconstrained_74: bv1;
const unconstrained_740: bv1;
const unconstrained_741: bv1;
const unconstrained_742: bv1;
const unconstrained_743: bv1;
const unconstrained_744: bv1;
const unconstrained_745: bv1;
const unconstrained_746: bv1;
const unconstrained_747: bv1;
const unconstrained_748: bv1;
const unconstrained_749: bv1;
const unconstrained_75: bv1;
const unconstrained_750: bv1;
const unconstrained_751: bv1;
const unconstrained_752: bv1;
const unconstrained_753: bv1;
const unconstrained_754: bv1;
const unconstrained_755: bv1;
const unconstrained_756: bv1;
const unconstrained_757: bv1;
const unconstrained_758: bv1;
const unconstrained_759: bv1;
const unconstrained_76: bv1;
const unconstrained_760: bv1;
const unconstrained_761: bv1;
const unconstrained_762: bv1;
const unconstrained_763: bv1;
const unconstrained_764: bv1;
const unconstrained_765: bv1;
const unconstrained_766: bv1;
const unconstrained_767: bv1;
const unconstrained_768: bv1;
const unconstrained_769: bv1;
const unconstrained_77: bv1;
const unconstrained_770: bv1;
const unconstrained_771: bv1;
const unconstrained_772: bv1;
const unconstrained_773: bv1;
const unconstrained_774: bv1;
const unconstrained_775: bv1;
const unconstrained_776: bv1;
const unconstrained_777: bv1;
const unconstrained_778: bv1;
const unconstrained_779: bv1;
const unconstrained_78: bv1;
const unconstrained_780: bv1;
const unconstrained_781: bv1;
const unconstrained_782: bv1;
const unconstrained_783: bv1;
const unconstrained_784: bv1;
const unconstrained_785: bv1;
const unconstrained_786: bv1;
const unconstrained_787: bv1;
const unconstrained_788: bv1;
const unconstrained_789: bv1;
const unconstrained_79: bv1;
const unconstrained_790: bv1;
const unconstrained_791: bv1;
const unconstrained_792: bv1;
const unconstrained_793: bv1;
const unconstrained_794: bv1;
const unconstrained_795: bv1;
const unconstrained_796: bv1;
const unconstrained_797: bv1;
const unconstrained_798: bv1;
const unconstrained_799: bv1;
const unconstrained_8: bv1;
const unconstrained_80: bv1;
const unconstrained_800: bv1;
const unconstrained_801: bv1;
const unconstrained_802: bv1;
const unconstrained_803: bv1;
const unconstrained_804: bv1;
const unconstrained_805: bv1;
const unconstrained_806: bv1;
const unconstrained_807: bv1;
const unconstrained_808: bv1;
const unconstrained_809: bv1;
const unconstrained_81: bv1;
const unconstrained_810: bv1;
const unconstrained_811: bv1;
const unconstrained_812: bv1;
const unconstrained_813: bv1;
const unconstrained_814: bv1;
const unconstrained_815: bv1;
const unconstrained_816: bv1;
const unconstrained_817: bv1;
const unconstrained_818: bv1;
const unconstrained_819: bv1;
const unconstrained_82: bv1;
const unconstrained_820: bv1;
const unconstrained_821: bv1;
const unconstrained_822: bv1;
const unconstrained_823: bv1;
const unconstrained_824: bv1;
const unconstrained_825: bv1;
const unconstrained_826: bv1;
const unconstrained_827: bv1;
const unconstrained_828: bv1;
const unconstrained_829: bv1;
const unconstrained_83: bv1;
const unconstrained_830: bv1;
const unconstrained_831: bv1;
const unconstrained_832: bv1;
const unconstrained_833: bv1;
const unconstrained_834: bv1;
const unconstrained_835: bv1;
const unconstrained_836: bv1;
const unconstrained_837: bv1;
const unconstrained_838: bv1;
const unconstrained_839: bv1;
const unconstrained_84: bv1;
const unconstrained_840: bv1;
const unconstrained_841: bv1;
const unconstrained_842: bv1;
const unconstrained_843: bv1;
const unconstrained_844: bv1;
const unconstrained_845: bv1;
const unconstrained_846: bv1;
const unconstrained_847: bv1;
const unconstrained_848: bv1;
const unconstrained_849: bv1;
const unconstrained_85: bv1;
const unconstrained_850: bv1;
const unconstrained_851: bv1;
const unconstrained_852: bv1;
const unconstrained_853: bv1;
const unconstrained_854: bv1;
const unconstrained_855: bv1;
const unconstrained_856: bv1;
const unconstrained_857: bv1;
const unconstrained_858: bv1;
const unconstrained_859: bv1;
const unconstrained_86: bv1;
const unconstrained_860: bv1;
const unconstrained_861: bv1;
const unconstrained_862: bv1;
const unconstrained_863: bv1;
const unconstrained_864: bv1;
const unconstrained_865: bv1;
const unconstrained_866: bv1;
const unconstrained_867: bv1;
const unconstrained_868: bv1;
const unconstrained_869: bv1;
const unconstrained_87: bv1;
const unconstrained_870: bv1;
const unconstrained_871: bv1;
const unconstrained_872: bv1;
const unconstrained_873: bv1;
const unconstrained_874: bv1;
const unconstrained_875: bv1;
const unconstrained_876: bv1;
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
var origCOUNT_1004: bv64;
var origCOUNT_1010: bv64;
var origCOUNT_1032: bv64;
var origCOUNT_1038: bv64;
var origCOUNT_106: bv64;
var origCOUNT_1066: bv64;
var origCOUNT_1072: bv64;
var origCOUNT_1102: bv64;
var origCOUNT_1108: bv64;
var origCOUNT_112: bv64;
var origCOUNT_1120: bv32;
var origCOUNT_1126: bv32;
var origCOUNT_1134: bv32;
var origCOUNT_1142: bv32;
var origCOUNT_1162: bv64;
var origCOUNT_1168: bv64;
var origCOUNT_1178: bv64;
var origCOUNT_1202: bv64;
var origCOUNT_1208: bv64;
var origCOUNT_1230: bv64;
var origCOUNT_1236: bv64;
var origCOUNT_1258: bv64;
var origCOUNT_1264: bv64;
var origCOUNT_1286: bv64;
var origCOUNT_1292: bv64;
var origCOUNT_1320: bv64;
var origCOUNT_1326: bv64;
var origCOUNT_134: bv64;
var origCOUNT_1350: bv64;
var origCOUNT_1356: bv64;
var origCOUNT_1380: bv64;
var origCOUNT_1386: bv64;
var origCOUNT_1392: bv32;
var origCOUNT_1398: bv32;
var origCOUNT_140: bv64;
var origCOUNT_1406: bv32;
var origCOUNT_1414: bv32;
var origCOUNT_1434: bv64;
var origCOUNT_1440: bv64;
var origCOUNT_1450: bv64;
var origCOUNT_1474: bv64;
var origCOUNT_1480: bv64;
var origCOUNT_1502: bv64;
var origCOUNT_1508: bv64;
var origCOUNT_1530: bv64;
var origCOUNT_1536: bv64;
var origCOUNT_1558: bv64;
var origCOUNT_1564: bv64;
var origCOUNT_1588: bv64;
var origCOUNT_1594: bv64;
var origCOUNT_1616: bv64;
var origCOUNT_162: bv64;
var origCOUNT_1622: bv64;
var origCOUNT_1656: bv64;
var origCOUNT_1662: bv64;
var origCOUNT_1668: bv32;
var origCOUNT_1674: bv32;
var origCOUNT_168: bv64;
var origCOUNT_1696: bv64;
var origCOUNT_1702: bv64;
var origCOUNT_1724: bv64;
var origCOUNT_1730: bv64;
var origCOUNT_1752: bv64;
var origCOUNT_1758: bv64;
var origCOUNT_1780: bv64;
var origCOUNT_1786: bv64;
var origCOUNT_1808: bv64;
var origCOUNT_1814: bv64;
var origCOUNT_1840: bv64;
var origCOUNT_1846: bv64;
var origCOUNT_1880: bv64;
var origCOUNT_1886: bv64;
var origCOUNT_190: bv64;
var origCOUNT_1910: bv64;
var origCOUNT_1916: bv64;
var origCOUNT_1928: bv32;
var origCOUNT_1934: bv32;
var origCOUNT_1942: bv32;
var origCOUNT_1950: bv32;
var origCOUNT_196: bv64;
var origCOUNT_1970: bv64;
var origCOUNT_1976: bv64;
var origCOUNT_1998: bv64;
var origCOUNT_2004: bv64;
var origCOUNT_2034: bv64;
var origCOUNT_2040: bv64;
var origCOUNT_2058: bv64;
var origCOUNT_2064: bv64;
var origCOUNT_2076: bv32;
var origCOUNT_2082: bv32;
var origCOUNT_2090: bv32;
var origCOUNT_2098: bv32;
var origCOUNT_2118: bv64;
var origCOUNT_2124: bv64;
var origCOUNT_2146: bv64;
var origCOUNT_2152: bv64;
var origCOUNT_2182: bv64;
var origCOUNT_2188: bv64;
var origCOUNT_2206: bv64;
var origCOUNT_2212: bv64;
var origCOUNT_222: bv64;
var origCOUNT_2224: bv32;
var origCOUNT_2230: bv32;
var origCOUNT_2238: bv32;
var origCOUNT_2246: bv32;
var origCOUNT_2266: bv64;
var origCOUNT_2272: bv64;
var origCOUNT_228: bv64;
var origCOUNT_2294: bv64;
var origCOUNT_2300: bv64;
var origCOUNT_2330: bv64;
var origCOUNT_2336: bv64;
var origCOUNT_2348: bv32;
var origCOUNT_2354: bv32;
var origCOUNT_2362: bv32;
var origCOUNT_2370: bv32;
var origCOUNT_2390: bv64;
var origCOUNT_2396: bv64;
var origCOUNT_2418: bv64;
var origCOUNT_2424: bv64;
var origCOUNT_2448: bv64;
var origCOUNT_2454: bv64;
var origCOUNT_2478: bv64;
var origCOUNT_2484: bv64;
var origCOUNT_2490: bv32;
var origCOUNT_2496: bv32;
var origCOUNT_2504: bv32;
var origCOUNT_2512: bv32;
var origCOUNT_2532: bv64;
var origCOUNT_2538: bv64;
var origCOUNT_2560: bv64;
var origCOUNT_2566: bv64;
var origCOUNT_262: bv64;
var origCOUNT_268: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_310: bv32;
var origCOUNT_316: bv32;
var origCOUNT_324: bv32;
var origCOUNT_332: bv32;
var origCOUNT_352: bv64;
var origCOUNT_358: bv64;
var origCOUNT_368: bv64;
var origCOUNT_38: bv64;
var origCOUNT_392: bv64;
var origCOUNT_398: bv64;
var origCOUNT_420: bv64;
var origCOUNT_426: bv64;
var origCOUNT_44: bv64;
var origCOUNT_448: bv64;
var origCOUNT_454: bv64;
var origCOUNT_476: bv64;
var origCOUNT_482: bv64;
var origCOUNT_50: bv32;
var origCOUNT_510: bv64;
var origCOUNT_516: bv64;
var origCOUNT_546: bv64;
var origCOUNT_552: bv64;
var origCOUNT_56: bv32;
var origCOUNT_570: bv64;
var origCOUNT_576: bv64;
var origCOUNT_588: bv32;
var origCOUNT_594: bv32;
var origCOUNT_602: bv32;
var origCOUNT_610: bv32;
var origCOUNT_630: bv64;
var origCOUNT_636: bv64;
var origCOUNT_646: bv64;
var origCOUNT_670: bv64;
var origCOUNT_676: bv64;
var origCOUNT_698: bv64;
var origCOUNT_704: bv64;
var origCOUNT_726: bv64;
var origCOUNT_732: bv64;
var origCOUNT_754: bv64;
var origCOUNT_760: bv64;
var origCOUNT_78: bv64;
var origCOUNT_788: bv64;
var origCOUNT_794: bv64;
var origCOUNT_824: bv64;
var origCOUNT_830: bv64;
var origCOUNT_84: bv64;
var origCOUNT_848: bv64;
var origCOUNT_854: bv64;
var origCOUNT_866: bv32;
var origCOUNT_872: bv32;
var origCOUNT_880: bv32;
var origCOUNT_888: bv32;
var origCOUNT_908: bv64;
var origCOUNT_914: bv64;
var origCOUNT_924: bv64;
var origCOUNT_948: bv64;
var origCOUNT_954: bv64;
var origCOUNT_976: bv64;
var origCOUNT_982: bv64;
var origDEST_1003: bv64;
var origDEST_1009: bv64;
var origDEST_1031: bv64;
var origDEST_1037: bv64;
var origDEST_105: bv64;
var origDEST_1065: bv64;
var origDEST_1071: bv64;
var origDEST_1101: bv64;
var origDEST_1107: bv64;
var origDEST_111: bv64;
var origDEST_1119: bv32;
var origDEST_1125: bv32;
var origDEST_1133: bv32;
var origDEST_1141: bv32;
var origDEST_1161: bv64;
var origDEST_1167: bv64;
var origDEST_1177: bv64;
var origDEST_1201: bv64;
var origDEST_1207: bv64;
var origDEST_1229: bv64;
var origDEST_1235: bv64;
var origDEST_1257: bv64;
var origDEST_1263: bv64;
var origDEST_1285: bv64;
var origDEST_1291: bv64;
var origDEST_1319: bv64;
var origDEST_1325: bv64;
var origDEST_133: bv64;
var origDEST_1349: bv64;
var origDEST_1355: bv64;
var origDEST_1379: bv64;
var origDEST_1385: bv64;
var origDEST_139: bv64;
var origDEST_1391: bv32;
var origDEST_1397: bv32;
var origDEST_1405: bv32;
var origDEST_1413: bv32;
var origDEST_1433: bv64;
var origDEST_1439: bv64;
var origDEST_1449: bv64;
var origDEST_1473: bv64;
var origDEST_1479: bv64;
var origDEST_1501: bv64;
var origDEST_1507: bv64;
var origDEST_1529: bv64;
var origDEST_1535: bv64;
var origDEST_1557: bv64;
var origDEST_1563: bv64;
var origDEST_1587: bv64;
var origDEST_1593: bv64;
var origDEST_161: bv64;
var origDEST_1615: bv64;
var origDEST_1621: bv64;
var origDEST_1655: bv64;
var origDEST_1661: bv64;
var origDEST_1667: bv32;
var origDEST_167: bv64;
var origDEST_1673: bv32;
var origDEST_1695: bv64;
var origDEST_1701: bv64;
var origDEST_1723: bv64;
var origDEST_1729: bv64;
var origDEST_1751: bv64;
var origDEST_1757: bv64;
var origDEST_1779: bv64;
var origDEST_1785: bv64;
var origDEST_1807: bv64;
var origDEST_1813: bv64;
var origDEST_1839: bv64;
var origDEST_1845: bv64;
var origDEST_1879: bv64;
var origDEST_1885: bv64;
var origDEST_189: bv64;
var origDEST_1909: bv64;
var origDEST_1915: bv64;
var origDEST_1927: bv32;
var origDEST_1933: bv32;
var origDEST_1941: bv32;
var origDEST_1949: bv32;
var origDEST_195: bv64;
var origDEST_1969: bv64;
var origDEST_1975: bv64;
var origDEST_1997: bv64;
var origDEST_2003: bv64;
var origDEST_2033: bv64;
var origDEST_2039: bv64;
var origDEST_2057: bv64;
var origDEST_2063: bv64;
var origDEST_2075: bv32;
var origDEST_2081: bv32;
var origDEST_2089: bv32;
var origDEST_2097: bv32;
var origDEST_2117: bv64;
var origDEST_2123: bv64;
var origDEST_2145: bv64;
var origDEST_2151: bv64;
var origDEST_2181: bv64;
var origDEST_2187: bv64;
var origDEST_2205: bv64;
var origDEST_221: bv64;
var origDEST_2211: bv64;
var origDEST_2223: bv32;
var origDEST_2229: bv32;
var origDEST_2237: bv32;
var origDEST_2245: bv32;
var origDEST_2265: bv64;
var origDEST_227: bv64;
var origDEST_2271: bv64;
var origDEST_2293: bv64;
var origDEST_2299: bv64;
var origDEST_2329: bv64;
var origDEST_2335: bv64;
var origDEST_2347: bv32;
var origDEST_2353: bv32;
var origDEST_2361: bv32;
var origDEST_2369: bv32;
var origDEST_2389: bv64;
var origDEST_2395: bv64;
var origDEST_2417: bv64;
var origDEST_2423: bv64;
var origDEST_2447: bv64;
var origDEST_2453: bv64;
var origDEST_2477: bv64;
var origDEST_2483: bv64;
var origDEST_2489: bv32;
var origDEST_2495: bv32;
var origDEST_2503: bv32;
var origDEST_2511: bv32;
var origDEST_2531: bv64;
var origDEST_2537: bv64;
var origDEST_2559: bv64;
var origDEST_2565: bv64;
var origDEST_261: bv64;
var origDEST_267: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_309: bv32;
var origDEST_315: bv32;
var origDEST_323: bv32;
var origDEST_331: bv32;
var origDEST_351: bv64;
var origDEST_357: bv64;
var origDEST_367: bv64;
var origDEST_37: bv64;
var origDEST_391: bv64;
var origDEST_397: bv64;
var origDEST_419: bv64;
var origDEST_425: bv64;
var origDEST_43: bv64;
var origDEST_447: bv64;
var origDEST_453: bv64;
var origDEST_475: bv64;
var origDEST_481: bv64;
var origDEST_49: bv32;
var origDEST_509: bv64;
var origDEST_515: bv64;
var origDEST_545: bv64;
var origDEST_55: bv32;
var origDEST_551: bv64;
var origDEST_569: bv64;
var origDEST_575: bv64;
var origDEST_587: bv32;
var origDEST_593: bv32;
var origDEST_601: bv32;
var origDEST_609: bv32;
var origDEST_629: bv64;
var origDEST_635: bv64;
var origDEST_645: bv64;
var origDEST_669: bv64;
var origDEST_675: bv64;
var origDEST_697: bv64;
var origDEST_703: bv64;
var origDEST_725: bv64;
var origDEST_731: bv64;
var origDEST_753: bv64;
var origDEST_759: bv64;
var origDEST_77: bv64;
var origDEST_787: bv64;
var origDEST_793: bv64;
var origDEST_823: bv64;
var origDEST_829: bv64;
var origDEST_83: bv64;
var origDEST_847: bv64;
var origDEST_853: bv64;
var origDEST_865: bv32;
var origDEST_871: bv32;
var origDEST_879: bv32;
var origDEST_887: bv32;
var origDEST_907: bv64;
var origDEST_913: bv64;
var origDEST_923: bv64;
var origDEST_947: bv64;
var origDEST_953: bv64;
var origDEST_975: bv64;
var origDEST_981: bv64;
var ra_2577: bv64;
var t1_1019: bv64;
var t1_1053: bv64;
var t1_1089: bv64;
var t1_1113: bv64;
var t1_1149: bv64;
var t1_1183: bv64;
var t1_1189: bv64;
var t1_121: bv64;
var t1_1217: bv64;
var t1_1245: bv64;
var t1_1273: bv64;
var t1_1307: bv64;
var t1_1331: bv32;
var t1_1337: bv64;
var t1_1361: bv64;
var t1_1367: bv64;
var t1_1421: bv64;
var t1_1455: bv64;
var t1_1461: bv64;
var t1_1489: bv64;
var t1_149: bv64;
var t1_1517: bv64;
var t1_1545: bv64;
var t1_1575: bv64;
var t1_1603: bv64;
var t1_1643: bv64;
var t1_1683: bv64;
var t1_1711: bv64;
var t1_1739: bv64;
var t1_1767: bv64;
var t1_177: bv64;
var t1_1795: bv64;
var t1_1827: bv64;
var t1_1867: bv64;
var t1_1891: bv64;
var t1_1897: bv64;
var t1_1921: bv64;
var t1_1957: bv64;
var t1_1985: bv64;
var t1_2021: bv64;
var t1_2045: bv64;
var t1_2069: bv64;
var t1_209: bv64;
var t1_2105: bv64;
var t1_2133: bv64;
var t1_2169: bv64;
var t1_2193: bv64;
var t1_2217: bv64;
var t1_2253: bv64;
var t1_2281: bv64;
var t1_2317: bv64;
var t1_2341: bv64;
var t1_2377: bv64;
var t1_2405: bv64;
var t1_2429: bv32;
var t1_2435: bv64;
var t1_2459: bv64;
var t1_2465: bv64;
var t1_249: bv64;
var t1_25: bv64;
var t1_2519: bv64;
var t1_2547: bv64;
var t1_2571: bv64;
var t1_273: bv64;
var t1_279: bv64;
var t1_303: bv64;
var t1_339: bv64;
var t1_373: bv64;
var t1_379: bv64;
var t1_407: bv64;
var t1_435: bv64;
var t1_463: bv64;
var t1_497: bv64;
var t1_533: bv64;
var t1_557: bv64;
var t1_581: bv64;
var t1_617: bv64;
var t1_65: bv64;
var t1_651: bv64;
var t1_657: bv64;
var t1_685: bv64;
var t1_713: bv64;
var t1_741: bv64;
var t1_775: bv64;
var t1_811: bv64;
var t1_835: bv64;
var t1_859: bv64;
var t1_895: bv64;
var t1_929: bv64;
var t1_93: bv64;
var t1_935: bv64;
var t1_963: bv64;
var t1_991: bv64;
var t2_1020: bv64;
var t2_1054: bv64;
var t2_1090: bv64;
var t2_1114: bv64;
var t2_1150: bv64;
var t2_1184: bv64;
var t2_1190: bv64;
var t2_1218: bv64;
var t2_122: bv64;
var t2_1246: bv64;
var t2_1274: bv64;
var t2_1308: bv64;
var t2_1332: bv32;
var t2_1338: bv64;
var t2_1362: bv64;
var t2_1368: bv64;
var t2_1422: bv64;
var t2_1456: bv64;
var t2_1462: bv64;
var t2_1490: bv64;
var t2_150: bv64;
var t2_1518: bv64;
var t2_1546: bv64;
var t2_1576: bv64;
var t2_1604: bv64;
var t2_1644: bv64;
var t2_1684: bv64;
var t2_1712: bv64;
var t2_1740: bv64;
var t2_1768: bv64;
var t2_178: bv64;
var t2_1796: bv64;
var t2_1828: bv64;
var t2_1868: bv64;
var t2_1892: bv64;
var t2_1898: bv64;
var t2_1922: bv64;
var t2_1958: bv64;
var t2_1986: bv64;
var t2_2022: bv64;
var t2_2046: bv64;
var t2_2070: bv64;
var t2_210: bv64;
var t2_2106: bv64;
var t2_2134: bv64;
var t2_2170: bv64;
var t2_2194: bv64;
var t2_2218: bv64;
var t2_2254: bv64;
var t2_2282: bv64;
var t2_2318: bv64;
var t2_2342: bv64;
var t2_2378: bv64;
var t2_2406: bv64;
var t2_2430: bv32;
var t2_2436: bv64;
var t2_2460: bv64;
var t2_2466: bv64;
var t2_250: bv64;
var t2_2520: bv64;
var t2_2548: bv64;
var t2_2572: bv64;
var t2_26: bv64;
var t2_274: bv64;
var t2_280: bv64;
var t2_304: bv64;
var t2_340: bv64;
var t2_374: bv64;
var t2_380: bv64;
var t2_408: bv64;
var t2_436: bv64;
var t2_464: bv64;
var t2_498: bv64;
var t2_534: bv64;
var t2_558: bv64;
var t2_582: bv64;
var t2_618: bv64;
var t2_652: bv64;
var t2_658: bv64;
var t2_66: bv64;
var t2_686: bv64;
var t2_714: bv64;
var t2_742: bv64;
var t2_776: bv64;
var t2_812: bv64;
var t2_836: bv64;
var t2_860: bv64;
var t2_896: bv64;
var t2_930: bv64;
var t2_936: bv64;
var t2_94: bv64;
var t2_964: bv64;
var t2_992: bv64;
var t_1: bv64;
var t_101: bv64;
var t_1015: bv32;
var t_1027: bv64;
var t_1043: bv32;
var t_1049: bv32;
var t_1061: bv64;
var t_1077: bv32;
var t_1081: bv32;
var t_1085: bv32;
var t_1097: bv64;
var t_1157: bv64;
var t_117: bv64;
var t_1173: bv32;
var t_1197: bv64;
var t_1213: bv32;
var t_1225: bv64;
var t_1241: bv32;
var t_1253: bv64;
var t_1269: bv32;
var t_1281: bv64;
var t_129: bv64;
var t_1297: bv32;
var t_13: bv32;
var t_1303: bv32;
var t_1315: bv64;
var t_1345: bv64;
var t_1375: bv64;
var t_1429: bv64;
var t_1445: bv32;
var t_145: bv32;
var t_1469: bv64;
var t_1485: bv32;
var t_1497: bv64;
var t_1513: bv32;
var t_1525: bv64;
var t_1541: bv32;
var t_1553: bv64;
var t_1569: bv32;
var t_157: bv64;
var t_1583: bv64;
var t_1599: bv32;
var t_1611: bv64;
var t_1627: bv32;
var t_1631: bv32;
var t_1635: bv32;
var t_1639: bv32;
var t_1651: bv64;
var t_1691: bv64;
var t_17: bv32;
var t_1707: bv32;
var t_1719: bv64;
var t_173: bv32;
var t_1735: bv64;
var t_1747: bv64;
var t_1763: bv32;
var t_1775: bv64;
var t_1791: bv32;
var t_1803: bv64;
var t_1819: bv32;
var t_1823: bv32;
var t_1835: bv64;
var t_185: bv64;
var t_1851: bv32;
var t_1855: bv32;
var t_1859: bv32;
var t_1863: bv32;
var t_1875: bv64;
var t_1905: bv64;
var t_1965: bv64;
var t_1981: bv32;
var t_1993: bv64;
var t_2009: bv32;
var t_201: bv32;
var t_2013: bv32;
var t_2017: bv32;
var t_2029: bv64;
var t_205: bv32;
var t_2053: bv64;
var t_21: bv32;
var t_2113: bv64;
var t_2129: bv32;
var t_2141: bv64;
var t_2157: bv32;
var t_2161: bv32;
var t_2165: bv32;
var t_217: bv64;
var t_2177: bv64;
var t_2201: bv64;
var t_2261: bv64;
var t_2277: bv32;
var t_2289: bv64;
var t_2305: bv32;
var t_2309: bv32;
var t_2313: bv32;
var t_2325: bv64;
var t_233: bv32;
var t_237: bv32;
var t_2385: bv64;
var t_2401: bv32;
var t_241: bv32;
var t_2413: bv64;
var t_2443: bv64;
var t_245: bv32;
var t_2473: bv64;
var t_2527: bv64;
var t_2543: bv32;
var t_2555: bv64;
var t_257: bv64;
var t_287: bv64;
var t_33: bv64;
var t_347: bv64;
var t_363: bv32;
var t_387: bv64;
var t_403: bv32;
var t_415: bv64;
var t_431: bv32;
var t_443: bv64;
var t_459: bv32;
var t_471: bv64;
var t_487: bv32;
var t_493: bv32;
var t_5: bv32;
var t_505: bv64;
var t_521: bv32;
var t_525: bv32;
var t_529: bv32;
var t_541: bv64;
var t_565: bv64;
var t_625: bv64;
var t_641: bv32;
var t_665: bv64;
var t_681: bv32;
var t_693: bv64;
var t_709: bv32;
var t_721: bv64;
var t_73: bv64;
var t_737: bv32;
var t_749: bv64;
var t_765: bv32;
var t_771: bv32;
var t_783: bv64;
var t_799: bv32;
var t_803: bv32;
var t_807: bv32;
var t_819: bv64;
var t_843: bv64;
var t_89: bv32;
var t_9: bv32;
var t_903: bv64;
var t_919: bv32;
var t_943: bv64;
var t_959: bv32;
var t_971: bv64;
var t_987: bv32;
var t_999: bv64;


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
