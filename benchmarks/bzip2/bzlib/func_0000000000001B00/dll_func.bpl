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
axiom _function_addr_low == 6912bv64;
axiom _function_addr_high == 7904bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1b00:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1b05:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1b09:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 112bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 112bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 112bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 112bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 112bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x1b0f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b1b;
}

label_0x1b11:
RAX := (0bv32 ++ 4294967294bv32);

label_0x1b16:
goto label_0x1ec7;

label_0x1b1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1b20:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 48bv64));

label_0x1b24:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x1b29:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x1b2f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b3b;
}

label_0x1b31:
RAX := (0bv32 ++ 4294967294bv32);

label_0x1b36:
goto label_0x1ec7;

label_0x1b3b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b40:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1b45:
t_13 := MINUS_64((LOAD_LE_64(mem, RAX)), RCX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), RCX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), RCX)), (XOR_64((LOAD_LE_64(mem, RAX)), t_13)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_13, (LOAD_LE_64(mem, RAX)))), RCX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x1b48:
if (bv2bool(ZF)) {
  goto label_0x1b54;
}

label_0x1b4a:
RAX := (0bv32 ++ 4294967294bv32);

label_0x1b4f:
goto label_0x1ec7;

label_0x1b54:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1b56:
t_17 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x1b59:
if (bv2bool(ZF)) {
  goto label_0x1eb4;
}

label_0x1b5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b64:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x1b68:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b74;
}

label_0x1b6a:
RAX := (0bv32 ++ 4294967295bv32);

label_0x1b6f:
goto label_0x1ec7;

label_0x1b74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b79:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x1b7d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1e19;
}

label_0x1b83:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b88:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 44bv64))));

label_0x1b8c:
t_29 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))))[1:0]));
SF := t_29[32:31];
ZF := bool2bv(0bv32 == t_29);

label_0x1b8e:
if (bv2bool(ZF)) {
  goto label_0x1ba0;
}

label_0x1b90:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b95:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7066bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1b9a"} true;
call arbitrary_func();

label_0x1b9a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 40bv64), RAX[32:0][8:0]);

label_0x1b9e:
goto label_0x1bae;

label_0x1ba0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1ba5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7082bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1baa"} true;
call arbitrary_func();

label_0x1baa:
mem := STORE_LE_8(mem, PLUS_64(RSP, 40bv64), RAX[32:0][8:0]);

label_0x1bae:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 40bv64))));

label_0x1bb3:
t_33 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0x1bb5:
if (bv2bool(ZF)) {
  goto label_0x1bc1;
}

label_0x1bb7:
RAX := (0bv32 ++ 4294967292bv32);

label_0x1bbc:
goto label_0x1ec7;

label_0x1bc1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1bc6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 64080bv64)));

label_0x1bcc:
t_37 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_37[32:31]) == (1bv32[32:31]))), (XOR_1((t_37[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_37)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1bce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1bd3:
t_41 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, PLUS_64(RCX, 1092bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0x1bd9:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1e12;
}

label_0x1bdf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1be4:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0x1be8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1e12;
}

label_0x1bee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1bf3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64)));

label_0x1bf9:
RAX := (0bv32 ++ NOT_32((RAX[32:0])));

label_0x1bfb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x1bff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1c04:
t1_49 := RAX;
t2_50 := 3184bv64;
RAX := PLUS_64(RAX, t2_50);
CF := bool2bv(LT_64(RAX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c0a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1c0f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c14:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c1a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1c1f:
t_57 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0x1c22:
if (bv2bool(ZF)) {
  goto label_0x1c25;
}

label_0x1c24:
assume false;

label_0x1c25:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c2a:
origDEST_61 := RAX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_7);

label_0x1c2e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1c35:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1c39:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c3e:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_9);

label_0x1c42:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_10;
SF := unconstrained_11;
AF := unconstrained_12;
PF := unconstrained_13;

label_0x1c46:
if (bv2bool(CF)) {
  goto label_0x1c49;
}

label_0x1c48:
assume false;

label_0x1c49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c4e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0x1c52:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1c54:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1c59:
t_73 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), t_73)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_73, (LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x1c5d:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1c90;
}

label_0x1c5f:
RCX := (0bv32 ++ 2bv32);

label_0x1c64:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7273bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c69"} true;
call arbitrary_func();

label_0x1c69:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1c6e:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3184bv64)));

label_0x1c75:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1c7a:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3176bv64)));

label_0x1c81:
RDX := PLUS_64((PLUS_64(0bv64, 7304bv64)), 0bv64)[64:0];

label_0x1c88:
RCX := RAX;

label_0x1c8b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7312bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c90"} true;
call arbitrary_func();

label_0x1c90:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1c95:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x1c99:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1cb4;
}

label_0x1c9b:
RCX := (0bv32 ++ 2bv32);

label_0x1ca0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7333bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ca5"} true;
call arbitrary_func();

label_0x1ca5:
RDX := PLUS_64((PLUS_64(0bv64, 7340bv64)), 0bv64)[64:0];

label_0x1cac:
RCX := RAX;

label_0x1caf:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7348bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1cb4"} true;
call arbitrary_func();

label_0x1cb4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1cb9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1cbe:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3176bv64)));

label_0x1cc4:
t_81 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64))), t_81)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_81, (LOAD_LE_32(mem, PLUS_64(RAX, 3184bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))))[1:0]));
SF := t_81[32:31];
ZF := bool2bv(0bv32 == t_81);

label_0x1cca:
if (bv2bool(ZF)) {
  goto label_0x1cd6;
}

label_0x1ccc:
RAX := (0bv32 ++ 4294967292bv32);

label_0x1cd1:
goto label_0x1ec7;

label_0x1cd6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1cdb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64)));

label_0x1ce1:
origDEST_85 := RAX[32:0];
origCOUNT_86 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), CF, RSHIFT_32(origDEST_85, (MINUS_32(32bv32, origCOUNT_86)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv32)), AF, unconstrained_15);

label_0x1ce3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1ce8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3188bv64)));

label_0x1cee:
origDEST_91 := RCX[32:0];
origCOUNT_92 := AND_32(31bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(31bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), CF, LSHIFT_32(origDEST_91, (MINUS_32(32bv32, origCOUNT_92)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv32)), origDEST_91[32:31], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv32)), AF, unconstrained_17);

label_0x1cf1:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1cf3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), RAX[32:0]);

label_0x1cf7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1cfc:
t1_99 := RAX;
t2_100 := 3188bv64;
RAX := PLUS_64(RAX, t2_100);
CF := bool2bv(LT_64(RAX, t1_99));
OF := AND_1((bool2bv((t1_99[64:63]) == (t2_100[64:63]))), (XOR_1((t1_99[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_99)), t2_100)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d02:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1d07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d0c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d12:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1d17:
t_107 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)), 2bv64)), (XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)), 2bv64)), (XOR_64((RSHIFT_64(t_107, 4bv64)), t_107)))))[1:0]));
SF := t_107[64:63];
ZF := bool2bv(0bv64 == t_107);

label_0x1d1a:
if (bv2bool(ZF)) {
  goto label_0x1d1d;
}

label_0x1d1c:
assume false;

label_0x1d1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d22:
origDEST_111 := RAX;
origCOUNT_112 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_22);

label_0x1d26:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1d2d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1d31:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d36:
origDEST_117 := RCX;
origCOUNT_118 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_24);

label_0x1d3a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x1d3e:
if (bv2bool(CF)) {
  goto label_0x1d41;
}

label_0x1d40:
assume false;

label_0x1d41:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d46:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 84bv64)));

label_0x1d4a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1d4c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1d51:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1d56:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3184bv64)));

label_0x1d5c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64)));

label_0x1d62:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1d64:
mem := STORE_LE_32(mem, PLUS_64(RSP, 88bv64), RAX[32:0]);

label_0x1d68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1d6d:
t1_125 := RAX;
t2_126 := 3188bv64;
RAX := PLUS_64(RAX, t2_126);
CF := bool2bv(LT_64(RAX, t1_125));
OF := AND_1((bool2bv((t1_125[64:63]) == (t2_126[64:63]))), (XOR_1((t1_125[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_125)), t2_126)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d73:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1d78:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d7d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_30;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d83:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1d88:
t_133 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)), 2bv64)), (XOR_64((RSHIFT_64(t_133, 4bv64)), t_133)))))[1:0]));
SF := t_133[64:63];
ZF := bool2bv(0bv64 == t_133);

label_0x1d8b:
if (bv2bool(ZF)) {
  goto label_0x1d8e;
}

label_0x1d8d:
assume false;

label_0x1d8e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d93:
origDEST_137 := RAX;
origCOUNT_138 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), CF, LSHIFT_64(origDEST_137, (MINUS_64(64bv64, origCOUNT_138)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv64)), origDEST_137[64:63], unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), AF, unconstrained_33);

label_0x1d97:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1d9e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1da2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1da7:
origDEST_143 := RCX;
origCOUNT_144 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_35);

label_0x1dab:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_36;
SF := unconstrained_37;
AF := unconstrained_38;
PF := unconstrained_39;

label_0x1daf:
if (bv2bool(CF)) {
  goto label_0x1db2;
}

label_0x1db1:
assume false;

label_0x1db2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1db7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x1dbb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1dbd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1dc2:
t1_149 := RAX;
t2_150 := 8bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1dc6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1dcb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1dd0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_40;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1dd6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1ddb:
t_157 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)), 2bv64)), (XOR_64((RSHIFT_64(t_157, 4bv64)), t_157)))))[1:0]));
SF := t_157[64:63];
ZF := bool2bv(0bv64 == t_157);

label_0x1dde:
if (bv2bool(ZF)) {
  goto label_0x1de1;
}

label_0x1de0:
assume false;

label_0x1de1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1de6:
origDEST_161 := RAX;
origCOUNT_162 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_43);

label_0x1dea:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1df1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1df5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1dfa:
origDEST_167 := RCX;
origCOUNT_168 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_45);

label_0x1dfe:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_46;
SF := unconstrained_47;
AF := unconstrained_48;
PF := unconstrained_49;

label_0x1e02:
if (bv2bool(CF)) {
  goto label_0x1e05;
}

label_0x1e04:
assume false;

label_0x1e05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1e0a:
mem := STORE_LE_32(mem, RAX, 14bv32);

label_0x1e10:
goto label_0x1e19;

label_0x1e12:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_50;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1e14:
goto label_0x1ec7;

label_0x1e19:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e1e:
t_173 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 10bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 10bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 10bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_173)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_173, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 10bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))))[1:0]));
SF := t_173[32:31];
ZF := bool2bv(0bv32 == t_173);

label_0x1e22:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1eaf;
}

label_0x1e28:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e2d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7730bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1e32"} true;
call arbitrary_func();

label_0x1e32:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x1e36:
t_177 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_177)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_177, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))))[1:0]));
SF := t_177[32:31];
ZF := bool2bv(0bv32 == t_177);

label_0x1e3b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1e9e;
}

label_0x1e3d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e42:
t_181 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))), t_181)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_181, (LOAD_LE_32(mem, PLUS_64(RAX, 52bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))))[1:0]));
SF := t_181[32:31];
ZF := bool2bv(0bv32 == t_181);

label_0x1e46:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1e79;
}

label_0x1e48:
RCX := (0bv32 ++ 2bv32);

label_0x1e4d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7762bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1e52"} true;
call arbitrary_func();

label_0x1e52:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e57:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3188bv64)));

label_0x1e5e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e63:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3180bv64)));

label_0x1e6a:
RDX := PLUS_64((PLUS_64(0bv64, 7793bv64)), 0bv64)[64:0];

label_0x1e71:
RCX := RAX;

label_0x1e74:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7801bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1e79"} true;
call arbitrary_func();

label_0x1e79:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e7e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1e83:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 3180bv64)));

label_0x1e89:
t_185 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64))), t_185)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_185, (LOAD_LE_32(mem, PLUS_64(RAX, 3188bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)), 2bv32)), (XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)), 2bv32)), (XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)))))[1:0]));
SF := t_185[32:31];
ZF := bool2bv(0bv32 == t_185);

label_0x1e8f:
if (bv2bool(ZF)) {
  goto label_0x1e98;
}

label_0x1e91:
RAX := (0bv32 ++ 4294967292bv32);

label_0x1e96:
goto label_0x1ec7;

label_0x1e98:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x1e9c:
goto label_0x1ec7;

label_0x1e9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1ea3:
t_189 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))), t_189)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_189, (LOAD_LE_32(mem, PLUS_64(RAX, 8bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)), 2bv32)), (XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)), 2bv32)), (XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)))))[1:0]));
SF := t_189[32:31];
ZF := bool2bv(0bv32 == t_189);

label_0x1ea7:
if (bv2bool(ZF)) {
  goto label_0x1eaf;
}

label_0x1ea9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x1ead:
goto label_0x1ec7;

label_0x1eaf:
goto label_0x1b54;

label_0x1eb4:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_51;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1eb6:
t_193 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_193)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_193, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)), 2bv32)), (XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)), 2bv32)), (XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)))))[1:0]));
SF := t_193[32:31];
ZF := bool2bv(0bv32 == t_193);

label_0x1eb9:
if (bv2bool(ZF)) {
  goto label_0x1ec5;
}

label_0x1ebb:
RCX := (0bv32 ++ 6001bv32);

label_0x1ec0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7877bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ec5"} true;
call arbitrary_func();

label_0x1ec5:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_52;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1ec7:
t1_197 := RSP;
t2_198 := 104bv64;
RSP := PLUS_64(RSP, t2_198);
CF := bool2bv(LT_64(RSP, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1ecb:

ra_203 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_112,origCOUNT_118,origCOUNT_138,origCOUNT_144,origCOUNT_162,origCOUNT_168,origCOUNT_62,origCOUNT_68,origCOUNT_86,origCOUNT_92,origDEST_111,origDEST_117,origDEST_137,origDEST_143,origDEST_161,origDEST_167,origDEST_61,origDEST_67,origDEST_85,origDEST_91,ra_203,t1_125,t1_149,t1_197,t1_49,t1_99,t2_100,t2_126,t2_150,t2_198,t2_50,t_1,t_107,t_13,t_133,t_157,t_17,t_173,t_177,t_181,t_185,t_189,t_193,t_21,t_25,t_29,t_33,t_37,t_41,t_45,t_5,t_57,t_73,t_77,t_81,t_9;

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
var origCOUNT_112: bv64;
var origCOUNT_118: bv64;
var origCOUNT_138: bv64;
var origCOUNT_144: bv64;
var origCOUNT_162: bv64;
var origCOUNT_168: bv64;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origCOUNT_86: bv32;
var origCOUNT_92: bv32;
var origDEST_111: bv64;
var origDEST_117: bv64;
var origDEST_137: bv64;
var origDEST_143: bv64;
var origDEST_161: bv64;
var origDEST_167: bv64;
var origDEST_61: bv64;
var origDEST_67: bv64;
var origDEST_85: bv32;
var origDEST_91: bv32;
var ra_203: bv64;
var t1_125: bv64;
var t1_149: bv64;
var t1_197: bv64;
var t1_49: bv64;
var t1_99: bv64;
var t2_100: bv64;
var t2_126: bv64;
var t2_150: bv64;
var t2_198: bv64;
var t2_50: bv64;
var t_1: bv64;
var t_107: bv64;
var t_13: bv64;
var t_133: bv64;
var t_157: bv64;
var t_17: bv32;
var t_173: bv32;
var t_177: bv32;
var t_181: bv32;
var t_185: bv32;
var t_189: bv32;
var t_193: bv32;
var t_21: bv32;
var t_25: bv32;
var t_29: bv32;
var t_33: bv32;
var t_37: bv32;
var t_41: bv32;
var t_45: bv32;
var t_5: bv64;
var t_57: bv64;
var t_73: bv32;
var t_77: bv32;
var t_81: bv32;
var t_9: bv64;


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
