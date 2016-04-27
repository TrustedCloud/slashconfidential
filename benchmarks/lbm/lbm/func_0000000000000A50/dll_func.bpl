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
axiom _function_addr_low == 2640bv64;
axiom _function_addr_high == 3136bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0xa50:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xa55:
t_1 := RSP;
RSP := MINUS_64(RSP, 56bv64);
CF := bool2bv(LT_64(t_1, 56bv64));
OF := AND_64((XOR_64(t_1, 56bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 56bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xa59:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), 4294967294bv32);

label_0xa61:
goto label_0xa6d;

label_0xa63:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0xa67:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa69:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0xa6d:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 132bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 132bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 132bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 132bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0xa75:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xc31;
}

label_0xa7b:
mem := STORE_LE_32(mem, RSP, 0bv32);

label_0xa82:
goto label_0xa8c;

label_0xa84:
RAX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0xa87:
t_13 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_13[32:31]) == (1bv32[32:31]))), (XOR_1((t_13[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_13)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xa89:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0xa8c:
t_17 := MINUS_32((LOAD_LE_32(mem, RSP)), 100bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 100bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 100bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, RSP)))), 100bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0xa90:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xc2c;
}

label_0xa96:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), 0bv32);

label_0xa9e:
goto label_0xaaa;

label_0xaa0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xaa4:
t_21 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_21[32:31]) == (1bv32[32:31]))), (XOR_1((t_21[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_21)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xaa6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0xaaa:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 100bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 100bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 100bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), 100bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0xaaf:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xc27;
}

label_0xab5:
t_29 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_29)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_29, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))))[1:0]));
SF := t_29[32:31];
ZF := bool2bv(0bv32 == t_29);

label_0xaba:
if (bv2bool(ZF)) {
  goto label_0xae4;
}

label_0xabc:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 99bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 99bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 99bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), 99bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0xac1:
if (bv2bool(ZF)) {
  goto label_0xae4;
}

label_0xac3:
t_37 := MINUS_32((LOAD_LE_32(mem, RSP)), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 0bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_37)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_37, (LOAD_LE_32(mem, RSP)))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))))[1:0]));
SF := t_37[32:31];
ZF := bool2bv(0bv32 == t_37);

label_0xac7:
if (bv2bool(ZF)) {
  goto label_0xae4;
}

label_0xac9:
t_41 := MINUS_32((LOAD_LE_32(mem, RSP)), 99bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 99bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 99bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, RSP)))), 99bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0xacd:
if (bv2bool(ZF)) {
  goto label_0xae4;
}

label_0xacf:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0xad4:
if (bv2bool(ZF)) {
  goto label_0xae4;
}

label_0xad6:
t_49 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 129bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 129bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 129bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_49)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_49, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 129bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))))[1:0]));
SF := t_49[32:31];
ZF := bool2bv(0bv32 == t_49);

label_0xade:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xb68;
}

label_0xae4:
t_53 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_53[32:0]);
OF := bool2bv(t_53 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_53 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_1;
SF := unconstrained_2;
ZF := unconstrained_3;
AF := unconstrained_4;

label_0xae8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xaec:
t1_55 := RCX[32:0];
t2_56 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_56));
CF := bool2bv(LT_32((RCX[32:0]), t1_55));
OF := AND_1((bool2bv((t1_55[32:31]) == (t2_56[32:31]))), (XOR_1((t1_55[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_55)), t2_56)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xaee:
RAX := (0bv32 ++ RCX[32:0]);

label_0xaf0:
t_61 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RCX := (0bv32 ++ t_61[32:0]);
OF := bool2bv(t_61 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_61 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_5;
SF := unconstrained_6;
ZF := unconstrained_7;
AF := unconstrained_8;

label_0xaf5:
t_63 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RCX := (0bv32 ++ t_63[32:0]);
OF := bool2bv(t_63 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_63 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_9;
SF := unconstrained_10;
ZF := unconstrained_11;
AF := unconstrained_12;

label_0xaf8:
t1_65 := RAX[32:0];
t2_66 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_66));
CF := bool2bv(LT_32((RAX[32:0]), t1_65));
OF := AND_1((bool2bv((t1_65[32:31]) == (t2_66[32:31]))), (XOR_1((t1_65[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_65)), t2_66)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xafa:
t_71 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(20bv32[32:31]) ,(1bv32 ++ 20bv32) ,(0bv32 ++ 20bv32)))));
RAX := (0bv32 ++ t_71[32:0]);
OF := bool2bv(t_71 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_71 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_13;
SF := unconstrained_14;
ZF := unconstrained_15;
AF := unconstrained_16;

label_0xafd:
t1_73 := RAX[32:0];
t2_74 := 19bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_74));
CF := bool2bv(LT_32((RAX[32:0]), t1_73));
OF := AND_1((bool2bv((t1_73[32:31]) == (t2_74[32:31]))), (XOR_1((t1_73[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_73)), t2_74)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb00:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xb02:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xb07:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64)))[64:0];

label_0xb0b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RAX);

label_0xb10:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0xb15:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xb17:
RAX := (0bv32 ++ OR_32((RAX[32:0]), 1bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xb1a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 12bv64), RAX[32:0]);

label_0xb1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0xb23:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xb29:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xb2e:
t_83 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0xb31:
if (bv2bool(ZF)) {
  goto label_0xb34;
}

label_0xb33:
assume false;

label_0xb34:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0xb39:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, LSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), origDEST_87[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_21);

label_0xb3d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xb44:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xb48:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0xb4d:
origDEST_93 := RCX;
origCOUNT_94 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_23);

label_0xb51:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_24;
SF := unconstrained_25;
AF := unconstrained_26;
PF := unconstrained_27;

label_0xb55:
if (bv2bool(CF)) {
  goto label_0xb58;
}

label_0xb57:
assume false;

label_0xb58:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0xb5d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 12bv64)));

label_0xb61:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xb63:
goto label_0xc22;

label_0xb68:
t_99 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_99)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_99, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))))[1:0]));
SF := t_99[32:31];
ZF := bool2bv(0bv32 == t_99);

label_0xb6d:
if (bv2bool(ZF)) {
  goto label_0xb7d;
}

label_0xb6f:
t_103 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 128bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 128bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), 128bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_103)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_103, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), 128bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))))[1:0]));
SF := t_103[32:31];
ZF := bool2bv(0bv32 == t_103);

label_0xb77:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xc22;
}

label_0xb7d:
t_107 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_107)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_107, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)), 2bv32)), (XOR_32((RSHIFT_32(t_107, 4bv32)), t_107)))))[1:0]));
SF := t_107[32:31];
ZF := bool2bv(0bv32 == t_107);

label_0xb82:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xc22;
}

label_0xb88:
t_111 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 98bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 98bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), 98bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_111)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_111, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), 98bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)), 2bv32)), (XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)), 2bv32)), (XOR_32((RSHIFT_32(t_111, 4bv32)), t_111)))))[1:0]));
SF := t_111[32:31];
ZF := bool2bv(0bv32 == t_111);

label_0xb8d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xc22;
}

label_0xb93:
t_115 := MINUS_32((LOAD_LE_32(mem, RSP)), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 1bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_115)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_115, (LOAD_LE_32(mem, RSP)))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)), 2bv32)), (XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)), 2bv32)), (XOR_32((RSHIFT_32(t_115, 4bv32)), t_115)))))[1:0]));
SF := t_115[32:31];
ZF := bool2bv(0bv32 == t_115);

label_0xb97:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xc22;
}

label_0xb9d:
t_119 := MINUS_32((LOAD_LE_32(mem, RSP)), 98bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RSP)), 98bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RSP)), 98bv32)), (XOR_32((LOAD_LE_32(mem, RSP)), t_119)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_119, (LOAD_LE_32(mem, RSP)))), 98bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_119, 4bv32)), t_119)), 2bv32)), (XOR_32((RSHIFT_32(t_119, 4bv32)), t_119)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_119, 4bv32)), t_119)), 2bv32)), (XOR_32((RSHIFT_32(t_119, 4bv32)), t_119)))))[1:0]));
SF := t_119[32:31];
ZF := bool2bv(0bv32 == t_119);

label_0xba1:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xc22;
}

label_0xba3:
t_123 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RAX := (0bv32 ++ t_123[32:0]);
OF := bool2bv(t_123 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_123 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_28;
SF := unconstrained_29;
ZF := unconstrained_30;
AF := unconstrained_31;

label_0xba7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0xbab:
t1_125 := RCX[32:0];
t2_126 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_126));
CF := bool2bv(LT_32((RCX[32:0]), t1_125));
OF := AND_1((bool2bv((t1_125[32:31]) == (t2_126[32:31]))), (XOR_1((t1_125[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_125)), t2_126)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0xbad:
RAX := (0bv32 ++ RCX[32:0]);

label_0xbaf:
t_131 := TIMES_64(((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)))))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RCX := (0bv32 ++ t_131[32:0]);
OF := bool2bv(t_131 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_131 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_32;
SF := unconstrained_33;
ZF := unconstrained_34;
AF := unconstrained_35;

label_0xbb4:
t_133 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(100bv32[32:31]) ,(1bv32 ++ 100bv32) ,(0bv32 ++ 100bv32)))));
RCX := (0bv32 ++ t_133[32:0]);
OF := bool2bv(t_133 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_133 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_36;
SF := unconstrained_37;
ZF := unconstrained_38;
AF := unconstrained_39;

label_0xbb7:
t1_135 := RAX[32:0];
t2_136 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_136));
CF := bool2bv(LT_32((RAX[32:0]), t1_135));
OF := AND_1((bool2bv((t1_135[32:31]) == (t2_136[32:31]))), (XOR_1((t1_135[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_135)), t2_136)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbb9:
t_141 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(20bv32[32:31]) ,(1bv32 ++ 20bv32) ,(0bv32 ++ 20bv32)))));
RAX := (0bv32 ++ t_141[32:0]);
OF := bool2bv(t_141 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_141 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_40;
SF := unconstrained_41;
ZF := unconstrained_42;
AF := unconstrained_43;

label_0xbbc:
t1_143 := RAX[32:0];
t2_144 := 19bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_144));
CF := bool2bv(LT_32((RAX[32:0]), t1_143));
OF := AND_1((bool2bv((t1_143[32:31]) == (t2_144[32:31]))), (XOR_1((t1_143[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_143)), t2_144)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbbf:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xbc1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xbc6:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64)))[64:0];

label_0xbca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0xbcf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xbd4:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xbd6:
RAX := (0bv32 ++ OR_32((RAX[32:0]), 2bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xbd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0xbdd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xbe2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xbe8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xbed:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0xbf0:
if (bv2bool(ZF)) {
  goto label_0xbf3;
}

label_0xbf2:
assume false;

label_0xbf3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xbf8:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_48);

label_0xbfc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xc03:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xc07:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xc0c:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_50);

label_0xc10:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_51;
SF := unconstrained_52;
AF := unconstrained_53;
PF := unconstrained_54;

label_0xc14:
if (bv2bool(CF)) {
  goto label_0xc17;
}

label_0xc16:
assume false;

label_0xc17:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0xc1c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0xc20:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xc22:
goto label_0xaa0;

label_0xc27:
goto label_0xa84;

label_0xc2c:
goto label_0xa63;

label_0xc31:
t1_169 := RSP;
t2_170 := 56bv64;
RSP := PLUS_64(RSP, t2_170);
CF := bool2bv(LT_64(RSP, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xc35:

ra_175 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RSP,SF,ZF,mem,origCOUNT_158,origCOUNT_164,origCOUNT_88,origCOUNT_94,origDEST_157,origDEST_163,origDEST_87,origDEST_93,ra_175,t1_125,t1_135,t1_143,t1_169,t1_55,t1_65,t1_73,t2_126,t2_136,t2_144,t2_170,t2_56,t2_66,t2_74,t_1,t_103,t_107,t_111,t_115,t_119,t_123,t_13,t_131,t_133,t_141,t_153,t_17,t_21,t_25,t_29,t_33,t_37,t_41,t_45,t_49,t_5,t_53,t_61,t_63,t_71,t_83,t_9,t_99;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R8: bv64;
var R9: bv64;
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
var RAX: bv64;
var RBX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_158: bv64;
var origCOUNT_164: bv64;
var origCOUNT_88: bv64;
var origCOUNT_94: bv64;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_87: bv64;
var origDEST_93: bv64;
var ra_175: bv64;
var t1_125: bv32;
var t1_135: bv32;
var t1_143: bv32;
var t1_169: bv64;
var t1_55: bv32;
var t1_65: bv32;
var t1_73: bv32;
var t2_126: bv32;
var t2_136: bv32;
var t2_144: bv32;
var t2_170: bv64;
var t2_56: bv32;
var t2_66: bv32;
var t2_74: bv32;
var t_1: bv64;
var t_103: bv32;
var t_107: bv32;
var t_111: bv32;
var t_115: bv32;
var t_119: bv32;
var t_123: bv64;
var t_13: bv32;
var t_131: bv64;
var t_133: bv64;
var t_141: bv64;
var t_153: bv64;
var t_17: bv32;
var t_21: bv32;
var t_25: bv32;
var t_29: bv32;
var t_33: bv32;
var t_37: bv32;
var t_41: bv32;
var t_45: bv32;
var t_49: bv32;
var t_5: bv32;
var t_53: bv64;
var t_61: bv64;
var t_63: bv64;
var t_71: bv64;
var t_83: bv64;
var t_9: bv32;
var t_99: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(304bv64);
axiom policy(448bv64);
axiom policy(2640bv64);
axiom policy(3136bv64);
axiom policy(3472bv64);
axiom policy(3952bv64);
axiom policy(4144bv64);
axiom policy(13232bv64);
axiom policy(25696bv64);
axiom policy(27584bv64);
axiom policy(31504bv64);
axiom policy(35728bv64);
axiom policy(36240bv64);
