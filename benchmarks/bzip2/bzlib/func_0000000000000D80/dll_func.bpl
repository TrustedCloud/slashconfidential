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
axiom _function_addr_low == 3456bv64;
axiom _function_addr_high == 3556bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xd80:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0xd84:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xd89:
t_1 := RSP;
RSP := MINUS_64(RSP, 136bv64);
CF := bool2bv(LT_64(t_1, 136bv64));
OF := AND_64((XOR_64(t_1, 136bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 136bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xd90:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0xd99:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xda5;
}

label_0xd9b:
RAX := (0bv32 ++ 4294967294bv32);

label_0xda0:
goto label_0x11d3;

label_0xda5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xdad:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 48bv64));

label_0xdb1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0xdb6:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0xdbc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xdc8;
}

label_0xdbe:
RAX := (0bv32 ++ 4294967294bv32);

label_0xdc3:
goto label_0x11d3;

label_0xdc8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xdcd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xdd5:
t_13 := MINUS_64((LOAD_LE_64(mem, RAX)), RCX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), RCX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), RCX)), (XOR_64((LOAD_LE_64(mem, RAX)), t_13)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_13, (LOAD_LE_64(mem, RAX)))), RCX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0xdd8:
if (bv2bool(ZF)) {
  goto label_0xde4;
}

label_0xdda:
RAX := (0bv32 ++ 4294967294bv32);

label_0xddf:
goto label_0x11d3;

label_0xde4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xde9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0xdec:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0xdf0:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0xdf5:
if (bv2bool(ZF)) {
  goto label_0xe19;
}

label_0xdf7:
t_21 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0xdfc:
if (bv2bool(ZF)) {
  goto label_0xe23;
}

label_0xdfe:
t_25 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0xe03:
if (bv2bool(ZF)) {
  goto label_0x1012;
}

label_0xe09:
t_29 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_29)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_29, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)), 2bv32)), (XOR_32((RSHIFT_32(t_29, 4bv32)), t_29)))))[1:0]));
SF := t_29[32:31];
ZF := bool2bv(0bv32 == t_29);

label_0xe0e:
if (bv2bool(ZF)) {
  goto label_0x10eb;
}

label_0xe14:
goto label_0x11d1;

label_0xe19:
RAX := (0bv32 ++ 4294967295bv32);

label_0xe1e:
goto label_0x11d3;

label_0xe23:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0xe2b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xe67;
}

label_0xe2d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xe35:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3642bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xe3a"} true;
call arbitrary_func();

label_0xe3a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0xe3e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0xe43:
t_37 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))))[1:0]));
SF := t_37[32:31];
ZF := bool2bv(0bv32 == t_37);

label_0xe45:
if (bv2bool(ZF)) {
  goto label_0xe51;
}

label_0xe47:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 1bv32);

label_0xe4f:
goto label_0xe59;

label_0xe51:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 4294967294bv32);

label_0xe59:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0xe5d:
goto label_0x11d3;

label_0xe62:
goto label_0x1012;

label_0xe67:
t_41 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0xe6f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0xf39;
}

label_0xe75:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xe7d:
t1_45 := RAX;
t2_46 := 8bv64;
RAX := PLUS_64(RAX, t2_46);
CF := bool2bv(LT_64(RAX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe81:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0xe86:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xe8b:
t1_51 := RAX;
t2_52 := 16bv64;
RAX := PLUS_64(RAX, t2_52);
CF := bool2bv(LT_64(RAX, t1_51));
OF := AND_1((bool2bv((t1_51[64:63]) == (t2_52[64:63]))), (XOR_1((t1_51[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_51)), t2_52)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe8f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0xe94:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xe99:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe9f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xea4:
t_59 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))))[1:0]));
SF := t_59[64:63];
ZF := bool2bv(0bv64 == t_59);

label_0xea7:
if (bv2bool(ZF)) {
  goto label_0xeaa;
}

label_0xea9:
assume false;

label_0xeaa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xeaf:
origDEST_63 := RAX;
origCOUNT_64 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), CF, LSHIFT_64(origDEST_63, (MINUS_64(64bv64, origCOUNT_64)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_64 == 1bv64)), origDEST_63[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), AF, unconstrained_5);

label_0xeb3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xeba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xebe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xec3:
origDEST_69 := RCX;
origCOUNT_70 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), CF, LSHIFT_64(origDEST_69, (MINUS_64(64bv64, origCOUNT_70)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_70 == 1bv64)), origDEST_69[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), AF, unconstrained_7);

label_0xec7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0xecb:
if (bv2bool(CF)) {
  goto label_0xece;
}

label_0xecd:
assume false;

label_0xece:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xed3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0xed8:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xeda:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xedc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xee1:
t1_75 := RAX;
t2_76 := 8bv64;
RAX := PLUS_64(RAX, t2_76);
CF := bool2bv(LT_64(RAX, t1_75));
OF := AND_1((bool2bv((t1_75[64:63]) == (t2_76[64:63]))), (XOR_1((t1_75[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_75)), t2_76)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xee5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0xeea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xeef:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xef5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xefa:
t_83 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0xefd:
if (bv2bool(ZF)) {
  goto label_0xf00;
}

label_0xeff:
assume false;

label_0xf00:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xf05:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, LSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), origDEST_87[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_15);

label_0xf09:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf10:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf14:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xf19:
origDEST_93 := RCX;
origCOUNT_94 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_17);

label_0xf1d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0xf21:
if (bv2bool(CF)) {
  goto label_0xf24;
}

label_0xf23:
assume false;

label_0xf24:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xf29:
mem := STORE_LE_32(mem, RAX, 3bv32);

label_0xf2f:
goto label_0xde4;

label_0xf34:
goto label_0x1012;

label_0xf39:
t_99 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_99)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_99, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)), 2bv32)), (XOR_32((RSHIFT_32(t_99, 4bv32)), t_99)))))[1:0]));
SF := t_99[32:31];
ZF := bool2bv(0bv32 == t_99);

label_0xf41:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1008;
}

label_0xf47:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0xf4f:
t1_103 := RAX;
t2_104 := 8bv64;
RAX := PLUS_64(RAX, t2_104);
CF := bool2bv(LT_64(RAX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf53:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0xf58:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xf5d:
t1_109 := RAX;
t2_110 := 16bv64;
RAX := PLUS_64(RAX, t2_110);
CF := bool2bv(LT_64(RAX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf61:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0xf66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xf6b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xf71:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xf76:
t_117 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0xf79:
if (bv2bool(ZF)) {
  goto label_0xf7c;
}

label_0xf7b:
assume false;

label_0xf7c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xf81:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_25);

label_0xf85:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xf8c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xf90:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xf95:
origDEST_127 := RCX;
origCOUNT_128 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_27);

label_0xf99:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0xf9d:
if (bv2bool(CF)) {
  goto label_0xfa0;
}

label_0xf9f:
assume false;

label_0xfa0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xfa5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xfaa:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0xfac:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xfae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xfb3:
t1_133 := RAX;
t2_134 := 8bv64;
RAX := PLUS_64(RAX, t2_134);
CF := bool2bv(LT_64(RAX, t1_133));
OF := AND_1((bool2bv((t1_133[64:63]) == (t2_134[64:63]))), (XOR_1((t1_133[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_133)), t2_134)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfb7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0xfbc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xfc1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xfc7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xfcc:
t_141 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)), 2bv64)), (XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)), 2bv64)), (XOR_64((RSHIFT_64(t_141, 4bv64)), t_141)))))[1:0]));
SF := t_141[64:63];
ZF := bool2bv(0bv64 == t_141);

label_0xfcf:
if (bv2bool(ZF)) {
  goto label_0xfd2;
}

label_0xfd1:
assume false;

label_0xfd2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xfd7:
origDEST_145 := RAX;
origCOUNT_146 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), CF, LSHIFT_64(origDEST_145, (MINUS_64(64bv64, origCOUNT_146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_146 == 1bv64)), origDEST_145[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), AF, unconstrained_35);

label_0xfdb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xfe2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xfe6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xfeb:
origDEST_151 := RCX;
origCOUNT_152 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), CF, LSHIFT_64(origDEST_151, (MINUS_64(64bv64, origCOUNT_152)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_152 == 1bv64)), origDEST_151[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_152 == 0bv64)), AF, unconstrained_37);

label_0xfef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0xff3:
if (bv2bool(CF)) {
  goto label_0xff6;
}

label_0xff5:
assume false;

label_0xff6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0xffb:
mem := STORE_LE_32(mem, RAX, 4bv32);

label_0x1001:
goto label_0xde4;

label_0x1006:
goto label_0x1012;

label_0x1008:
RAX := (0bv32 ++ 4294967294bv32);

label_0x100d:
goto label_0x11d3;

label_0x1012:
t_157 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_157)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_157, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)), 2bv32)), (XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)), 2bv32)), (XOR_32((RSHIFT_32(t_157, 4bv32)), t_157)))))[1:0]));
SF := t_157[32:31];
ZF := bool2bv(0bv32 == t_157);

label_0x101a:
if (bv2bool(ZF)) {
  goto label_0x1026;
}

label_0x101c:
RAX := (0bv32 ++ 4294967295bv32);

label_0x1021:
goto label_0x11d3;

label_0x1026:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x102b:
RAX := LOAD_LE_64(mem, RAX);

label_0x102e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1033:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x1036:
t_161 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), t_161)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_161, (LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)), 2bv32)), (XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)), 2bv32)), (XOR_32((RSHIFT_32(t_161, 4bv32)), t_161)))))[1:0]));
SF := t_161[32:31];
ZF := bool2bv(0bv32 == t_161);

label_0x1039:
if (bv2bool(ZF)) {
  goto label_0x1045;
}

label_0x103b:
RAX := (0bv32 ++ 4294967295bv32);

label_0x1040:
goto label_0x11d3;

label_0x1045:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x104d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4178bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1052"} true;
call arbitrary_func();

label_0x1052:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0x1056:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x105b:
t_165 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_165)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_165, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))))[1:0]));
SF := t_165[32:31];
ZF := bool2bv(0bv32 == t_165);

label_0x105f:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1084;
}

label_0x1061:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1066:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4203bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x106b"} true;
call arbitrary_func();

label_0x106b:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x106e:
t_169 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))))[1:0]));
SF := t_169[32:31];
ZF := bool2bv(0bv32 == t_169);

label_0x1070:
if (bv2bool(ZF)) {
  goto label_0x1084;
}

label_0x1072:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1077:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x107c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 116bv64)));

label_0x107f:
t_173 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), t_173)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_173, (LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))))[1:0]));
SF := t_173[32:31];
ZF := bool2bv(0bv32 == t_173);

label_0x1082:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x108e;
}

label_0x1084:
RAX := (0bv32 ++ 2bv32);

label_0x1089:
goto label_0x11d3;

label_0x108e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1093:
t1_177 := RAX;
t2_178 := 8bv64;
RAX := PLUS_64(RAX, t2_178);
CF := bool2bv(LT_64(RAX, t1_177));
OF := AND_1((bool2bv((t1_177[64:63]) == (t2_178[64:63]))), (XOR_1((t1_177[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_177)), t2_178)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1097:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x109c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x10a1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x10a7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x10ac:
t_185 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)), 2bv64)), (XOR_64((RSHIFT_64(t_185, 4bv64)), t_185)))))[1:0]));
SF := t_185[64:63];
ZF := bool2bv(0bv64 == t_185);

label_0x10af:
if (bv2bool(ZF)) {
  goto label_0x10b2;
}

label_0x10b1:
assume false;

label_0x10b2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x10b7:
origDEST_189 := RAX;
origCOUNT_190 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_46);

label_0x10bb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x10c2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x10c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x10cb:
origDEST_195 := RCX;
origCOUNT_196 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), CF, LSHIFT_64(origDEST_195, (MINUS_64(64bv64, origCOUNT_196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_196 == 1bv64)), origDEST_195[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), AF, unconstrained_48);

label_0x10cf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x10d3:
if (bv2bool(CF)) {
  goto label_0x10d6;
}

label_0x10d5:
assume false;

label_0x10d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x10db:
mem := STORE_LE_32(mem, RAX, 2bv32);

label_0x10e1:
RAX := (0bv32 ++ 1bv32);

label_0x10e6:
goto label_0x11d3;

label_0x10eb:
t_201 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_201)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_201, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)), 2bv32)), (XOR_32((RSHIFT_32(t_201, 4bv32)), t_201)))))[1:0]));
SF := t_201[32:31];
ZF := bool2bv(0bv32 == t_201);

label_0x10f3:
if (bv2bool(ZF)) {
  goto label_0x10ff;
}

label_0x10f5:
RAX := (0bv32 ++ 4294967295bv32);

label_0x10fa:
goto label_0x11d3;

label_0x10ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1104:
RAX := LOAD_LE_64(mem, RAX);

label_0x1107:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x110c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x110f:
t_205 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))), t_205)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_205, (LOAD_LE_32(mem, PLUS_64(RCX, 16bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_205, 4bv32)), t_205)), 2bv32)), (XOR_32((RSHIFT_32(t_205, 4bv32)), t_205)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_205, 4bv32)), t_205)), 2bv32)), (XOR_32((RSHIFT_32(t_205, 4bv32)), t_205)))))[1:0]));
SF := t_205[32:31];
ZF := bool2bv(0bv32 == t_205);

label_0x1112:
if (bv2bool(ZF)) {
  goto label_0x111e;
}

label_0x1114:
RAX := (0bv32 ++ 4294967295bv32);

label_0x1119:
goto label_0x11d3;

label_0x111e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1126:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4395bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x112b"} true;
call arbitrary_func();

label_0x112b:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), RAX[32:0][8:0]);

label_0x112f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x1134:
t_209 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_209, 4bv32)), t_209)), 2bv32)), (XOR_32((RSHIFT_32(t_209, 4bv32)), t_209)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_209, 4bv32)), t_209)), 2bv32)), (XOR_32((RSHIFT_32(t_209, 4bv32)), t_209)))))[1:0]));
SF := t_209[32:31];
ZF := bool2bv(0bv32 == t_209);

label_0x1136:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1142;
}

label_0x1138:
RAX := (0bv32 ++ 4294967295bv32);

label_0x113d:
goto label_0x11d3;

label_0x1142:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1147:
t_213 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_213)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_213, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_213, 4bv32)), t_213)), 2bv32)), (XOR_32((RSHIFT_32(t_213, 4bv32)), t_213)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_213, 4bv32)), t_213)), 2bv32)), (XOR_32((RSHIFT_32(t_213, 4bv32)), t_213)))))[1:0]));
SF := t_213[32:31];
ZF := bool2bv(0bv32 == t_213);

label_0x114b:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x1170;
}

label_0x114d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1152:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4439bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1157"} true;
call arbitrary_func();

label_0x1157:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x115a:
t_217 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)), 2bv32)), (XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)), 2bv32)), (XOR_32((RSHIFT_32(t_217, 4bv32)), t_217)))))[1:0]));
SF := t_217[32:31];
ZF := bool2bv(0bv32 == t_217);

label_0x115c:
if (bv2bool(ZF)) {
  goto label_0x1170;
}

label_0x115e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1163:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1168:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 116bv64)));

label_0x116b:
t_221 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))), t_221)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_221, (LOAD_LE_32(mem, PLUS_64(RAX, 120bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)), 2bv32)), (XOR_32((RSHIFT_32(t_221, 4bv32)), t_221)))))[1:0]));
SF := t_221[32:31];
ZF := bool2bv(0bv32 == t_221);

label_0x116e:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1177;
}

label_0x1170:
RAX := (0bv32 ++ 3bv32);

label_0x1175:
goto label_0x11d3;

label_0x1177:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x117c:
t1_225 := RAX;
t2_226 := 8bv64;
RAX := PLUS_64(RAX, t2_226);
CF := bool2bv(LT_64(RAX, t1_225));
OF := AND_1((bool2bv((t1_225[64:63]) == (t2_226[64:63]))), (XOR_1((t1_225[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_225)), t2_226)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1180:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x1185:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x118a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1190:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1195:
t_233 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))))[1:0]));
SF := t_233[64:63];
ZF := bool2bv(0bv64 == t_233);

label_0x1198:
if (bv2bool(ZF)) {
  goto label_0x119b;
}

label_0x119a:
assume false;

label_0x119b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x11a0:
origDEST_237 := RAX;
origCOUNT_238 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), CF, LSHIFT_64(origDEST_237, (MINUS_64(64bv64, origCOUNT_238)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_238 == 1bv64)), origDEST_237[64:63], unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), AF, unconstrained_58);

label_0x11a4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x11ab:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x11af:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x11b4:
origDEST_243 := RCX;
origCOUNT_244 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_60);

label_0x11b8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_61;
SF := unconstrained_62;
AF := unconstrained_63;
PF := unconstrained_64;

label_0x11bc:
if (bv2bool(CF)) {
  goto label_0x11bf;
}

label_0x11be:
assume false;

label_0x11bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x11c4:
mem := STORE_LE_32(mem, RAX, 1bv32);

label_0x11ca:
RAX := (0bv32 ++ 4bv32);

label_0x11cf:
goto label_0x11d3;

label_0x11d1:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_65;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x11d3:
t1_249 := RSP;
t2_250 := 136bv64;
RSP := PLUS_64(RSP, t2_250);
CF := bool2bv(LT_64(RSP, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x11da:

ra_255 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_122,origCOUNT_128,origCOUNT_146,origCOUNT_152,origCOUNT_190,origCOUNT_196,origCOUNT_238,origCOUNT_244,origCOUNT_64,origCOUNT_70,origCOUNT_88,origCOUNT_94,origDEST_121,origDEST_127,origDEST_145,origDEST_151,origDEST_189,origDEST_195,origDEST_237,origDEST_243,origDEST_63,origDEST_69,origDEST_87,origDEST_93,ra_255,t1_103,t1_109,t1_133,t1_177,t1_225,t1_249,t1_45,t1_51,t1_75,t2_104,t2_110,t2_134,t2_178,t2_226,t2_250,t2_46,t2_52,t2_76,t_1,t_117,t_13,t_141,t_157,t_161,t_165,t_169,t_17,t_173,t_185,t_201,t_205,t_209,t_21,t_213,t_217,t_221,t_233,t_25,t_29,t_33,t_37,t_41,t_5,t_59,t_83,t_9,t_99;

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
var origCOUNT_122: bv64;
var origCOUNT_128: bv64;
var origCOUNT_146: bv64;
var origCOUNT_152: bv64;
var origCOUNT_190: bv64;
var origCOUNT_196: bv64;
var origCOUNT_238: bv64;
var origCOUNT_244: bv64;
var origCOUNT_64: bv64;
var origCOUNT_70: bv64;
var origCOUNT_88: bv64;
var origCOUNT_94: bv64;
var origDEST_121: bv64;
var origDEST_127: bv64;
var origDEST_145: bv64;
var origDEST_151: bv64;
var origDEST_189: bv64;
var origDEST_195: bv64;
var origDEST_237: bv64;
var origDEST_243: bv64;
var origDEST_63: bv64;
var origDEST_69: bv64;
var origDEST_87: bv64;
var origDEST_93: bv64;
var ra_255: bv64;
var t1_103: bv64;
var t1_109: bv64;
var t1_133: bv64;
var t1_177: bv64;
var t1_225: bv64;
var t1_249: bv64;
var t1_45: bv64;
var t1_51: bv64;
var t1_75: bv64;
var t2_104: bv64;
var t2_110: bv64;
var t2_134: bv64;
var t2_178: bv64;
var t2_226: bv64;
var t2_250: bv64;
var t2_46: bv64;
var t2_52: bv64;
var t2_76: bv64;
var t_1: bv64;
var t_117: bv64;
var t_13: bv64;
var t_141: bv64;
var t_157: bv32;
var t_161: bv32;
var t_165: bv32;
var t_169: bv32;
var t_17: bv32;
var t_173: bv32;
var t_185: bv64;
var t_201: bv32;
var t_205: bv32;
var t_209: bv32;
var t_21: bv32;
var t_213: bv32;
var t_217: bv32;
var t_221: bv32;
var t_233: bv64;
var t_25: bv32;
var t_29: bv32;
var t_33: bv32;
var t_37: bv32;
var t_41: bv32;
var t_5: bv64;
var t_59: bv64;
var t_83: bv64;
var t_9: bv64;
var t_99: bv32;


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
