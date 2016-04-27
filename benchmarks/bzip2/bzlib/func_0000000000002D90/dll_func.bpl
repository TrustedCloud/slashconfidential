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
axiom _function_addr_low == 11664bv64;
axiom _function_addr_high == 12624bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2d90:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x2d95:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x2d9a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x2d9f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x2da4:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2da8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2dad:
mem := STORE_LE_64(mem, RSP, RAX);

label_0x2db1:
t_5 := MINUS_64((LOAD_LE_64(mem, RSP)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RSP)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RSP)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RSP)), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, RSP)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x2db6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2e69;
}

label_0x2dbc:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x2dc2:
if (bv2bool(ZF)) {
  goto label_0x2e09;
}

label_0x2dc4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2dc9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2dcf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2dd4:
t_15 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))))[1:0]));
SF := t_15[64:63];
ZF := bool2bv(0bv64 == t_15);

label_0x2dd7:
if (bv2bool(ZF)) {
  goto label_0x2dda;
}

label_0x2dd9:
assume false;

label_0x2dda:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2ddf:
origDEST_19 := RAX;
origCOUNT_20 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_4);

label_0x2de3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2dea:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2dee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2df3:
origDEST_25 := RCX;
origCOUNT_26 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, LSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), origDEST_25[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_6);

label_0x2df7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x2dfb:
if (bv2bool(CF)) {
  goto label_0x2dfe;
}

label_0x2dfd:
assume false;

label_0x2dfe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2e03:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x2e09:
t_31 := MINUS_64((LOAD_LE_64(mem, RSP)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RSP)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RSP)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RSP)), t_31)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_31, (LOAD_LE_64(mem, RSP)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))))[1:0]));
SF := t_31[64:63];
ZF := bool2bv(0bv64 == t_31);

label_0x2e0e:
if (bv2bool(ZF)) {
  goto label_0x2e64;
}

label_0x2e10:
RAX := LOAD_LE_64(mem, RSP);

label_0x2e14:
t1_35 := RAX;
t2_36 := 5096bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e1a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RAX);

label_0x2e1f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e24:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e2a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2e2f:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x2e32:
if (bv2bool(ZF)) {
  goto label_0x2e35;
}

label_0x2e34:
assume false;

label_0x2e35:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e3a:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_14);

label_0x2e3e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2e45:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2e49:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e4e:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_16);

label_0x2e52:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x2e56:
if (bv2bool(CF)) {
  goto label_0x2e59;
}

label_0x2e58:
assume false;

label_0x2e59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e5e:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x2e64:
goto label_0x3140;

label_0x2e69:
RAX := LOAD_LE_64(mem, RSP);

label_0x2e6d:
t_59 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), t_59)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_59, (LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))))[1:0]));
SF := t_59[32:31];
ZF := bool2bv(0bv32 == t_59);

label_0x2e74:
if (bv2bool(ZF)) {
  goto label_0x2f27;
}

label_0x2e7a:
t_63 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), t_63)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_63, (LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))))[1:0]));
SF := t_63[64:63];
ZF := bool2bv(0bv64 == t_63);

label_0x2e80:
if (bv2bool(ZF)) {
  goto label_0x2ec7;
}

label_0x2e82:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2e87:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e8d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2e92:
t_69 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))))[1:0]));
SF := t_69[64:63];
ZF := bool2bv(0bv64 == t_69);

label_0x2e95:
if (bv2bool(ZF)) {
  goto label_0x2e98;
}

label_0x2e97:
assume false;

label_0x2e98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2e9d:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_24);

label_0x2ea1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2ea8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2eac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2eb1:
origDEST_79 := RCX;
origCOUNT_80 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_26);

label_0x2eb5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x2eb9:
if (bv2bool(CF)) {
  goto label_0x2ebc;
}

label_0x2ebb:
assume false;

label_0x2ebc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2ec1:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x2ec7:
t_85 := MINUS_64((LOAD_LE_64(mem, RSP)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RSP)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RSP)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RSP)), t_85)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_85, (LOAD_LE_64(mem, RSP)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))))[1:0]));
SF := t_85[64:63];
ZF := bool2bv(0bv64 == t_85);

label_0x2ecc:
if (bv2bool(ZF)) {
  goto label_0x2f22;
}

label_0x2ece:
RAX := LOAD_LE_64(mem, RSP);

label_0x2ed2:
t1_89 := RAX;
t2_90 := 5096bv64;
RAX := PLUS_64(RAX, t2_90);
CF := bool2bv(LT_64(RAX, t1_89));
OF := AND_1((bool2bv((t1_89[64:63]) == (t2_90[64:63]))), (XOR_1((t1_89[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_89)), t2_90)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ed8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RAX);

label_0x2edd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x2ee2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ee8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2eed:
t_97 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))))[1:0]));
SF := t_97[64:63];
ZF := bool2bv(0bv64 == t_97);

label_0x2ef0:
if (bv2bool(ZF)) {
  goto label_0x2ef3;
}

label_0x2ef2:
assume false;

label_0x2ef3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x2ef8:
origDEST_101 := RAX;
origCOUNT_102 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), CF, LSHIFT_64(origDEST_101, (MINUS_64(64bv64, origCOUNT_102)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_102 == 1bv64)), origDEST_101[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), AF, unconstrained_34);

label_0x2efc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2f03:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2f07:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x2f0c:
origDEST_107 := RCX;
origCOUNT_108 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_36);

label_0x2f10:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x2f14:
if (bv2bool(CF)) {
  goto label_0x2f17;
}

label_0x2f16:
assume false;

label_0x2f17:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x2f1c:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x2f22:
goto label_0x3140;

label_0x2f27:
t_113 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), t_113)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_113, (LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)), 2bv64)), (XOR_64((RSHIFT_64(t_113, 4bv64)), t_113)))))[1:0]));
SF := t_113[64:63];
ZF := bool2bv(0bv64 == t_113);

label_0x2f2d:
if (bv2bool(ZF)) {
  goto label_0x2f3b;
}

label_0x2f2f:
t_117 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_117)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_117, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x2f35:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2fe8;
}

label_0x2f3b:
t_121 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), t_121)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_121, (LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x2f41:
if (bv2bool(ZF)) {
  goto label_0x2f88;
}

label_0x2f43:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2f48:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f4e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2f53:
t_127 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))))[1:0]));
SF := t_127[64:63];
ZF := bool2bv(0bv64 == t_127);

label_0x2f56:
if (bv2bool(ZF)) {
  goto label_0x2f59;
}

label_0x2f58:
assume false;

label_0x2f59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2f5e:
origDEST_131 := RAX;
origCOUNT_132 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_44);

label_0x2f62:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2f69:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2f6d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2f72:
origDEST_137 := RCX;
origCOUNT_138 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), CF, LSHIFT_64(origDEST_137, (MINUS_64(64bv64, origCOUNT_138)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv64)), origDEST_137[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), AF, unconstrained_46);

label_0x2f76:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x2f7a:
if (bv2bool(CF)) {
  goto label_0x2f7d;
}

label_0x2f7c:
assume false;

label_0x2f7d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2f82:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x2f88:
t_143 := MINUS_64((LOAD_LE_64(mem, RSP)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RSP)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RSP)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RSP)), t_143)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_143, (LOAD_LE_64(mem, RSP)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x2f8d:
if (bv2bool(ZF)) {
  goto label_0x2fe3;
}

label_0x2f8f:
RAX := LOAD_LE_64(mem, RSP);

label_0x2f93:
t1_147 := RAX;
t2_148 := 5096bv64;
RAX := PLUS_64(RAX, t2_148);
CF := bool2bv(LT_64(RAX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f99:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RAX);

label_0x2f9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x2fa3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2fa9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2fae:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x2fb1:
if (bv2bool(ZF)) {
  goto label_0x2fb4;
}

label_0x2fb3:
assume false;

label_0x2fb4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x2fb9:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_54);

label_0x2fbd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2fc4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2fc8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x2fcd:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_56);

label_0x2fd1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x2fd5:
if (bv2bool(CF)) {
  goto label_0x2fd8;
}

label_0x2fd7:
assume false;

label_0x2fd8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x2fdd:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x2fe3:
goto label_0x3140;

label_0x2fe8:
t_171 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))), t_171)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_171, (LOAD_LE_64(mem, PLUS_64(RSP, 80bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))))[1:0]));
SF := t_171[64:63];
ZF := bool2bv(0bv64 == t_171);

label_0x2fee:
if (bv2bool(ZF)) {
  goto label_0x3035;
}

label_0x2ff0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2ff5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ffb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3000:
t_177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))))[1:0]));
SF := t_177[64:63];
ZF := bool2bv(0bv64 == t_177);

label_0x3003:
if (bv2bool(ZF)) {
  goto label_0x3006;
}

label_0x3005:
assume false;

label_0x3006:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x300b:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_64);

label_0x300f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3016:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x301a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x301f:
origDEST_187 := RCX;
origCOUNT_188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_66);

label_0x3023:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x3027:
if (bv2bool(CF)) {
  goto label_0x302a;
}

label_0x3029:
assume false;

label_0x302a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x302f:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3035:
t_193 := MINUS_64((LOAD_LE_64(mem, RSP)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RSP)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RSP)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RSP)), t_193)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_193, (LOAD_LE_64(mem, RSP)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_193, 4bv64)), t_193)), 2bv64)), (XOR_64((RSHIFT_64(t_193, 4bv64)), t_193)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_193, 4bv64)), t_193)), 2bv64)), (XOR_64((RSHIFT_64(t_193, 4bv64)), t_193)))))[1:0]));
SF := t_193[64:63];
ZF := bool2bv(0bv64 == t_193);

label_0x303a:
if (bv2bool(ZF)) {
  goto label_0x3090;
}

label_0x303c:
RAX := LOAD_LE_64(mem, RSP);

label_0x3040:
t1_197 := RAX;
t2_198 := 5096bv64;
RAX := PLUS_64(RAX, t2_198);
CF := bool2bv(LT_64(RAX, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3046:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x304b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3050:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3056:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x305b:
t_205 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))))[1:0]));
SF := t_205[64:63];
ZF := bool2bv(0bv64 == t_205);

label_0x305e:
if (bv2bool(ZF)) {
  goto label_0x3061;
}

label_0x3060:
assume false;

label_0x3061:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3066:
origDEST_209 := RAX;
origCOUNT_210 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_74);

label_0x306a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3071:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3075:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x307a:
origDEST_215 := RCX;
origCOUNT_216 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), CF, LSHIFT_64(origDEST_215, (MINUS_64(64bv64, origCOUNT_216)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_216 == 1bv64)), origDEST_215[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), AF, unconstrained_76);

label_0x307e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_77;
SF := unconstrained_78;
AF := unconstrained_79;
PF := unconstrained_80;

label_0x3082:
if (bv2bool(CF)) {
  goto label_0x3085;
}

label_0x3084:
assume false;

label_0x3085:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x308a:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3090:
RAX := LOAD_LE_64(mem, RSP);

label_0x3094:
t1_221 := RAX;
t2_222 := 5024bv64;
RAX := PLUS_64(RAX, t2_222);
CF := bool2bv(LT_64(RAX, t1_221));
OF := AND_1((bool2bv((t1_221[64:63]) == (t2_222[64:63]))), (XOR_1((t1_221[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_221)), t2_222)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x309a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x309f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x30a4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30aa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x30af:
t_229 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))))[1:0]));
SF := t_229[64:63];
ZF := bool2bv(0bv64 == t_229);

label_0x30b2:
if (bv2bool(ZF)) {
  goto label_0x30b5;
}

label_0x30b4:
assume false;

label_0x30b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x30ba:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_83));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_84);

label_0x30be:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x30c5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x30c9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x30ce:
origDEST_239 := RCX;
origCOUNT_240 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_86);

label_0x30d2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_87;
SF := unconstrained_88;
AF := unconstrained_89;
PF := unconstrained_90;

label_0x30d6:
if (bv2bool(CF)) {
  goto label_0x30d9;
}

label_0x30d8:
assume false;

label_0x30d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x30de:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x30e3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x30e5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x30e7:
RAX := LOAD_LE_64(mem, RSP);

label_0x30eb:
t1_245 := RAX;
t2_246 := 5016bv64;
RAX := PLUS_64(RAX, t2_246);
CF := bool2bv(LT_64(RAX, t1_245));
OF := AND_1((bool2bv((t1_245[64:63]) == (t2_246[64:63]))), (XOR_1((t1_245[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_245)), t2_246)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30f1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x30f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x30fb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3101:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3106:
t_253 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))))[1:0]));
SF := t_253[64:63];
ZF := bool2bv(0bv64 == t_253);

label_0x3109:
if (bv2bool(ZF)) {
  goto label_0x310c;
}

label_0x310b:
assume false;

label_0x310c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3111:
origDEST_257 := RAX;
origCOUNT_258 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_94);

label_0x3115:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x311c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3120:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3125:
origDEST_263 := RCX;
origCOUNT_264 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_95));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_96);

label_0x3129:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x312d:
if (bv2bool(CF)) {
  goto label_0x3130;
}

label_0x312f:
assume false;

label_0x3130:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3135:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x313a:
RCX := LOAD_LE_64(mem, RCX);

label_0x313d:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3140:
t1_269 := RSP;
t2_270 := 72bv64;
RSP := PLUS_64(RSP, t2_270);
CF := bool2bv(LT_64(RSP, t1_269));
OF := AND_1((bool2bv((t1_269[64:63]) == (t2_270[64:63]))), (XOR_1((t1_269[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_269)), t2_270)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3144:

ra_275 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_102,origCOUNT_108,origCOUNT_132,origCOUNT_138,origCOUNT_160,origCOUNT_166,origCOUNT_182,origCOUNT_188,origCOUNT_20,origCOUNT_210,origCOUNT_216,origCOUNT_234,origCOUNT_240,origCOUNT_258,origCOUNT_26,origCOUNT_264,origCOUNT_48,origCOUNT_54,origCOUNT_74,origCOUNT_80,origDEST_101,origDEST_107,origDEST_131,origDEST_137,origDEST_159,origDEST_165,origDEST_181,origDEST_187,origDEST_19,origDEST_209,origDEST_215,origDEST_233,origDEST_239,origDEST_25,origDEST_257,origDEST_263,origDEST_47,origDEST_53,origDEST_73,origDEST_79,ra_275,t1_147,t1_197,t1_221,t1_245,t1_269,t1_35,t1_89,t2_148,t2_198,t2_222,t2_246,t2_270,t2_36,t2_90,t_1,t_113,t_117,t_121,t_127,t_143,t_15,t_155,t_171,t_177,t_193,t_205,t_229,t_253,t_31,t_43,t_5,t_59,t_63,t_69,t_85,t_9,t_97;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_100: bv1;
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
var origCOUNT_102: bv64;
var origCOUNT_108: bv64;
var origCOUNT_132: bv64;
var origCOUNT_138: bv64;
var origCOUNT_160: bv64;
var origCOUNT_166: bv64;
var origCOUNT_182: bv64;
var origCOUNT_188: bv64;
var origCOUNT_20: bv64;
var origCOUNT_210: bv64;
var origCOUNT_216: bv64;
var origCOUNT_234: bv64;
var origCOUNT_240: bv64;
var origCOUNT_258: bv64;
var origCOUNT_26: bv64;
var origCOUNT_264: bv64;
var origCOUNT_48: bv64;
var origCOUNT_54: bv64;
var origCOUNT_74: bv64;
var origCOUNT_80: bv64;
var origDEST_101: bv64;
var origDEST_107: bv64;
var origDEST_131: bv64;
var origDEST_137: bv64;
var origDEST_159: bv64;
var origDEST_165: bv64;
var origDEST_181: bv64;
var origDEST_187: bv64;
var origDEST_19: bv64;
var origDEST_209: bv64;
var origDEST_215: bv64;
var origDEST_233: bv64;
var origDEST_239: bv64;
var origDEST_25: bv64;
var origDEST_257: bv64;
var origDEST_263: bv64;
var origDEST_47: bv64;
var origDEST_53: bv64;
var origDEST_73: bv64;
var origDEST_79: bv64;
var ra_275: bv64;
var t1_147: bv64;
var t1_197: bv64;
var t1_221: bv64;
var t1_245: bv64;
var t1_269: bv64;
var t1_35: bv64;
var t1_89: bv64;
var t2_148: bv64;
var t2_198: bv64;
var t2_222: bv64;
var t2_246: bv64;
var t2_270: bv64;
var t2_36: bv64;
var t2_90: bv64;
var t_1: bv64;
var t_113: bv64;
var t_117: bv64;
var t_121: bv64;
var t_127: bv64;
var t_143: bv64;
var t_15: bv64;
var t_155: bv64;
var t_171: bv64;
var t_177: bv64;
var t_193: bv64;
var t_205: bv64;
var t_229: bv64;
var t_253: bv64;
var t_31: bv64;
var t_43: bv64;
var t_5: bv64;
var t_59: bv32;
var t_63: bv64;
var t_69: bv64;
var t_85: bv64;
var t_9: bv64;
var t_97: bv64;


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
