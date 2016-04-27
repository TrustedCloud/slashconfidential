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
axiom _function_addr_low == 20048bv64;
axiom _function_addr_high == 22784bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x4e50:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x4e55:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x4e5a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x4e5f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x4e64:
t_1 := RSP;
RSP := MINUS_64(RSP, 184bv64);
CF := bool2bv(LT_64(t_1, 184bv64));
OF := AND_64((XOR_64(t_1, 184bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 184bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4e6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x4e73:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x4e78:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x4e7e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4f42;
}

label_0x4e84:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x4e8d:
if (bv2bool(ZF)) {
  goto label_0x4ee0;
}

label_0x4e8f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4e97:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4e9d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4ea2:
t_15 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))))[1:0]));
SF := t_15[64:63];
ZF := bool2bv(0bv64 == t_15);

label_0x4ea5:
if (bv2bool(ZF)) {
  goto label_0x4ea8;
}

label_0x4ea7:
assume false;

label_0x4ea8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4eb0:
origDEST_19 := RAX;
origCOUNT_20 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), CF, LSHIFT_64(origDEST_19, (MINUS_64(64bv64, origCOUNT_20)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_20 == 1bv64)), origDEST_19[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_20 == 0bv64)), AF, unconstrained_4);

label_0x4eb4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4ebb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ebf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4ec7:
origDEST_25 := RCX;
origCOUNT_26 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, LSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), origDEST_25[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_6);

label_0x4ecb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x4ecf:
if (bv2bool(CF)) {
  goto label_0x4ed2;
}

label_0x4ed1:
assume false;

label_0x4ed2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4eda:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4ee0:
t_31 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_31)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_31, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))))[1:0]));
SF := t_31[64:63];
ZF := bool2bv(0bv64 == t_31);

label_0x4ee6:
if (bv2bool(ZF)) {
  goto label_0x4f3d;
}

label_0x4ee8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4eed:
t1_35 := RAX;
t2_36 := 5096bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ef3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x4ef8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4efd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f03:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4f08:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x4f0b:
if (bv2bool(ZF)) {
  goto label_0x4f0e;
}

label_0x4f0d:
assume false;

label_0x4f0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4f13:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_14);

label_0x4f17:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4f1e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4f22:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4f27:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_16);

label_0x4f2b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x4f2f:
if (bv2bool(CF)) {
  goto label_0x4f32;
}

label_0x4f31:
assume false;

label_0x4f32:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4f37:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4f3d:
goto label_0x58e4;

label_0x4f42:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4f47:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 5008bv64))));

label_0x4f4e:
t_59 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))))[1:0]));
SF := t_59[32:31];
ZF := bool2bv(0bv32 == t_59);

label_0x4f50:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5014;
}

label_0x4f56:
t_63 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_63)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_63, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)), 2bv64)), (XOR_64((RSHIFT_64(t_63, 4bv64)), t_63)))))[1:0]));
SF := t_63[64:63];
ZF := bool2bv(0bv64 == t_63);

label_0x4f5f:
if (bv2bool(ZF)) {
  goto label_0x4fb2;
}

label_0x4f61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4f69:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f6f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4f74:
t_69 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))))[1:0]));
SF := t_69[64:63];
ZF := bool2bv(0bv64 == t_69);

label_0x4f77:
if (bv2bool(ZF)) {
  goto label_0x4f7a;
}

label_0x4f79:
assume false;

label_0x4f7a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4f82:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_25);

label_0x4f86:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4f8d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4f91:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4f99:
origDEST_79 := RCX;
origCOUNT_80 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_27);

label_0x4f9d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_28;
SF := unconstrained_29;
AF := unconstrained_30;
PF := unconstrained_31;

label_0x4fa1:
if (bv2bool(CF)) {
  goto label_0x4fa4;
}

label_0x4fa3:
assume false;

label_0x4fa4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4fac:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x4fb2:
t_85 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_85)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_85, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))))[1:0]));
SF := t_85[64:63];
ZF := bool2bv(0bv64 == t_85);

label_0x4fb8:
if (bv2bool(ZF)) {
  goto label_0x500f;
}

label_0x4fba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4fbf:
t1_89 := RAX;
t2_90 := 5096bv64;
RAX := PLUS_64(RAX, t2_90);
CF := bool2bv(LT_64(RAX, t1_89));
OF := AND_1((bool2bv((t1_89[64:63]) == (t2_90[64:63]))), (XOR_1((t1_89[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_89)), t2_90)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4fc5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x4fca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x4fcf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4fd5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4fda:
t_97 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))))[1:0]));
SF := t_97[64:63];
ZF := bool2bv(0bv64 == t_97);

label_0x4fdd:
if (bv2bool(ZF)) {
  goto label_0x4fe0;
}

label_0x4fdf:
assume false;

label_0x4fe0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x4fe5:
origDEST_101 := RAX;
origCOUNT_102 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), CF, LSHIFT_64(origDEST_101, (MINUS_64(64bv64, origCOUNT_102)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_102 == 1bv64)), origDEST_101[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), AF, unconstrained_35);

label_0x4fe9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4ff0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ff4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x4ff9:
origDEST_107 := RCX;
origCOUNT_108 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_37);

label_0x4ffd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_38;
SF := unconstrained_39;
AF := unconstrained_40;
PF := unconstrained_41;

label_0x5001:
if (bv2bool(CF)) {
  goto label_0x5004;
}

label_0x5003:
assume false;

label_0x5004:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x5009:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x500f:
goto label_0x58e4;

label_0x5014:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5016:
t_113 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))))[1:0]));
SF := t_113[32:31];
ZF := bool2bv(0bv32 == t_113);

label_0x5018:
if (bv2bool(ZF)) {
  goto label_0x50dc;
}

label_0x501e:
t_117 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_117)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_117, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x5027:
if (bv2bool(ZF)) {
  goto label_0x507a;
}

label_0x5029:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5031:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5037:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x503c:
t_123 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))))[1:0]));
SF := t_123[64:63];
ZF := bool2bv(0bv64 == t_123);

label_0x503f:
if (bv2bool(ZF)) {
  goto label_0x5042;
}

label_0x5041:
assume false;

label_0x5042:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x504a:
origDEST_127 := RAX;
origCOUNT_128 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_47);

label_0x504e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5055:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5059:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5061:
origDEST_133 := RCX;
origCOUNT_134 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_49);

label_0x5065:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_50;
SF := unconstrained_51;
AF := unconstrained_52;
PF := unconstrained_53;

label_0x5069:
if (bv2bool(CF)) {
  goto label_0x506c;
}

label_0x506b:
assume false;

label_0x506c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5074:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x507a:
t_139 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_139)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_139, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x5080:
if (bv2bool(ZF)) {
  goto label_0x50d7;
}

label_0x5082:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5087:
t1_143 := RAX;
t2_144 := 5096bv64;
RAX := PLUS_64(RAX, t2_144);
CF := bool2bv(LT_64(RAX, t1_143));
OF := AND_1((bool2bv((t1_143[64:63]) == (t2_144[64:63]))), (XOR_1((t1_143[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_143)), t2_144)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x508d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x5092:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x5097:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x509d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x50a2:
t_151 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))))[1:0]));
SF := t_151[64:63];
ZF := bool2bv(0bv64 == t_151);

label_0x50a5:
if (bv2bool(ZF)) {
  goto label_0x50a8;
}

label_0x50a7:
assume false;

label_0x50a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x50ad:
origDEST_155 := RAX;
origCOUNT_156 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_57);

label_0x50b1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x50b8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x50bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x50c1:
origDEST_161 := RCX;
origCOUNT_162 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_59);

label_0x50c5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_60;
SF := unconstrained_61;
AF := unconstrained_62;
PF := unconstrained_63;

label_0x50c9:
if (bv2bool(CF)) {
  goto label_0x50cc;
}

label_0x50cb:
assume false;

label_0x50cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x50d1:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x50d7:
goto label_0x58e4;

label_0x50dc:
t_167 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), t_167)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_167, (LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))))[1:0]));
SF := t_167[64:63];
ZF := bool2bv(0bv64 == t_167);

label_0x50e5:
if (bv2bool(ZF)) {
  goto label_0x5138;
}

label_0x50e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x50ef:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_64;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x50f5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x50fa:
t_173 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))))[1:0]));
SF := t_173[64:63];
ZF := bool2bv(0bv64 == t_173);

label_0x50fd:
if (bv2bool(ZF)) {
  goto label_0x5100;
}

label_0x50ff:
assume false;

label_0x5100:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x5108:
origDEST_177 := RAX;
origCOUNT_178 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), CF, LSHIFT_64(origDEST_177, (MINUS_64(64bv64, origCOUNT_178)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_178 == 1bv64)), origDEST_177[64:63], unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), AF, unconstrained_67);

label_0x510c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5113:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5117:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x511f:
origDEST_183 := RCX;
origCOUNT_184 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_68));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_69);

label_0x5123:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_70;
SF := unconstrained_71;
AF := unconstrained_72;
PF := unconstrained_73;

label_0x5127:
if (bv2bool(CF)) {
  goto label_0x512a;
}

label_0x5129:
assume false;

label_0x512a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x5132:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x5138:
t_189 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), t_189)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_189, (LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)), 2bv64)), (XOR_64((RSHIFT_64(t_189, 4bv64)), t_189)))))[1:0]));
SF := t_189[64:63];
ZF := bool2bv(0bv64 == t_189);

label_0x5141:
if (bv2bool(ZF)) {
  goto label_0x5194;
}

label_0x5143:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x514b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_74;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5151:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5156:
t_195 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))))[1:0]));
SF := t_195[64:63];
ZF := bool2bv(0bv64 == t_195);

label_0x5159:
if (bv2bool(ZF)) {
  goto label_0x515c;
}

label_0x515b:
assume false;

label_0x515c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x5164:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_77);

label_0x5168:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x516f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5173:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x517b:
origDEST_205 := RCX;
origCOUNT_206 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_79);

label_0x517f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_80;
SF := unconstrained_81;
AF := unconstrained_82;
PF := unconstrained_83;

label_0x5183:
if (bv2bool(CF)) {
  goto label_0x5186;
}

label_0x5185:
assume false;

label_0x5186:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x518e:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x5194:
t_211 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), t_211)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_211, (LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_211, 4bv64)), t_211)), 2bv64)), (XOR_64((RSHIFT_64(t_211, 4bv64)), t_211)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_211, 4bv64)), t_211)), 2bv64)), (XOR_64((RSHIFT_64(t_211, 4bv64)), t_211)))))[1:0]));
SF := t_211[64:63];
ZF := bool2bv(0bv64 == t_211);

label_0x519d:
if (bv2bool(ZF)) {
  goto label_0x51f0;
}

label_0x519f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x51a7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_84;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x51ad:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x51b2:
t_217 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_85;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)), 2bv64)), (XOR_64((RSHIFT_64(t_217, 4bv64)), t_217)))))[1:0]));
SF := t_217[64:63];
ZF := bool2bv(0bv64 == t_217);

label_0x51b5:
if (bv2bool(ZF)) {
  goto label_0x51b8;
}

label_0x51b7:
assume false;

label_0x51b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x51c0:
origDEST_221 := RAX;
origCOUNT_222 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), CF, LSHIFT_64(origDEST_221, (MINUS_64(64bv64, origCOUNT_222)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_222 == 1bv64)), origDEST_221[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_222 == 0bv64)), AF, unconstrained_87);

label_0x51c4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x51cb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x51cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x51d7:
origDEST_227 := RCX;
origCOUNT_228 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_89);

label_0x51db:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_90;
SF := unconstrained_91;
AF := unconstrained_92;
PF := unconstrained_93;

label_0x51df:
if (bv2bool(CF)) {
  goto label_0x51e2;
}

label_0x51e1:
assume false;

label_0x51e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x51ea:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x51f0:
t_233 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_233)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_233, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))))[1:0]));
SF := t_233[64:63];
ZF := bool2bv(0bv64 == t_233);

label_0x51f9:
if (bv2bool(ZF)) {
  goto label_0x524c;
}

label_0x51fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x5203:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5209:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x520e:
t_239 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_239, 4bv64)), t_239)), 2bv64)), (XOR_64((RSHIFT_64(t_239, 4bv64)), t_239)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_239, 4bv64)), t_239)), 2bv64)), (XOR_64((RSHIFT_64(t_239, 4bv64)), t_239)))))[1:0]));
SF := t_239[64:63];
ZF := bool2bv(0bv64 == t_239);

label_0x5211:
if (bv2bool(ZF)) {
  goto label_0x5214;
}

label_0x5213:
assume false;

label_0x5214:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x521c:
origDEST_243 := RAX;
origCOUNT_244 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_97);

label_0x5220:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5227:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x522b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x5233:
origDEST_249 := RCX;
origCOUNT_250 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), CF, LSHIFT_64(origDEST_249, (MINUS_64(64bv64, origCOUNT_250)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_250 == 1bv64)), origDEST_249[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_250 == 0bv64)), AF, unconstrained_99);

label_0x5237:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_100;
SF := unconstrained_101;
AF := unconstrained_102;
PF := unconstrained_103;

label_0x523b:
if (bv2bool(CF)) {
  goto label_0x523e;
}

label_0x523d:
assume false;

label_0x523e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x5246:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x524c:
t_255 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), t_255)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_255, (LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)), 2bv32)), (XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)), 2bv32)), (XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)))))[1:0]));
SF := t_255[32:31];
ZF := bool2bv(0bv32 == t_255);

label_0x5254:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5559;
}

label_0x525a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x525f:
t_259 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))), t_259)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_259, (LOAD_LE_32(mem, PLUS_64(RAX, 5096bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))))[1:0]));
SF := t_259[32:31];
ZF := bool2bv(0bv32 == t_259);

label_0x5266:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5559;
}

label_0x526c:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_104;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x526e:
t_263 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_263)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_263, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)), 2bv32)), (XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)), 2bv32)), (XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)))))[1:0]));
SF := t_263[32:31];
ZF := bool2bv(0bv32 == t_263);

label_0x5271:
if (bv2bool(ZF)) {
  goto label_0x5559;
}

label_0x5277:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x527c:
t1_267 := RAX;
t2_268 := 5048bv64;
RAX := PLUS_64(RAX, t2_268);
CF := bool2bv(LT_64(RAX, t1_267));
OF := AND_1((bool2bv((t1_267[64:63]) == (t2_268[64:63]))), (XOR_1((t1_267[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_267)), t2_268)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5282:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x5287:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x528c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5292:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5297:
t_275 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))))[1:0]));
SF := t_275[64:63];
ZF := bool2bv(0bv64 == t_275);

label_0x529a:
if (bv2bool(ZF)) {
  goto label_0x529d;
}

label_0x529c:
assume false;

label_0x529d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x52a2:
origDEST_279 := RAX;
origCOUNT_280 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), CF, LSHIFT_64(origDEST_279, (MINUS_64(64bv64, origCOUNT_280)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_280 == 1bv64)), origDEST_279[64:63], unconstrained_107));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), AF, unconstrained_108);

label_0x52a6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x52ad:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x52b1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x52b6:
origDEST_285 := RCX;
origCOUNT_286 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), CF, LSHIFT_64(origDEST_285, (MINUS_64(64bv64, origCOUNT_286)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_286 == 1bv64)), origDEST_285[64:63], unconstrained_109));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), AF, unconstrained_110);

label_0x52ba:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_111;
SF := unconstrained_112;
AF := unconstrained_113;
PF := unconstrained_114;

label_0x52be:
if (bv2bool(CF)) {
  goto label_0x52c1;
}

label_0x52c0:
assume false;

label_0x52c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x52c6:
mem := STORE_LE_32(mem, RAX, 5000bv32);

label_0x52cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x52d1:
t1_291 := RAX;
t2_292 := 4bv64;
RAX := PLUS_64(RAX, t2_292);
CF := bool2bv(LT_64(RAX, t1_291));
OF := AND_1((bool2bv((t1_291[64:63]) == (t2_292[64:63]))), (XOR_1((t1_291[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_291)), t2_292)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x52d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x52dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x52e2:
t1_297 := RAX;
t2_298 := 5040bv64;
RAX := PLUS_64(RAX, t2_298);
CF := bool2bv(LT_64(RAX, t1_297));
OF := AND_1((bool2bv((t1_297[64:63]) == (t2_298[64:63]))), (XOR_1((t1_297[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_297)), t2_298)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x52e8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x52ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x52f2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_115;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x52f8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x52fd:
t_305 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))))[1:0]));
SF := t_305[64:63];
ZF := bool2bv(0bv64 == t_305);

label_0x5300:
if (bv2bool(ZF)) {
  goto label_0x5303;
}

label_0x5302:
assume false;

label_0x5303:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x5308:
origDEST_309 := RAX;
origCOUNT_310 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), CF, LSHIFT_64(origDEST_309, (MINUS_64(64bv64, origCOUNT_310)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv64)), origDEST_309[64:63], unconstrained_117));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), AF, unconstrained_118);

label_0x530c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5313:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5317:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x531c:
origDEST_315 := RCX;
origCOUNT_316 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_120);

label_0x5320:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_121;
SF := unconstrained_122;
AF := unconstrained_123;
PF := unconstrained_124;

label_0x5324:
if (bv2bool(CF)) {
  goto label_0x5327;
}

label_0x5326:
assume false;

label_0x5327:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x532c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x5334:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x5337:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x533c:
t1_321 := RAX;
t2_322 := 5016bv64;
RAX := PLUS_64(RAX, t2_322);
CF := bool2bv(LT_64(RAX, t1_321));
OF := AND_1((bool2bv((t1_321[64:63]) == (t2_322[64:63]))), (XOR_1((t1_321[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_321)), t2_322)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5342:
RDX := (0bv32 ++ 2bv32);

label_0x5347:
RCX := RAX;

label_0x534a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21327bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x534f"} true;
call arbitrary_func();

label_0x534f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x5353:
t_327 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_327)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_327, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))))[1:0]));
SF := t_327[32:31];
ZF := bool2bv(0bv32 == t_327);

label_0x5358:
if (bv2bool(ZF)) {
  goto label_0x5427;
}

label_0x535e:
t_331 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_331)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_331, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))))[1:0]));
SF := t_331[32:31];
ZF := bool2bv(0bv32 == t_331);

label_0x5363:
if (bv2bool(ZF)) {
  goto label_0x5427;
}

label_0x5369:
t_335 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_335)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_335, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_335, 4bv64)), t_335)), 2bv64)), (XOR_64((RSHIFT_64(t_335, 4bv64)), t_335)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_335, 4bv64)), t_335)), 2bv64)), (XOR_64((RSHIFT_64(t_335, 4bv64)), t_335)))))[1:0]));
SF := t_335[64:63];
ZF := bool2bv(0bv64 == t_335);

label_0x5372:
if (bv2bool(ZF)) {
  goto label_0x53c5;
}

label_0x5374:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x537c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5382:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5387:
t_341 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)), 2bv64)), (XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)), 2bv64)), (XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)))))[1:0]));
SF := t_341[64:63];
ZF := bool2bv(0bv64 == t_341);

label_0x538a:
if (bv2bool(ZF)) {
  goto label_0x538d;
}

label_0x538c:
assume false;

label_0x538d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5395:
origDEST_345 := RAX;
origCOUNT_346 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), CF, LSHIFT_64(origDEST_345, (MINUS_64(64bv64, origCOUNT_346)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_346 == 1bv64)), origDEST_345[64:63], unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), AF, unconstrained_128);

label_0x5399:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x53a0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x53a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x53ac:
origDEST_351 := RCX;
origCOUNT_352 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), CF, LSHIFT_64(origDEST_351, (MINUS_64(64bv64, origCOUNT_352)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_352 == 1bv64)), origDEST_351[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), AF, unconstrained_130);

label_0x53b0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_131;
SF := unconstrained_132;
AF := unconstrained_133;
PF := unconstrained_134;

label_0x53b4:
if (bv2bool(CF)) {
  goto label_0x53b7;
}

label_0x53b6:
assume false;

label_0x53b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x53bf:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x53c3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x53c5:
t_357 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_357)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_357, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))))[1:0]));
SF := t_357[64:63];
ZF := bool2bv(0bv64 == t_357);

label_0x53cb:
if (bv2bool(ZF)) {
  goto label_0x5422;
}

label_0x53cd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x53d2:
t1_361 := RAX;
t2_362 := 5096bv64;
RAX := PLUS_64(RAX, t2_362);
CF := bool2bv(LT_64(RAX, t1_361));
OF := AND_1((bool2bv((t1_361[64:63]) == (t2_362[64:63]))), (XOR_1((t1_361[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_361)), t2_362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x53d8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x53dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x53e2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x53e8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x53ed:
t_369 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))))[1:0]));
SF := t_369[64:63];
ZF := bool2bv(0bv64 == t_369);

label_0x53f0:
if (bv2bool(ZF)) {
  goto label_0x53f3;
}

label_0x53f2:
assume false;

label_0x53f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x53f8:
origDEST_373 := RAX;
origCOUNT_374 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), CF, LSHIFT_64(origDEST_373, (MINUS_64(64bv64, origCOUNT_374)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_374 == 1bv64)), origDEST_373[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), AF, unconstrained_138);

label_0x53fc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5403:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5407:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x540c:
origDEST_379 := RCX;
origCOUNT_380 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), CF, LSHIFT_64(origDEST_379, (MINUS_64(64bv64, origCOUNT_380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_380 == 1bv64)), origDEST_379[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), AF, unconstrained_140);

label_0x5410:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_141;
SF := unconstrained_142;
AF := unconstrained_143;
PF := unconstrained_144;

label_0x5414:
if (bv2bool(CF)) {
  goto label_0x5417;
}

label_0x5416:
assume false;

label_0x5417:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x541c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x5420:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5422:
goto label_0x58e4;

label_0x5427:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x542c:
t_385 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), t_385)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_385, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), 5000bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)), 2bv32)), (XOR_32((RSHIFT_32(t_385, 4bv32)), t_385)))))[1:0]));
SF := t_385[32:31];
ZF := bool2bv(0bv32 == t_385);

label_0x5436:
if (bv2bool(NOT_1(CF))) {
  goto label_0x554b;
}

label_0x543c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5441:
RCX := (0bv32 ++ 5000bv32);

label_0x5446:
t_389 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64)))));
CF := bool2bv(LT_32(t_389, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64)))));
OF := AND_32((XOR_32(t_389, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), (XOR_32(t_389, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_389)), (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x544c:
RAX := (0bv32 ++ RCX[32:0]);

label_0x544e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x5452:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5457:
t1_393 := RAX;
t2_394 := 4bv64;
RAX := PLUS_64(RAX, t2_394);
CF := bool2bv(LT_64(RAX, t1_393));
OF := AND_1((bool2bv((t1_393[64:63]) == (t2_394[64:63]))), (XOR_1((t1_393[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_393)), t2_394)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x545b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5460:
R9 := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5463:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x5468:
RDX := (0bv32 ++ 1bv32);

label_0x546d:
RCX := RAX;

label_0x5470:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 21621bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5475"} true;
call arbitrary_func();

label_0x5475:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x5479:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x547d:
t_399 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_399)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_399, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)), 2bv32)), (XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)), 2bv32)), (XOR_32((RSHIFT_32(t_399, 4bv32)), t_399)))))[1:0]));
SF := t_399[32:31];
ZF := bool2bv(0bv32 == t_399);

label_0x5481:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x548d;
}

label_0x5483:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_145;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5485:
t_403 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)), 2bv32)), (XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)), 2bv32)), (XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)))))[1:0]));
SF := t_403[32:31];
ZF := bool2bv(0bv32 == t_403);

label_0x5487:
if (bv2bool(ZF)) {
  goto label_0x554b;
}

label_0x548d:
t_407 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_407)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_407, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)), 2bv64)), (XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)), 2bv64)), (XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)))))[1:0]));
SF := t_407[64:63];
ZF := bool2bv(0bv64 == t_407);

label_0x5496:
if (bv2bool(ZF)) {
  goto label_0x54e9;
}

label_0x5498:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x54a0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x54a6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x54ab:
t_413 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_148;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)), 2bv64)), (XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)), 2bv64)), (XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)))))[1:0]));
SF := t_413[64:63];
ZF := bool2bv(0bv64 == t_413);

label_0x54ae:
if (bv2bool(ZF)) {
  goto label_0x54b1;
}

label_0x54b0:
assume false;

label_0x54b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x54b9:
origDEST_417 := RAX;
origCOUNT_418 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), CF, LSHIFT_64(origDEST_417, (MINUS_64(64bv64, origCOUNT_418)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_418 == 1bv64)), origDEST_417[64:63], unconstrained_149));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), AF, unconstrained_150);

label_0x54bd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x54c4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x54c8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x54d0:
origDEST_423 := RCX;
origCOUNT_424 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), CF, LSHIFT_64(origDEST_423, (MINUS_64(64bv64, origCOUNT_424)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_424 == 1bv64)), origDEST_423[64:63], unconstrained_151));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), AF, unconstrained_152);

label_0x54d4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_153;
SF := unconstrained_154;
AF := unconstrained_155;
PF := unconstrained_156;

label_0x54d8:
if (bv2bool(CF)) {
  goto label_0x54db;
}

label_0x54da:
assume false;

label_0x54db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x54e3:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x54e9:
t_429 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_429)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_429, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))))[1:0]));
SF := t_429[64:63];
ZF := bool2bv(0bv64 == t_429);

label_0x54ef:
if (bv2bool(ZF)) {
  goto label_0x5546;
}

label_0x54f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x54f6:
t1_433 := RAX;
t2_434 := 5096bv64;
RAX := PLUS_64(RAX, t2_434);
CF := bool2bv(LT_64(RAX, t1_433));
OF := AND_1((bool2bv((t1_433[64:63]) == (t2_434[64:63]))), (XOR_1((t1_433[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_433)), t2_434)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x54fc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x5501:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x5506:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x550c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5511:
t_441 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_158;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)), 2bv64)), (XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)), 2bv64)), (XOR_64((RSHIFT_64(t_441, 4bv64)), t_441)))))[1:0]));
SF := t_441[64:63];
ZF := bool2bv(0bv64 == t_441);

label_0x5514:
if (bv2bool(ZF)) {
  goto label_0x5517;
}

label_0x5516:
assume false;

label_0x5517:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x551c:
origDEST_445 := RAX;
origCOUNT_446 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), CF, LSHIFT_64(origDEST_445, (MINUS_64(64bv64, origCOUNT_446)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_446 == 1bv64)), origDEST_445[64:63], unconstrained_159));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_446 == 0bv64)), AF, unconstrained_160);

label_0x5520:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5527:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x552b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x5530:
origDEST_451 := RCX;
origCOUNT_452 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), CF, LSHIFT_64(origDEST_451, (MINUS_64(64bv64, origCOUNT_452)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_452 == 1bv64)), origDEST_451[64:63], unconstrained_161));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_452 == 0bv64)), AF, unconstrained_162);

label_0x5534:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_163;
SF := unconstrained_164;
AF := unconstrained_165;
PF := unconstrained_166;

label_0x5538:
if (bv2bool(CF)) {
  goto label_0x553b;
}

label_0x553a:
assume false;

label_0x553b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x5540:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x5546:
goto label_0x58e4;

label_0x554b:
t_457 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_457)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_457, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_457, 4bv32)), t_457)), 2bv32)), (XOR_32((RSHIFT_32(t_457, 4bv32)), t_457)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_457, 4bv32)), t_457)), 2bv32)), (XOR_32((RSHIFT_32(t_457, 4bv32)), t_457)))))[1:0]));
SF := t_457[32:31];
ZF := bool2bv(0bv32 == t_457);

label_0x5550:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5554;
}

label_0x5552:
goto label_0x5559;

label_0x5554:
goto label_0x526c;

label_0x5559:
t_461 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), t_461)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_461, (LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_461, 4bv32)), t_461)), 2bv32)), (XOR_32((RSHIFT_32(t_461, 4bv32)), t_461)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_461, 4bv32)), t_461)), 2bv32)), (XOR_32((RSHIFT_32(t_461, 4bv32)), t_461)))))[1:0]));
SF := t_461[32:31];
ZF := bool2bv(0bv32 == t_461);

label_0x5561:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x563a;
}

label_0x5567:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_167;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5569:
t_465 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_465)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_465, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)), 2bv32)), (XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)), 2bv32)), (XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)))))[1:0]));
SF := t_465[32:31];
ZF := bool2bv(0bv32 == t_465);

label_0x556c:
if (bv2bool(ZF)) {
  goto label_0x563a;
}

label_0x5572:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_168;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5574:
t_469 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_169;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_469, 4bv32)), t_469)), 2bv32)), (XOR_32((RSHIFT_32(t_469, 4bv32)), t_469)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_469, 4bv32)), t_469)), 2bv32)), (XOR_32((RSHIFT_32(t_469, 4bv32)), t_469)))))[1:0]));
SF := t_469[32:31];
ZF := bool2bv(0bv32 == t_469);

label_0x5576:
if (bv2bool(ZF)) {
  goto label_0x563a;
}

label_0x557c:
t_473 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_473)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_473, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))))[1:0]));
SF := t_473[64:63];
ZF := bool2bv(0bv64 == t_473);

label_0x5585:
if (bv2bool(ZF)) {
  goto label_0x55d8;
}

label_0x5587:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x558f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_170;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5595:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x559a:
t_479 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_171;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)), 2bv64)), (XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)), 2bv64)), (XOR_64((RSHIFT_64(t_479, 4bv64)), t_479)))))[1:0]));
SF := t_479[64:63];
ZF := bool2bv(0bv64 == t_479);

label_0x559d:
if (bv2bool(ZF)) {
  goto label_0x55a0;
}

label_0x559f:
assume false;

label_0x55a0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x55a8:
origDEST_483 := RAX;
origCOUNT_484 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), CF, LSHIFT_64(origDEST_483, (MINUS_64(64bv64, origCOUNT_484)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_484 == 1bv64)), origDEST_483[64:63], unconstrained_172));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), AF, unconstrained_173);

label_0x55ac:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x55b3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x55b7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x55bf:
origDEST_489 := RCX;
origCOUNT_490 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), CF, LSHIFT_64(origDEST_489, (MINUS_64(64bv64, origCOUNT_490)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_490 == 1bv64)), origDEST_489[64:63], unconstrained_174));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), AF, unconstrained_175);

label_0x55c3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_176;
SF := unconstrained_177;
AF := unconstrained_178;
PF := unconstrained_179;

label_0x55c7:
if (bv2bool(CF)) {
  goto label_0x55ca;
}

label_0x55c9:
assume false;

label_0x55ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x55d2:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x55d8:
t_495 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_495)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_495, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_495, 4bv64)), t_495)), 2bv64)), (XOR_64((RSHIFT_64(t_495, 4bv64)), t_495)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_495, 4bv64)), t_495)), 2bv64)), (XOR_64((RSHIFT_64(t_495, 4bv64)), t_495)))))[1:0]));
SF := t_495[64:63];
ZF := bool2bv(0bv64 == t_495);

label_0x55de:
if (bv2bool(ZF)) {
  goto label_0x5635;
}

label_0x55e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x55e5:
t1_499 := RAX;
t2_500 := 5096bv64;
RAX := PLUS_64(RAX, t2_500);
CF := bool2bv(LT_64(RAX, t1_499));
OF := AND_1((bool2bv((t1_499[64:63]) == (t2_500[64:63]))), (XOR_1((t1_499[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_499)), t2_500)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x55eb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x55f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x55f5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_180;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x55fb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5600:
t_507 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_181;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_507, 4bv64)), t_507)), 2bv64)), (XOR_64((RSHIFT_64(t_507, 4bv64)), t_507)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_507, 4bv64)), t_507)), 2bv64)), (XOR_64((RSHIFT_64(t_507, 4bv64)), t_507)))))[1:0]));
SF := t_507[64:63];
ZF := bool2bv(0bv64 == t_507);

label_0x5603:
if (bv2bool(ZF)) {
  goto label_0x5606;
}

label_0x5605:
assume false;

label_0x5606:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x560b:
origDEST_511 := RAX;
origCOUNT_512 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), CF, LSHIFT_64(origDEST_511, (MINUS_64(64bv64, origCOUNT_512)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_512 == 1bv64)), origDEST_511[64:63], unconstrained_182));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), AF, unconstrained_183);

label_0x560f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5616:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x561a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x561f:
origDEST_517 := RCX;
origCOUNT_518 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), CF, LSHIFT_64(origDEST_517, (MINUS_64(64bv64, origCOUNT_518)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_518 == 1bv64)), origDEST_517[64:63], unconstrained_184));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_518 == 0bv64)), AF, unconstrained_185);

label_0x5623:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_186;
SF := unconstrained_187;
AF := unconstrained_188;
PF := unconstrained_189;

label_0x5627:
if (bv2bool(CF)) {
  goto label_0x562a;
}

label_0x5629:
assume false;

label_0x562a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x562f:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x5635:
goto label_0x58e4;

label_0x563a:
t_523 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))), t_523)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_523, (LOAD_LE_64(mem, PLUS_64(RSP, 216bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)), 2bv64)), (XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)), 2bv64)), (XOR_64((RSHIFT_64(t_523, 4bv64)), t_523)))))[1:0]));
SF := t_523[64:63];
ZF := bool2bv(0bv64 == t_523);

label_0x5643:
if (bv2bool(ZF)) {
  goto label_0x56af;
}

label_0x5645:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x564a:
t1_527 := RAX;
t2_528 := 5028bv64;
RAX := PLUS_64(RAX, t2_528);
CF := bool2bv(LT_64(RAX, t1_527));
OF := AND_1((bool2bv((t1_527[64:63]) == (t2_528[64:63]))), (XOR_1((t1_527[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_527)), t2_528)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5650:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x5658:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x5660:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_190;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5666:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x566b:
t_535 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_191;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_535, 4bv64)), t_535)), 2bv64)), (XOR_64((RSHIFT_64(t_535, 4bv64)), t_535)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_535, 4bv64)), t_535)), 2bv64)), (XOR_64((RSHIFT_64(t_535, 4bv64)), t_535)))))[1:0]));
SF := t_535[64:63];
ZF := bool2bv(0bv64 == t_535);

label_0x566e:
if (bv2bool(ZF)) {
  goto label_0x5671;
}

label_0x5670:
assume false;

label_0x5671:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x5679:
origDEST_539 := RAX;
origCOUNT_540 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), CF, LSHIFT_64(origDEST_539, (MINUS_64(64bv64, origCOUNT_540)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_540 == 1bv64)), origDEST_539[64:63], unconstrained_192));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_540 == 0bv64)), AF, unconstrained_193);

label_0x567d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5684:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5688:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x5690:
origDEST_545 := RCX;
origCOUNT_546 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), CF, LSHIFT_64(origDEST_545, (MINUS_64(64bv64, origCOUNT_546)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_546 == 1bv64)), origDEST_545[64:63], unconstrained_194));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_546 == 0bv64)), AF, unconstrained_195);

label_0x5694:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_196;
SF := unconstrained_197;
AF := unconstrained_198;
PF := unconstrained_199;

label_0x5698:
if (bv2bool(CF)) {
  goto label_0x569b;
}

label_0x569a:
assume false;

label_0x569b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x56a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x56ab:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x56ad:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x56af:
t_551 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), t_551)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_551, (LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)), 2bv64)), (XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)), 2bv64)), (XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)))))[1:0]));
SF := t_551[64:63];
ZF := bool2bv(0bv64 == t_551);

label_0x56b8:
if (bv2bool(ZF)) {
  goto label_0x5724;
}

label_0x56ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x56bf:
t1_555 := RAX;
t2_556 := 5032bv64;
RAX := PLUS_64(RAX, t2_556);
CF := bool2bv(LT_64(RAX, t1_555));
OF := AND_1((bool2bv((t1_555[64:63]) == (t2_556[64:63]))), (XOR_1((t1_555[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_555)), t2_556)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x56c5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x56cd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x56d5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_200;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x56db:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x56e0:
t_563 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_201;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))))[1:0]));
SF := t_563[64:63];
ZF := bool2bv(0bv64 == t_563);

label_0x56e3:
if (bv2bool(ZF)) {
  goto label_0x56e6;
}

label_0x56e5:
assume false;

label_0x56e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x56ee:
origDEST_567 := RAX;
origCOUNT_568 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), CF, LSHIFT_64(origDEST_567, (MINUS_64(64bv64, origCOUNT_568)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_568 == 1bv64)), origDEST_567[64:63], unconstrained_202));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_568 == 0bv64)), AF, unconstrained_203);

label_0x56f2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x56f9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x56fd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x5705:
origDEST_573 := RCX;
origCOUNT_574 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), CF, LSHIFT_64(origDEST_573, (MINUS_64(64bv64, origCOUNT_574)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_574 == 1bv64)), origDEST_573[64:63], unconstrained_204));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), AF, unconstrained_205);

label_0x5709:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_206;
SF := unconstrained_207;
AF := unconstrained_208;
PF := unconstrained_209;

label_0x570d:
if (bv2bool(CF)) {
  goto label_0x5710;
}

label_0x570f:
assume false;

label_0x5710:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x5718:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x5720:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5722:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5724:
t_579 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))), t_579)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_579, (LOAD_LE_64(mem, PLUS_64(RSP, 232bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)), 2bv64)), (XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)), 2bv64)), (XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)))))[1:0]));
SF := t_579[64:63];
ZF := bool2bv(0bv64 == t_579);

label_0x572d:
if (bv2bool(ZF)) {
  goto label_0x5799;
}

label_0x572f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5734:
t1_583 := RAX;
t2_584 := 5052bv64;
RAX := PLUS_64(RAX, t2_584);
CF := bool2bv(LT_64(RAX, t1_583));
OF := AND_1((bool2bv((t1_583[64:63]) == (t2_584[64:63]))), (XOR_1((t1_583[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_583)), t2_584)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x573a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x5742:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x574a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_210;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5750:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5755:
t_591 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_211;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_591, 4bv64)), t_591)), 2bv64)), (XOR_64((RSHIFT_64(t_591, 4bv64)), t_591)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_591, 4bv64)), t_591)), 2bv64)), (XOR_64((RSHIFT_64(t_591, 4bv64)), t_591)))))[1:0]));
SF := t_591[64:63];
ZF := bool2bv(0bv64 == t_591);

label_0x5758:
if (bv2bool(ZF)) {
  goto label_0x575b;
}

label_0x575a:
assume false;

label_0x575b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x5763:
origDEST_595 := RAX;
origCOUNT_596 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), CF, LSHIFT_64(origDEST_595, (MINUS_64(64bv64, origCOUNT_596)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_596 == 1bv64)), origDEST_595[64:63], unconstrained_212));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_596 == 0bv64)), AF, unconstrained_213);

label_0x5767:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x576e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5772:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x577a:
origDEST_601 := RCX;
origCOUNT_602 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), CF, LSHIFT_64(origDEST_601, (MINUS_64(64bv64, origCOUNT_602)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_602 == 1bv64)), origDEST_601[64:63], unconstrained_214));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), AF, unconstrained_215);

label_0x577e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_216;
SF := unconstrained_217;
AF := unconstrained_218;
PF := unconstrained_219;

label_0x5782:
if (bv2bool(CF)) {
  goto label_0x5785;
}

label_0x5784:
assume false;

label_0x5785:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x578d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x5795:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x5797:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5799:
t_607 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_607)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_607, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_607, 4bv64)), t_607)), 2bv64)), (XOR_64((RSHIFT_64(t_607, 4bv64)), t_607)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_607, 4bv64)), t_607)), 2bv64)), (XOR_64((RSHIFT_64(t_607, 4bv64)), t_607)))))[1:0]));
SF := t_607[64:63];
ZF := bool2bv(0bv64 == t_607);

label_0x57a2:
if (bv2bool(ZF)) {
  goto label_0x580e;
}

label_0x57a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x57a9:
t1_611 := RAX;
t2_612 := 5056bv64;
RAX := PLUS_64(RAX, t2_612);
CF := bool2bv(LT_64(RAX, t1_611));
OF := AND_1((bool2bv((t1_611[64:63]) == (t2_612[64:63]))), (XOR_1((t1_611[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_611)), t2_612)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x57af:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x57b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x57bf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_220;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x57c5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x57ca:
t_619 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_221;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_619, 4bv64)), t_619)), 2bv64)), (XOR_64((RSHIFT_64(t_619, 4bv64)), t_619)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_619, 4bv64)), t_619)), 2bv64)), (XOR_64((RSHIFT_64(t_619, 4bv64)), t_619)))))[1:0]));
SF := t_619[64:63];
ZF := bool2bv(0bv64 == t_619);

label_0x57cd:
if (bv2bool(ZF)) {
  goto label_0x57d0;
}

label_0x57cf:
assume false;

label_0x57d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x57d8:
origDEST_623 := RAX;
origCOUNT_624 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), CF, LSHIFT_64(origDEST_623, (MINUS_64(64bv64, origCOUNT_624)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_624 == 1bv64)), origDEST_623[64:63], unconstrained_222));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), AF, unconstrained_223);

label_0x57dc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x57e3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x57e7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x57ef:
origDEST_629 := RCX;
origCOUNT_630 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), CF, LSHIFT_64(origDEST_629, (MINUS_64(64bv64, origCOUNT_630)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_630 == 1bv64)), origDEST_629[64:63], unconstrained_224));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_630 == 0bv64)), AF, unconstrained_225);

label_0x57f3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_226;
SF := unconstrained_227;
AF := unconstrained_228;
PF := unconstrained_229;

label_0x57f7:
if (bv2bool(CF)) {
  goto label_0x57fa;
}

label_0x57f9:
assume false;

label_0x57fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x5802:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x580a:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x580c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x580e:
t_635 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_635)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_635, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_635, 4bv64)), t_635)), 2bv64)), (XOR_64((RSHIFT_64(t_635, 4bv64)), t_635)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_635, 4bv64)), t_635)), 2bv64)), (XOR_64((RSHIFT_64(t_635, 4bv64)), t_635)))))[1:0]));
SF := t_635[64:63];
ZF := bool2bv(0bv64 == t_635);

label_0x5817:
if (bv2bool(ZF)) {
  goto label_0x586a;
}

label_0x5819:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5821:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_230;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5827:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x582c:
t_641 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_231;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)), 2bv64)), (XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)), 2bv64)), (XOR_64((RSHIFT_64(t_641, 4bv64)), t_641)))))[1:0]));
SF := t_641[64:63];
ZF := bool2bv(0bv64 == t_641);

label_0x582f:
if (bv2bool(ZF)) {
  goto label_0x5832;
}

label_0x5831:
assume false;

label_0x5832:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x583a:
origDEST_645 := RAX;
origCOUNT_646 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), CF, LSHIFT_64(origDEST_645, (MINUS_64(64bv64, origCOUNT_646)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_646 == 1bv64)), origDEST_645[64:63], unconstrained_232));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_646 == 0bv64)), AF, unconstrained_233);

label_0x583e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5845:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5849:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5851:
origDEST_651 := RCX;
origCOUNT_652 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), CF, LSHIFT_64(origDEST_651, (MINUS_64(64bv64, origCOUNT_652)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_652 == 1bv64)), origDEST_651[64:63], unconstrained_234));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_652 == 0bv64)), AF, unconstrained_235);

label_0x5855:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_236;
SF := unconstrained_237;
AF := unconstrained_238;
PF := unconstrained_239;

label_0x5859:
if (bv2bool(CF)) {
  goto label_0x585c;
}

label_0x585b:
assume false;

label_0x585c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x5864:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x586a:
t_657 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_657)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_657, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_657, 4bv64)), t_657)), 2bv64)), (XOR_64((RSHIFT_64(t_657, 4bv64)), t_657)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_657, 4bv64)), t_657)), 2bv64)), (XOR_64((RSHIFT_64(t_657, 4bv64)), t_657)))))[1:0]));
SF := t_657[64:63];
ZF := bool2bv(0bv64 == t_657);

label_0x5870:
if (bv2bool(ZF)) {
  goto label_0x58c7;
}

label_0x5872:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x5877:
t1_661 := RAX;
t2_662 := 5096bv64;
RAX := PLUS_64(RAX, t2_662);
CF := bool2bv(LT_64(RAX, t1_661));
OF := AND_1((bool2bv((t1_661[64:63]) == (t2_662[64:63]))), (XOR_1((t1_661[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_661)), t2_662)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x587d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x5882:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x5887:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_240;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x588d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5892:
t_669 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_241;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_669, 4bv64)), t_669)), 2bv64)), (XOR_64((RSHIFT_64(t_669, 4bv64)), t_669)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_669, 4bv64)), t_669)), 2bv64)), (XOR_64((RSHIFT_64(t_669, 4bv64)), t_669)))))[1:0]));
SF := t_669[64:63];
ZF := bool2bv(0bv64 == t_669);

label_0x5895:
if (bv2bool(ZF)) {
  goto label_0x5898;
}

label_0x5897:
assume false;

label_0x5898:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x589d:
origDEST_673 := RAX;
origCOUNT_674 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), CF, LSHIFT_64(origDEST_673, (MINUS_64(64bv64, origCOUNT_674)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_674 == 1bv64)), origDEST_673[64:63], unconstrained_242));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), AF, unconstrained_243);

label_0x58a1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x58a8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x58ac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x58b1:
origDEST_679 := RCX;
origCOUNT_680 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), CF, LSHIFT_64(origDEST_679, (MINUS_64(64bv64, origCOUNT_680)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_680 == 1bv64)), origDEST_679[64:63], unconstrained_244));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_680 == 0bv64)), AF, unconstrained_245);

label_0x58b5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_246;
SF := unconstrained_247;
AF := unconstrained_248;
PF := unconstrained_249;

label_0x58b9:
if (bv2bool(CF)) {
  goto label_0x58bc;
}

label_0x58bb:
assume false;

label_0x58bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x58c1:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x58c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x58cc:
t1_685 := RAX;
t2_686 := 5016bv64;
RAX := PLUS_64(RAX, t2_686);
CF := bool2bv(LT_64(RAX, t1_685));
OF := AND_1((bool2bv((t1_685[64:63]) == (t2_686[64:63]))), (XOR_1((t1_685[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_685)), t2_686)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x58d2:
RCX := RAX;

label_0x58d5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 22746bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x58da"} true;
call arbitrary_func();

label_0x58da:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x58df:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 22756bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x58e4"} true;
call arbitrary_func();

label_0x58e4:
t1_691 := RSP;
t2_692 := 184bv64;
RSP := PLUS_64(RSP, t2_692);
CF := bool2bv(LT_64(RSP, t1_691));
OF := AND_1((bool2bv((t1_691[64:63]) == (t2_692[64:63]))), (XOR_1((t1_691[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_691)), t2_692)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x58eb:

ra_697 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_102,origCOUNT_108,origCOUNT_128,origCOUNT_134,origCOUNT_156,origCOUNT_162,origCOUNT_178,origCOUNT_184,origCOUNT_20,origCOUNT_200,origCOUNT_206,origCOUNT_222,origCOUNT_228,origCOUNT_244,origCOUNT_250,origCOUNT_26,origCOUNT_280,origCOUNT_286,origCOUNT_310,origCOUNT_316,origCOUNT_346,origCOUNT_352,origCOUNT_374,origCOUNT_380,origCOUNT_418,origCOUNT_424,origCOUNT_446,origCOUNT_452,origCOUNT_48,origCOUNT_484,origCOUNT_490,origCOUNT_512,origCOUNT_518,origCOUNT_54,origCOUNT_540,origCOUNT_546,origCOUNT_568,origCOUNT_574,origCOUNT_596,origCOUNT_602,origCOUNT_624,origCOUNT_630,origCOUNT_646,origCOUNT_652,origCOUNT_674,origCOUNT_680,origCOUNT_74,origCOUNT_80,origDEST_101,origDEST_107,origDEST_127,origDEST_133,origDEST_155,origDEST_161,origDEST_177,origDEST_183,origDEST_19,origDEST_199,origDEST_205,origDEST_221,origDEST_227,origDEST_243,origDEST_249,origDEST_25,origDEST_279,origDEST_285,origDEST_309,origDEST_315,origDEST_345,origDEST_351,origDEST_373,origDEST_379,origDEST_417,origDEST_423,origDEST_445,origDEST_451,origDEST_47,origDEST_483,origDEST_489,origDEST_511,origDEST_517,origDEST_53,origDEST_539,origDEST_545,origDEST_567,origDEST_573,origDEST_595,origDEST_601,origDEST_623,origDEST_629,origDEST_645,origDEST_651,origDEST_673,origDEST_679,origDEST_73,origDEST_79,ra_697,t1_143,t1_267,t1_291,t1_297,t1_321,t1_35,t1_361,t1_393,t1_433,t1_499,t1_527,t1_555,t1_583,t1_611,t1_661,t1_685,t1_691,t1_89,t2_144,t2_268,t2_292,t2_298,t2_322,t2_36,t2_362,t2_394,t2_434,t2_500,t2_528,t2_556,t2_584,t2_612,t2_662,t2_686,t2_692,t2_90,t_1,t_113,t_117,t_123,t_139,t_15,t_151,t_167,t_173,t_189,t_195,t_211,t_217,t_233,t_239,t_255,t_259,t_263,t_275,t_305,t_31,t_327,t_331,t_335,t_341,t_357,t_369,t_385,t_389,t_399,t_403,t_407,t_413,t_429,t_43,t_441,t_457,t_461,t_465,t_469,t_473,t_479,t_495,t_5,t_507,t_523,t_535,t_551,t_563,t_579,t_59,t_591,t_607,t_619,t_63,t_635,t_641,t_657,t_669,t_69,t_85,t_9,t_97;

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
var origCOUNT_128: bv64;
var origCOUNT_134: bv64;
var origCOUNT_156: bv64;
var origCOUNT_162: bv64;
var origCOUNT_178: bv64;
var origCOUNT_184: bv64;
var origCOUNT_20: bv64;
var origCOUNT_200: bv64;
var origCOUNT_206: bv64;
var origCOUNT_222: bv64;
var origCOUNT_228: bv64;
var origCOUNT_244: bv64;
var origCOUNT_250: bv64;
var origCOUNT_26: bv64;
var origCOUNT_280: bv64;
var origCOUNT_286: bv64;
var origCOUNT_310: bv64;
var origCOUNT_316: bv64;
var origCOUNT_346: bv64;
var origCOUNT_352: bv64;
var origCOUNT_374: bv64;
var origCOUNT_380: bv64;
var origCOUNT_418: bv64;
var origCOUNT_424: bv64;
var origCOUNT_446: bv64;
var origCOUNT_452: bv64;
var origCOUNT_48: bv64;
var origCOUNT_484: bv64;
var origCOUNT_490: bv64;
var origCOUNT_512: bv64;
var origCOUNT_518: bv64;
var origCOUNT_54: bv64;
var origCOUNT_540: bv64;
var origCOUNT_546: bv64;
var origCOUNT_568: bv64;
var origCOUNT_574: bv64;
var origCOUNT_596: bv64;
var origCOUNT_602: bv64;
var origCOUNT_624: bv64;
var origCOUNT_630: bv64;
var origCOUNT_646: bv64;
var origCOUNT_652: bv64;
var origCOUNT_674: bv64;
var origCOUNT_680: bv64;
var origCOUNT_74: bv64;
var origCOUNT_80: bv64;
var origDEST_101: bv64;
var origDEST_107: bv64;
var origDEST_127: bv64;
var origDEST_133: bv64;
var origDEST_155: bv64;
var origDEST_161: bv64;
var origDEST_177: bv64;
var origDEST_183: bv64;
var origDEST_19: bv64;
var origDEST_199: bv64;
var origDEST_205: bv64;
var origDEST_221: bv64;
var origDEST_227: bv64;
var origDEST_243: bv64;
var origDEST_249: bv64;
var origDEST_25: bv64;
var origDEST_279: bv64;
var origDEST_285: bv64;
var origDEST_309: bv64;
var origDEST_315: bv64;
var origDEST_345: bv64;
var origDEST_351: bv64;
var origDEST_373: bv64;
var origDEST_379: bv64;
var origDEST_417: bv64;
var origDEST_423: bv64;
var origDEST_445: bv64;
var origDEST_451: bv64;
var origDEST_47: bv64;
var origDEST_483: bv64;
var origDEST_489: bv64;
var origDEST_511: bv64;
var origDEST_517: bv64;
var origDEST_53: bv64;
var origDEST_539: bv64;
var origDEST_545: bv64;
var origDEST_567: bv64;
var origDEST_573: bv64;
var origDEST_595: bv64;
var origDEST_601: bv64;
var origDEST_623: bv64;
var origDEST_629: bv64;
var origDEST_645: bv64;
var origDEST_651: bv64;
var origDEST_673: bv64;
var origDEST_679: bv64;
var origDEST_73: bv64;
var origDEST_79: bv64;
var ra_697: bv64;
var t1_143: bv64;
var t1_267: bv64;
var t1_291: bv64;
var t1_297: bv64;
var t1_321: bv64;
var t1_35: bv64;
var t1_361: bv64;
var t1_393: bv64;
var t1_433: bv64;
var t1_499: bv64;
var t1_527: bv64;
var t1_555: bv64;
var t1_583: bv64;
var t1_611: bv64;
var t1_661: bv64;
var t1_685: bv64;
var t1_691: bv64;
var t1_89: bv64;
var t2_144: bv64;
var t2_268: bv64;
var t2_292: bv64;
var t2_298: bv64;
var t2_322: bv64;
var t2_36: bv64;
var t2_362: bv64;
var t2_394: bv64;
var t2_434: bv64;
var t2_500: bv64;
var t2_528: bv64;
var t2_556: bv64;
var t2_584: bv64;
var t2_612: bv64;
var t2_662: bv64;
var t2_686: bv64;
var t2_692: bv64;
var t2_90: bv64;
var t_1: bv64;
var t_113: bv32;
var t_117: bv64;
var t_123: bv64;
var t_139: bv64;
var t_15: bv64;
var t_151: bv64;
var t_167: bv64;
var t_173: bv64;
var t_189: bv64;
var t_195: bv64;
var t_211: bv64;
var t_217: bv64;
var t_233: bv64;
var t_239: bv64;
var t_255: bv32;
var t_259: bv32;
var t_263: bv32;
var t_275: bv64;
var t_305: bv64;
var t_31: bv64;
var t_327: bv32;
var t_331: bv32;
var t_335: bv64;
var t_341: bv64;
var t_357: bv64;
var t_369: bv64;
var t_385: bv32;
var t_389: bv32;
var t_399: bv32;
var t_403: bv32;
var t_407: bv64;
var t_413: bv64;
var t_429: bv64;
var t_43: bv64;
var t_441: bv64;
var t_457: bv32;
var t_461: bv32;
var t_465: bv32;
var t_469: bv32;
var t_473: bv64;
var t_479: bv64;
var t_495: bv64;
var t_5: bv64;
var t_507: bv64;
var t_523: bv64;
var t_535: bv64;
var t_551: bv64;
var t_563: bv64;
var t_579: bv64;
var t_59: bv32;
var t_591: bv64;
var t_607: bv64;
var t_619: bv64;
var t_63: bv64;
var t_635: bv64;
var t_641: bv64;
var t_657: bv64;
var t_669: bv64;
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
