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
axiom _function_addr_low == 12592bv64;
axiom _function_addr_high == 14480bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x3130:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x3135:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x313a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x313e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x3143:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x314a:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x3152:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x3159:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3161:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12646bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3166"} true;
call arbitrary_func();

label_0x3166:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3169:
t_5 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x316b:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3220;
}

label_0x3171:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3179:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x317f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3184:
t_11 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x3187:
if (bv2bool(ZF)) {
  goto label_0x318a;
}

label_0x3189:
assume false;

label_0x318a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3192:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_5);

label_0x3196:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x319d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x31a1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x31a9:
origDEST_21 := RCX;
origCOUNT_22 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x31ad:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_8;
SF := unconstrained_9;
AF := unconstrained_10;
PF := unconstrained_11;

label_0x31b1:
if (bv2bool(CF)) {
  goto label_0x31b4;
}

label_0x31b3:
assume false;

label_0x31b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x31bc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x31c3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x31c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x31cd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31d3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x31d8:
t_29 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0x31db:
if (bv2bool(ZF)) {
  goto label_0x31de;
}

label_0x31dd:
assume false;

label_0x31de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x31e6:
origDEST_33 := RAX;
origCOUNT_34 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, LSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), origDEST_33[64:63], unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_15);

label_0x31ea:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x31f1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x31f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x31fd:
origDEST_39 := RCX;
origCOUNT_40 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), CF, LSHIFT_64(origDEST_39, (MINUS_64(64bv64, origCOUNT_40)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv64)), origDEST_39[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), AF, unconstrained_17);

label_0x3201:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_18;
SF := unconstrained_19;
AF := unconstrained_20;
PF := unconstrained_21;

label_0x3205:
if (bv2bool(CF)) {
  goto label_0x3208;
}

label_0x3207:
assume false;

label_0x3208:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3210:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x3217:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3219:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x321b:
goto label_0x3880;

label_0x3220:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x3228:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x322f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3237:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12860bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x323c"} true;
call arbitrary_func();

label_0x323c:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, RAX)[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, RAX)) ,(0bv16 ++ LOAD_LE_16(mem, RAX)))));

label_0x323f:
t_45 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0x3241:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x32f6;
}

label_0x3247:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x324f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3255:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x325a:
t_51 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x325d:
if (bv2bool(ZF)) {
  goto label_0x3260;
}

label_0x325f:
assume false;

label_0x3260:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3268:
origDEST_55 := RAX;
origCOUNT_56 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_26);

label_0x326c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3273:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3277:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x327f:
origDEST_61 := RCX;
origCOUNT_62 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_28);

label_0x3283:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_29;
SF := unconstrained_30;
AF := unconstrained_31;
PF := unconstrained_32;

label_0x3287:
if (bv2bool(CF)) {
  goto label_0x328a;
}

label_0x3289:
assume false;

label_0x328a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3292:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x3299:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x329b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x32a3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x32a9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x32ae:
t_69 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))))[1:0]));
SF := t_69[64:63];
ZF := bool2bv(0bv64 == t_69);

label_0x32b1:
if (bv2bool(ZF)) {
  goto label_0x32b4;
}

label_0x32b3:
assume false;

label_0x32b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x32bc:
origDEST_73 := RAX;
origCOUNT_74 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), CF, LSHIFT_64(origDEST_73, (MINUS_64(64bv64, origCOUNT_74)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv64)), origDEST_73[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv64)), AF, unconstrained_36);

label_0x32c0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x32c7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x32cb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x32d3:
origDEST_79 := RCX;
origCOUNT_80 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_38);

label_0x32d7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x32db:
if (bv2bool(CF)) {
  goto label_0x32de;
}

label_0x32dd:
assume false;

label_0x32de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x32e6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x32ed:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x32ef:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x32f1:
goto label_0x3880;

label_0x32f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x32fe:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 170bv64))));

label_0x3305:
t_85 := MINUS_32((RAX[32:0]), 65535bv32);
CF := bool2bv(LT_32((RAX[32:0]), 65535bv32));
OF := AND_32((XOR_32((RAX[32:0]), 65535bv32)), (XOR_32((RAX[32:0]), t_85)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_85, (RAX[32:0]))), 65535bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))))[1:0]));
SF := t_85[32:31];
ZF := bool2bv(0bv32 == t_85);

label_0x330a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x33af;
}

label_0x3310:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3318:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x331a:
RCX := (0bv32 ++ 1bv32);

label_0x331f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), RCX[32:0]);

label_0x3323:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3326:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x332a:
origDEST_89 := RAX[32:0];
origCOUNT_90 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), CF, RSHIFT_32(origDEST_89, (MINUS_32(32bv32, origCOUNT_90)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv32)), AF, unconstrained_44);

label_0x332c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3334:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4bv64)));

label_0x3337:
origDEST_95 := RAX[32:0];
origCOUNT_96 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), CF, RSHIFT_32(origDEST_95, (MINUS_32(32bv32, origCOUNT_96)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_96 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv32)), AF, unconstrained_46);

label_0x3339:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x333b:
origDEST_101 := RAX;
origCOUNT_102 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), CF, RSHIFT_64(origDEST_101, (MINUS_64(64bv64, origCOUNT_102)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_102 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), AF, unconstrained_48);

label_0x333f:
R8 := RAX;

label_0x3342:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_49;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3344:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x334c:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 128bv64));

label_0x3353:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13144bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3358"} true;
call arbitrary_func();

label_0x3358:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3360:
t1_107 := RAX;
t2_108 := 170bv64;
RAX := PLUS_64(RAX, t2_108);
CF := bool2bv(LT_64(RAX, t1_107));
OF := AND_1((bool2bv((t1_107[64:63]) == (t2_108[64:63]))), (XOR_1((t1_107[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_107)), t2_108)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3366:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x336b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3370:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_50;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3376:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x337b:
t_115 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))))[1:0]));
SF := t_115[64:63];
ZF := bool2bv(0bv64 == t_115);

label_0x337e:
if (bv2bool(ZF)) {
  goto label_0x3381;
}

label_0x3380:
assume false;

label_0x3381:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3386:
origDEST_119 := RAX;
origCOUNT_120 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), CF, LSHIFT_64(origDEST_119, (MINUS_64(64bv64, origCOUNT_120)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_120 == 1bv64)), origDEST_119[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), AF, unconstrained_53);

label_0x338a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3391:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3395:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x339a:
origDEST_125 := RCX;
origCOUNT_126 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_54));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_55);

label_0x339e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_56;
SF := unconstrained_57;
AF := unconstrained_58;
PF := unconstrained_59;

label_0x33a2:
if (bv2bool(CF)) {
  goto label_0x33a5;
}

label_0x33a4:
assume false;

label_0x33a5:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_60;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x33a7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x33ac:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x33af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x33b7:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 170bv64))));

label_0x33be:
t_131 := RAX[32:0][16:0];
RAX := (RAX[64:16]) ++ (PLUS_16((RAX[32:0][16:0]), 1bv16));
OF := AND_1((bool2bv((t_131[16:15]) == (1bv16[16:15]))), (XOR_1((t_131[16:15]), (RAX[32:0][16:0][16:15]))));
AF := bool2bv(16bv16 == (AND_16(16bv16, (XOR_16((XOR_16((RAX[32:0][16:0]), t_131)), 1bv16)))));
PF := NOT_1((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))), 1bv16)), (XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))))[1:0]));
SF := RAX[32:0][16:0][16:15];
ZF := bool2bv(0bv16 == (RAX[32:0][16:0]));

label_0x33c1:
mem := STORE_LE_16(mem, PLUS_64(RSP, 40bv64), RAX[32:0][16:0]);

label_0x33c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x33ce:
t1_135 := RAX;
t2_136 := 170bv64;
RAX := PLUS_64(RAX, t2_136);
CF := bool2bv(LT_64(RAX, t1_135));
OF := AND_1((bool2bv((t1_135[64:63]) == (t2_136[64:63]))), (XOR_1((t1_135[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_135)), t2_136)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33d4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x33d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x33de:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33e4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x33e9:
t_143 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x33ec:
if (bv2bool(ZF)) {
  goto label_0x33ef;
}

label_0x33ee:
assume false;

label_0x33ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x33f4:
origDEST_147 := RAX;
origCOUNT_148 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), CF, LSHIFT_64(origDEST_147, (MINUS_64(64bv64, origCOUNT_148)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_148 == 1bv64)), origDEST_147[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), AF, unconstrained_64);

label_0x33f8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x33ff:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3403:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3408:
origDEST_153 := RCX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_66);

label_0x340c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x3410:
if (bv2bool(CF)) {
  goto label_0x3413;
}

label_0x3412:
assume false;

label_0x3413:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3418:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 40bv64))));

label_0x341d:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x3420:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x3428:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x342f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3437:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13372bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x343c"} true;
call arbitrary_func();

label_0x343c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), RAX[32:0]);

label_0x3440:
RAX := (0bv32 ++ 4bv32);

label_0x3445:
t_159 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_159[64:0];
OF := bool2bv(t_159 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_159 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_71;
SF := unconstrained_72;
ZF := unconstrained_73;
AF := unconstrained_74;

label_0x3449:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3451:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 136bv64));

label_0x3458:
t1_161 := RCX;
t2_162 := RAX;
RCX := PLUS_64(RCX, t2_162);
CF := bool2bv(LT_64(RCX, t1_161));
OF := AND_1((bool2bv((t1_161[64:63]) == (t2_162[64:63]))), (XOR_1((t1_161[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_161)), t2_162)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x345b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0x3460:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3465:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x346b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3470:
t_169 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_76;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)), 2bv64)), (XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)), 2bv64)), (XOR_64((RSHIFT_64(t_169, 4bv64)), t_169)))))[1:0]));
SF := t_169[64:63];
ZF := bool2bv(0bv64 == t_169);

label_0x3473:
if (bv2bool(ZF)) {
  goto label_0x3476;
}

label_0x3475:
assume false;

label_0x3476:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x347b:
origDEST_173 := RAX;
origCOUNT_174 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), CF, LSHIFT_64(origDEST_173, (MINUS_64(64bv64, origCOUNT_174)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv64)), origDEST_173[64:63], unconstrained_77));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv64)), AF, unconstrained_78);

label_0x347f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3486:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x348a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x348f:
origDEST_179 := RCX;
origCOUNT_180 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), CF, LSHIFT_64(origDEST_179, (MINUS_64(64bv64, origCOUNT_180)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_180 == 1bv64)), origDEST_179[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), AF, unconstrained_80);

label_0x3493:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_81;
SF := unconstrained_82;
AF := unconstrained_83;
PF := unconstrained_84;

label_0x3497:
if (bv2bool(CF)) {
  goto label_0x349a;
}

label_0x3499:
assume false;

label_0x349a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x349f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 116bv64)));

label_0x34a3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x34a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x34ad:
t1_185 := RAX;
t2_186 := 170bv64;
RAX := PLUS_64(RAX, t2_186);
CF := bool2bv(LT_64(RAX, t1_185));
OF := AND_1((bool2bv((t1_185[64:63]) == (t2_186[64:63]))), (XOR_1((t1_185[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_185)), t2_186)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x34b3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x34bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x34c3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x34c6:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x34c9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x34d0:
origDEST_191 := RAX[32:0];
origCOUNT_192 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), CF, RSHIFT_32(origDEST_191, (MINUS_32(32bv32, origCOUNT_192)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv32)), AF, unconstrained_86);

label_0x34d2:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x34d9:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x34db:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x34e3:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 128bv64));

label_0x34ea:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x34ee:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x34f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x34f8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_88;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x34fe:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3503:
t_201 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_89;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)), 2bv64)), (XOR_64((RSHIFT_64(t_201, 4bv64)), t_201)))))[1:0]));
SF := t_201[64:63];
ZF := bool2bv(0bv64 == t_201);

label_0x3506:
if (bv2bool(ZF)) {
  goto label_0x3509;
}

label_0x3508:
assume false;

label_0x3509:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x350e:
origDEST_205 := RAX;
origCOUNT_206 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_91);

label_0x3512:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3519:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x351d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3522:
origDEST_211 := RCX;
origCOUNT_212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), CF, LSHIFT_64(origDEST_211, (MINUS_64(64bv64, origCOUNT_212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv64)), origDEST_211[64:63], unconstrained_92));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), AF, unconstrained_93);

label_0x3526:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_94;
SF := unconstrained_95;
AF := unconstrained_96;
PF := unconstrained_97;

label_0x352a:
if (bv2bool(CF)) {
  goto label_0x352d;
}

label_0x352c:
assume false;

label_0x352d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3532:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x353a:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x353d:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x3540:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3548:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0x354b:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x354e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 176bv64)));

label_0x3555:
origDEST_217 := RAX[32:0];
origCOUNT_218 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), CF, RSHIFT_32(origDEST_217, (MINUS_32(32bv32, origCOUNT_218)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv32)), AF, unconstrained_99);

label_0x3557:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x355e:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3560:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3568:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 128bv64));

label_0x356f:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x3573:
t1_225 := RAX;
t2_226 := 2bv64;
RAX := PLUS_64(RAX, t2_226);
CF := bool2bv(LT_64(RAX, t1_225));
OF := AND_1((bool2bv((t1_225[64:63]) == (t2_226[64:63]))), (XOR_1((t1_225[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_225)), t2_226)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3577:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x357c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3581:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3587:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x358c:
t_233 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))))[1:0]));
SF := t_233[64:63];
ZF := bool2bv(0bv64 == t_233);

label_0x358f:
if (bv2bool(ZF)) {
  goto label_0x3592;
}

label_0x3591:
assume false;

label_0x3592:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3597:
origDEST_237 := RAX;
origCOUNT_238 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), CF, LSHIFT_64(origDEST_237, (MINUS_64(64bv64, origCOUNT_238)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_238 == 1bv64)), origDEST_237[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), AF, unconstrained_104);

label_0x359b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x35a2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x35a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x35ab:
origDEST_243 := RCX;
origCOUNT_244 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_105));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_106);

label_0x35af:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_107;
SF := unconstrained_108;
AF := unconstrained_109;
PF := unconstrained_110;

label_0x35b3:
if (bv2bool(CF)) {
  goto label_0x35b6;
}

label_0x35b5:
assume false;

label_0x35b6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_111;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x35b8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x35bd:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x35c0:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x35c5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0x35cd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x35d5:
t1_249 := RAX;
t2_250 := 160bv64;
RAX := PLUS_64(RAX, t2_250);
CF := bool2bv(LT_64(RAX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x35db:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x35e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x35e5:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_112;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x35eb:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x35f0:
t_257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_113;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))))[1:0]));
SF := t_257[64:63];
ZF := bool2bv(0bv64 == t_257);

label_0x35f3:
if (bv2bool(ZF)) {
  goto label_0x35f6;
}

label_0x35f5:
assume false;

label_0x35f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x35fb:
origDEST_261 := RAX;
origCOUNT_262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_115);

label_0x35ff:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3606:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x360a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x360f:
origDEST_267 := RCX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_116));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_117);

label_0x3613:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_118;
SF := unconstrained_119;
AF := unconstrained_120;
PF := unconstrained_121;

label_0x3617:
if (bv2bool(CF)) {
  goto label_0x361a;
}

label_0x3619:
assume false;

label_0x361a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x361f:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x3622:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x362a:
t1_273 := RAX;
t2_274 := 168bv64;
RAX := PLUS_64(RAX, t2_274);
CF := bool2bv(LT_64(RAX, t1_273));
OF := AND_1((bool2bv((t1_273[64:63]) == (t2_274[64:63]))), (XOR_1((t1_273[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_273)), t2_274)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3630:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x3635:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x363a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_122;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3640:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3645:
t_281 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_123;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))))[1:0]));
SF := t_281[64:63];
ZF := bool2bv(0bv64 == t_281);

label_0x3648:
if (bv2bool(ZF)) {
  goto label_0x364b;
}

label_0x364a:
assume false;

label_0x364b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3650:
origDEST_285 := RAX;
origCOUNT_286 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), CF, LSHIFT_64(origDEST_285, (MINUS_64(64bv64, origCOUNT_286)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_286 == 1bv64)), origDEST_285[64:63], unconstrained_124));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), AF, unconstrained_125);

label_0x3654:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x365b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x365f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3664:
origDEST_291 := RCX;
origCOUNT_292 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_127);

label_0x3668:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_128;
SF := unconstrained_129;
AF := unconstrained_130;
PF := unconstrained_131;

label_0x366c:
if (bv2bool(CF)) {
  goto label_0x366f;
}

label_0x366e:
assume false;

label_0x366f:
RAX := (0bv32 ++ 1bv32);

label_0x3674:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3679:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x367c:
t_297 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_297)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_297, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)), 2bv32)), (XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)), 2bv32)), (XOR_32((RSHIFT_32(t_297, 4bv32)), t_297)))))[1:0]));
SF := t_297[32:31];
ZF := bool2bv(0bv32 == t_297);

label_0x3681:
if (bv2bool(ZF)) {
  goto label_0x3791;
}

label_0x3687:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x368f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 160bv64))));

label_0x3696:
t_301 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)), 2bv32)), (XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)), 2bv32)), (XOR_32((RSHIFT_32(t_301, 4bv32)), t_301)))))[1:0]));
SF := t_301[32:31];
ZF := bool2bv(0bv32 == t_301);

label_0x3698:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3791;
}

label_0x369e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x36a3:
t_305 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_305, 4bv32)), t_305)), 2bv32)), (XOR_32((RSHIFT_32(t_305, 4bv32)), t_305)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_305, 4bv32)), t_305)), 2bv32)), (XOR_32((RSHIFT_32(t_305, 4bv32)), t_305)))))[1:0]));
SF := t_305[32:31];
ZF := bool2bv(0bv32 == t_305);

label_0x36a5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x36e2;
}

label_0x36a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x36af:
R9 := LOAD_LE_64(mem, PLUS_64(RAX, 144bv64));

label_0x36b6:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x36bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x36c3:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 136bv64));

label_0x36ca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x36d2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14039bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x36d7"} true;
call arbitrary_func();

label_0x36d7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x36db:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x36e0:
goto label_0x371b;

label_0x36e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x36ea:
R9 := LOAD_LE_64(mem, PLUS_64(RAX, 136bv64));

label_0x36f1:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x36f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x36fe:
RDX := LOAD_LE_64(mem, PLUS_64(RAX, 144bv64));

label_0x3705:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x370d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14098bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3712"} true;
call arbitrary_func();

label_0x3712:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x3716:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x371b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3723:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RAX, 168bv64))));

label_0x372a:
t_309 := RAX[32:0][16:0];
RAX := (RAX[64:16]) ++ (PLUS_16((RAX[32:0][16:0]), 1bv16));
OF := AND_1((bool2bv((t_309[16:15]) == (1bv16[16:15]))), (XOR_1((t_309[16:15]), (RAX[32:0][16:0][16:15]))));
AF := bool2bv(16bv16 == (AND_16(16bv16, (XOR_16((XOR_16((RAX[32:0][16:0]), t_309)), 1bv16)))));
PF := NOT_1((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))), 1bv16)), (XOR_16((RSHIFT_16((XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))), 2bv16)), (XOR_16((RSHIFT_16((RAX[32:0][16:0]), 4bv16)), (RAX[32:0][16:0]))))))[1:0]));
SF := RAX[32:0][16:0][16:15];
ZF := bool2bv(0bv16 == (RAX[32:0][16:0]));

label_0x372d:
mem := STORE_LE_16(mem, PLUS_64(RSP, 42bv64), RAX[32:0][16:0]);

label_0x3732:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x373a:
t1_313 := RAX;
t2_314 := 168bv64;
RAX := PLUS_64(RAX, t2_314);
CF := bool2bv(LT_64(RAX, t1_313));
OF := AND_1((bool2bv((t1_313[64:63]) == (t2_314[64:63]))), (XOR_1((t1_313[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_313)), t2_314)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3740:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x3745:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x374a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_134;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3750:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3755:
t_321 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))))[1:0]));
SF := t_321[64:63];
ZF := bool2bv(0bv64 == t_321);

label_0x3758:
if (bv2bool(ZF)) {
  goto label_0x375b;
}

label_0x375a:
assume false;

label_0x375b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3760:
origDEST_325 := RAX;
origCOUNT_326 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_136));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_137);

label_0x3764:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x376b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x376f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3774:
origDEST_331 := RCX;
origCOUNT_332 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), CF, LSHIFT_64(origDEST_331, (MINUS_64(64bv64, origCOUNT_332)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_332 == 1bv64)), origDEST_331[64:63], unconstrained_138));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), AF, unconstrained_139);

label_0x3778:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_140;
SF := unconstrained_141;
AF := unconstrained_142;
PF := unconstrained_143;

label_0x377c:
if (bv2bool(CF)) {
  goto label_0x377f;
}

label_0x377e:
assume false;

label_0x377f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3784:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 42bv64))));

label_0x3789:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x378c:
goto label_0x367c;

label_0x3791:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3799:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x379f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x37a7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14252bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x37ac"} true;
call arbitrary_func();

label_0x37ac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x37b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x37b8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_144;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37be:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x37c3:
t_339 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_145;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))))[1:0]));
SF := t_339[64:63];
ZF := bool2bv(0bv64 == t_339);

label_0x37c6:
if (bv2bool(ZF)) {
  goto label_0x37c9;
}

label_0x37c8:
assume false;

label_0x37c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x37d1:
origDEST_343 := RAX;
origCOUNT_344 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), CF, LSHIFT_64(origDEST_343, (MINUS_64(64bv64, origCOUNT_344)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_344 == 1bv64)), origDEST_343[64:63], unconstrained_146));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), AF, unconstrained_147);

label_0x37d5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x37dc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x37e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x37e8:
origDEST_349 := RCX;
origCOUNT_350 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, LSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), origDEST_349[64:63], unconstrained_148));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_149);

label_0x37ec:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_150;
SF := unconstrained_151;
AF := unconstrained_152;
PF := unconstrained_153;

label_0x37f0:
if (bv2bool(CF)) {
  goto label_0x37f3;
}

label_0x37f2:
assume false;

label_0x37f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x37fb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x37ff:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3801:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3809:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 164bv64)));

label_0x380f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3817:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14364bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x381c"} true;
call arbitrary_func();

label_0x381c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x3820:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3828:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_154;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x382e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3833:
t_357 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_155;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)), 2bv64)), (XOR_64((RSHIFT_64(t_357, 4bv64)), t_357)))))[1:0]));
SF := t_357[64:63];
ZF := bool2bv(0bv64 == t_357);

label_0x3836:
if (bv2bool(ZF)) {
  goto label_0x3839;
}

label_0x3838:
assume false;

label_0x3839:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3841:
origDEST_361 := RAX;
origCOUNT_362 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), CF, LSHIFT_64(origDEST_361, (MINUS_64(64bv64, origCOUNT_362)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_362 == 1bv64)), origDEST_361[64:63], unconstrained_156));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), AF, unconstrained_157);

label_0x3845:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x384c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3850:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3858:
origDEST_367 := RCX;
origCOUNT_368 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, LSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), origDEST_367[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_159);

label_0x385c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_160;
SF := unconstrained_161;
AF := unconstrained_162;
PF := unconstrained_163;

label_0x3860:
if (bv2bool(CF)) {
  goto label_0x3863;
}

label_0x3862:
assume false;

label_0x3863:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x386b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 124bv64)));

label_0x386f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3871:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3879:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 160bv64))));

label_0x3880:
t1_373 := RSP;
t2_374 := 152bv64;
RSP := PLUS_64(RSP, t2_374);
CF := bool2bv(LT_64(RSP, t1_373));
OF := AND_1((bool2bv((t1_373[64:63]) == (t2_374[64:63]))), (XOR_1((t1_373[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_373)), t2_374)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3887:

ra_379 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_102,origCOUNT_120,origCOUNT_126,origCOUNT_148,origCOUNT_154,origCOUNT_16,origCOUNT_174,origCOUNT_180,origCOUNT_192,origCOUNT_206,origCOUNT_212,origCOUNT_218,origCOUNT_22,origCOUNT_238,origCOUNT_244,origCOUNT_262,origCOUNT_268,origCOUNT_286,origCOUNT_292,origCOUNT_326,origCOUNT_332,origCOUNT_34,origCOUNT_344,origCOUNT_350,origCOUNT_362,origCOUNT_368,origCOUNT_40,origCOUNT_56,origCOUNT_62,origCOUNT_74,origCOUNT_80,origCOUNT_90,origCOUNT_96,origDEST_101,origDEST_119,origDEST_125,origDEST_147,origDEST_15,origDEST_153,origDEST_173,origDEST_179,origDEST_191,origDEST_205,origDEST_21,origDEST_211,origDEST_217,origDEST_237,origDEST_243,origDEST_261,origDEST_267,origDEST_285,origDEST_291,origDEST_325,origDEST_33,origDEST_331,origDEST_343,origDEST_349,origDEST_361,origDEST_367,origDEST_39,origDEST_55,origDEST_61,origDEST_73,origDEST_79,origDEST_89,origDEST_95,ra_379,t1_107,t1_135,t1_161,t1_185,t1_225,t1_249,t1_273,t1_313,t1_373,t2_108,t2_136,t2_162,t2_186,t2_226,t2_250,t2_274,t2_314,t2_374,t_1,t_11,t_115,t_131,t_143,t_159,t_169,t_201,t_233,t_257,t_281,t_29,t_297,t_301,t_305,t_309,t_321,t_339,t_357,t_45,t_5,t_51,t_69,t_85;

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
var origCOUNT_120: bv64;
var origCOUNT_126: bv64;
var origCOUNT_148: bv64;
var origCOUNT_154: bv64;
var origCOUNT_16: bv64;
var origCOUNT_174: bv64;
var origCOUNT_180: bv64;
var origCOUNT_192: bv32;
var origCOUNT_206: bv64;
var origCOUNT_212: bv64;
var origCOUNT_218: bv32;
var origCOUNT_22: bv64;
var origCOUNT_238: bv64;
var origCOUNT_244: bv64;
var origCOUNT_262: bv64;
var origCOUNT_268: bv64;
var origCOUNT_286: bv64;
var origCOUNT_292: bv64;
var origCOUNT_326: bv64;
var origCOUNT_332: bv64;
var origCOUNT_34: bv64;
var origCOUNT_344: bv64;
var origCOUNT_350: bv64;
var origCOUNT_362: bv64;
var origCOUNT_368: bv64;
var origCOUNT_40: bv64;
var origCOUNT_56: bv64;
var origCOUNT_62: bv64;
var origCOUNT_74: bv64;
var origCOUNT_80: bv64;
var origCOUNT_90: bv32;
var origCOUNT_96: bv32;
var origDEST_101: bv64;
var origDEST_119: bv64;
var origDEST_125: bv64;
var origDEST_147: bv64;
var origDEST_15: bv64;
var origDEST_153: bv64;
var origDEST_173: bv64;
var origDEST_179: bv64;
var origDEST_191: bv32;
var origDEST_205: bv64;
var origDEST_21: bv64;
var origDEST_211: bv64;
var origDEST_217: bv32;
var origDEST_237: bv64;
var origDEST_243: bv64;
var origDEST_261: bv64;
var origDEST_267: bv64;
var origDEST_285: bv64;
var origDEST_291: bv64;
var origDEST_325: bv64;
var origDEST_33: bv64;
var origDEST_331: bv64;
var origDEST_343: bv64;
var origDEST_349: bv64;
var origDEST_361: bv64;
var origDEST_367: bv64;
var origDEST_39: bv64;
var origDEST_55: bv64;
var origDEST_61: bv64;
var origDEST_73: bv64;
var origDEST_79: bv64;
var origDEST_89: bv32;
var origDEST_95: bv32;
var ra_379: bv64;
var t1_107: bv64;
var t1_135: bv64;
var t1_161: bv64;
var t1_185: bv64;
var t1_225: bv64;
var t1_249: bv64;
var t1_273: bv64;
var t1_313: bv64;
var t1_373: bv64;
var t2_108: bv64;
var t2_136: bv64;
var t2_162: bv64;
var t2_186: bv64;
var t2_226: bv64;
var t2_250: bv64;
var t2_274: bv64;
var t2_314: bv64;
var t2_374: bv64;
var t_1: bv64;
var t_11: bv64;
var t_115: bv64;
var t_131: bv16;
var t_143: bv64;
var t_159: bv128;
var t_169: bv64;
var t_201: bv64;
var t_233: bv64;
var t_257: bv64;
var t_281: bv64;
var t_29: bv64;
var t_297: bv32;
var t_301: bv32;
var t_305: bv32;
var t_309: bv16;
var t_321: bv64;
var t_339: bv64;
var t_357: bv64;
var t_45: bv32;
var t_5: bv32;
var t_51: bv64;
var t_69: bv64;
var t_85: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(96bv64);
axiom policy(656bv64);
axiom policy(5408bv64);
axiom policy(6768bv64);
axiom policy(12448bv64);
axiom policy(12592bv64);
axiom policy(14480bv64);
