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
axiom _function_addr_low == 12624bv64;
axiom _function_addr_high == 15504bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x3150:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x3155:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x315a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x315f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x3164:
t_1 := RSP;
RSP := MINUS_64(RSP, 200bv64);
CF := bool2bv(LT_64(t_1, 200bv64));
OF := AND_64((XOR_64(t_1, 200bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 200bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x316b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x3173:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x3178:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x3181:
if (bv2bool(ZF)) {
  goto label_0x31d4;
}

label_0x3183:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x318b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3191:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3196:
t_11 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x3199:
if (bv2bool(ZF)) {
  goto label_0x319c;
}

label_0x319b:
assume false;

label_0x319c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x31a4:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_4);

label_0x31a8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x31af:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x31b3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x31bb:
origDEST_21 := RCX;
origCOUNT_22 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_6);

label_0x31bf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x31c3:
if (bv2bool(CF)) {
  goto label_0x31c6;
}

label_0x31c5:
assume false;

label_0x31c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x31ce:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x31d4:
t_27 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_27)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_27, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x31da:
if (bv2bool(ZF)) {
  goto label_0x3231;
}

label_0x31dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x31e1:
t1_31 := RAX;
t2_32 := 5096bv64;
RAX := PLUS_64(RAX, t2_32);
CF := bool2bv(LT_64(RAX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x31ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x31f1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31f7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x31fc:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x31ff:
if (bv2bool(ZF)) {
  goto label_0x3202;
}

label_0x3201:
assume false;

label_0x3202:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3207:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0x320b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3212:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3216:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x321b:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_16);

label_0x321f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x3223:
if (bv2bool(CF)) {
  goto label_0x3226;
}

label_0x3225:
assume false;

label_0x3226:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x322b:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3231:
t_55 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_55)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_55, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))))[1:0]));
SF := t_55[64:63];
ZF := bool2bv(0bv64 == t_55);

label_0x3237:
if (bv2bool(ZF)) {
  goto label_0x3252;
}

label_0x3239:
t_59 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))), t_59)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_59, (LOAD_LE_64(mem, PLUS_64(RSP, 224bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))))[1:0]));
SF := t_59[64:63];
ZF := bool2bv(0bv64 == t_59);

label_0x3242:
if (bv2bool(ZF)) {
  goto label_0x3252;
}

label_0x3244:
t_63 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), t_63)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_63, (LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x324c:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x3312;
}

label_0x3252:
t_67 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_67)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_67, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x325b:
if (bv2bool(ZF)) {
  goto label_0x32ae;
}

label_0x325d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3265:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x326b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3270:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0x3273:
if (bv2bool(ZF)) {
  goto label_0x3276;
}

label_0x3275:
assume false;

label_0x3276:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x327e:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_24);

label_0x3282:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3289:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x328d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3295:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_26);

label_0x3299:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x329d:
if (bv2bool(CF)) {
  goto label_0x32a0;
}

label_0x329f:
assume false;

label_0x32a0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x32a8:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x32ae:
t_89 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_89)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_89, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))))[1:0]));
SF := t_89[64:63];
ZF := bool2bv(0bv64 == t_89);

label_0x32b4:
if (bv2bool(ZF)) {
  goto label_0x330b;
}

label_0x32b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x32bb:
t1_93 := RAX;
t2_94 := 5096bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x32c1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x32c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x32cb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x32d1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x32d6:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x32d9:
if (bv2bool(ZF)) {
  goto label_0x32dc;
}

label_0x32db:
assume false;

label_0x32dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x32e1:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_34);

label_0x32e5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x32ec:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x32f0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x32f5:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_36);

label_0x32f9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x32fd:
if (bv2bool(CF)) {
  goto label_0x3300;
}

label_0x32ff:
assume false;

label_0x3300:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3305:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x330b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_41;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x330d:
goto label_0x3c82;

label_0x3312:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3317:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 5008bv64))));

label_0x331e:
t_117 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x3320:
if (bv2bool(ZF)) {
  goto label_0x33e6;
}

label_0x3326:
t_121 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_121)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_121, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x332f:
if (bv2bool(ZF)) {
  goto label_0x3382;
}

label_0x3331:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3339:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x333f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3344:
t_127 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))))[1:0]));
SF := t_127[64:63];
ZF := bool2bv(0bv64 == t_127);

label_0x3347:
if (bv2bool(ZF)) {
  goto label_0x334a;
}

label_0x3349:
assume false;

label_0x334a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3352:
origDEST_131 := RAX;
origCOUNT_132 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_46);

label_0x3356:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x335d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3361:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3369:
origDEST_137 := RCX;
origCOUNT_138 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), CF, LSHIFT_64(origDEST_137, (MINUS_64(64bv64, origCOUNT_138)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv64)), origDEST_137[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), AF, unconstrained_48);

label_0x336d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_49;
SF := unconstrained_50;
AF := unconstrained_51;
PF := unconstrained_52;

label_0x3371:
if (bv2bool(CF)) {
  goto label_0x3374;
}

label_0x3373:
assume false;

label_0x3374:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x337c:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x3382:
t_143 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_143)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_143, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x3388:
if (bv2bool(ZF)) {
  goto label_0x33df;
}

label_0x338a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x338f:
t1_147 := RAX;
t2_148 := 5096bv64;
RAX := PLUS_64(RAX, t2_148);
CF := bool2bv(LT_64(RAX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3395:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x339a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x339f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33a5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x33aa:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x33ad:
if (bv2bool(ZF)) {
  goto label_0x33b0;
}

label_0x33af:
assume false;

label_0x33b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x33b5:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_56);

label_0x33b9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x33c0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x33c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x33c9:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_58);

label_0x33cd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_59;
SF := unconstrained_60;
AF := unconstrained_61;
PF := unconstrained_62;

label_0x33d1:
if (bv2bool(CF)) {
  goto label_0x33d4;
}

label_0x33d3:
assume false;

label_0x33d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x33d9:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x33df:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_63;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x33e1:
goto label_0x3c82;

label_0x33e6:
t_171 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))), t_171)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_171, (LOAD_LE_32(mem, PLUS_64(RSP, 232bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))))[1:0]));
SF := t_171[32:31];
ZF := bool2bv(0bv32 == t_171);

label_0x33ee:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x34b4;
}

label_0x33f4:
t_175 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_175)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_175, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))))[1:0]));
SF := t_175[64:63];
ZF := bool2bv(0bv64 == t_175);

label_0x33fd:
if (bv2bool(ZF)) {
  goto label_0x3450;
}

label_0x33ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3407:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_64;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x340d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3412:
t_181 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))))[1:0]));
SF := t_181[64:63];
ZF := bool2bv(0bv64 == t_181);

label_0x3415:
if (bv2bool(ZF)) {
  goto label_0x3418;
}

label_0x3417:
assume false;

label_0x3418:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3420:
origDEST_185 := RAX;
origCOUNT_186 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), CF, LSHIFT_64(origDEST_185, (MINUS_64(64bv64, origCOUNT_186)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv64)), origDEST_185[64:63], unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), AF, unconstrained_67);

label_0x3424:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x342b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x342f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3437:
origDEST_191 := RCX;
origCOUNT_192 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_68));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_69);

label_0x343b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_70;
SF := unconstrained_71;
AF := unconstrained_72;
PF := unconstrained_73;

label_0x343f:
if (bv2bool(CF)) {
  goto label_0x3442;
}

label_0x3441:
assume false;

label_0x3442:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x344a:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3450:
t_197 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_197)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_197, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))))[1:0]));
SF := t_197[64:63];
ZF := bool2bv(0bv64 == t_197);

label_0x3456:
if (bv2bool(ZF)) {
  goto label_0x34ad;
}

label_0x3458:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x345d:
t1_201 := RAX;
t2_202 := 5096bv64;
RAX := PLUS_64(RAX, t2_202);
CF := bool2bv(LT_64(RAX, t1_201));
OF := AND_1((bool2bv((t1_201[64:63]) == (t2_202[64:63]))), (XOR_1((t1_201[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_201)), t2_202)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3463:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x3468:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x346d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_74;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3473:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3478:
t_209 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))))[1:0]));
SF := t_209[64:63];
ZF := bool2bv(0bv64 == t_209);

label_0x347b:
if (bv2bool(ZF)) {
  goto label_0x347e;
}

label_0x347d:
assume false;

label_0x347e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3483:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_77);

label_0x3487:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x348e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3492:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3497:
origDEST_219 := RCX;
origCOUNT_220 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), CF, LSHIFT_64(origDEST_219, (MINUS_64(64bv64, origCOUNT_220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv64)), origDEST_219[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), AF, unconstrained_79);

label_0x349b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_80;
SF := unconstrained_81;
AF := unconstrained_82;
PF := unconstrained_83;

label_0x349f:
if (bv2bool(CF)) {
  goto label_0x34a2;
}

label_0x34a1:
assume false;

label_0x34a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x34a7:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x34ad:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_84;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x34af:
goto label_0x3c82;

label_0x34b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x34b9:
t1_225 := RAX;
t2_226 := 5048bv64;
RAX := PLUS_64(RAX, t2_226);
CF := bool2bv(LT_64(RAX, t1_225));
OF := AND_1((bool2bv((t1_225[64:63]) == (t2_226[64:63]))), (XOR_1((t1_225[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_225)), t2_226)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x34bf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x34c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x34c9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_85;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x34cf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x34d4:
t_233 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)), 2bv64)), (XOR_64((RSHIFT_64(t_233, 4bv64)), t_233)))))[1:0]));
SF := t_233[64:63];
ZF := bool2bv(0bv64 == t_233);

label_0x34d7:
if (bv2bool(ZF)) {
  goto label_0x34da;
}

label_0x34d9:
assume false;

label_0x34da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x34df:
origDEST_237 := RAX;
origCOUNT_238 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), CF, LSHIFT_64(origDEST_237, (MINUS_64(64bv64, origCOUNT_238)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_238 == 1bv64)), origDEST_237[64:63], unconstrained_87));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), AF, unconstrained_88);

label_0x34e3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x34ea:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x34ee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x34f3:
origDEST_243 := RCX;
origCOUNT_244 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_89));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_90);

label_0x34f7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_91;
SF := unconstrained_92;
AF := unconstrained_93;
PF := unconstrained_94;

label_0x34fb:
if (bv2bool(CF)) {
  goto label_0x34fe;
}

label_0x34fd:
assume false;

label_0x34fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3503:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 232bv64)));

label_0x350a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x350c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3511:
t1_249 := RAX;
t2_250 := 5040bv64;
RAX := PLUS_64(RAX, t2_250);
CF := bool2bv(LT_64(RAX, t1_249));
OF := AND_1((bool2bv((t1_249[64:63]) == (t2_250[64:63]))), (XOR_1((t1_249[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_249)), t2_250)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3517:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x351c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3521:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3527:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x352c:
t_257 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)), 2bv64)), (XOR_64((RSHIFT_64(t_257, 4bv64)), t_257)))))[1:0]));
SF := t_257[64:63];
ZF := bool2bv(0bv64 == t_257);

label_0x352f:
if (bv2bool(ZF)) {
  goto label_0x3532;
}

label_0x3531:
assume false;

label_0x3532:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3537:
origDEST_261 := RAX;
origCOUNT_262 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_97));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_98);

label_0x353b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3542:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3546:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x354b:
origDEST_267 := RCX;
origCOUNT_268 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_99));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_100);

label_0x354f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_101;
SF := unconstrained_102;
AF := unconstrained_103;
PF := unconstrained_104;

label_0x3553:
if (bv2bool(CF)) {
  goto label_0x3556;
}

label_0x3555:
assume false;

label_0x3556:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x355b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x3563:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3566:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_105;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3568:
t_273 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_273)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_273, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)), 2bv32)), (XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)), 2bv32)), (XOR_32((RSHIFT_32(t_273, 4bv32)), t_273)))))[1:0]));
SF := t_273[32:31];
ZF := bool2bv(0bv32 == t_273);

label_0x356b:
if (bv2bool(ZF)) {
  goto label_0x3c80;
}

label_0x3571:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_106;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3573:
t_277 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)), 2bv32)), (XOR_32((RSHIFT_32(t_277, 4bv32)), t_277)))))[1:0]));
SF := t_277[32:31];
ZF := bool2bv(0bv32 == t_277);

label_0x3575:
if (bv2bool(ZF)) {
  goto label_0x363b;
}

label_0x357b:
t_281 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_281)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_281, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))))[1:0]));
SF := t_281[64:63];
ZF := bool2bv(0bv64 == t_281);

label_0x3584:
if (bv2bool(ZF)) {
  goto label_0x35d7;
}

label_0x3586:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x358e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_108;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3594:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3599:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_109;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x359c:
if (bv2bool(ZF)) {
  goto label_0x359f;
}

label_0x359e:
assume false;

label_0x359f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x35a7:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_111);

label_0x35ab:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x35b2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x35b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x35be:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_113);

label_0x35c2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_114;
SF := unconstrained_115;
AF := unconstrained_116;
PF := unconstrained_117;

label_0x35c6:
if (bv2bool(CF)) {
  goto label_0x35c9;
}

label_0x35c8:
assume false;

label_0x35c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x35d1:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x35d7:
t_303 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_303)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_303, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)), 2bv64)), (XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)), 2bv64)), (XOR_64((RSHIFT_64(t_303, 4bv64)), t_303)))))[1:0]));
SF := t_303[64:63];
ZF := bool2bv(0bv64 == t_303);

label_0x35dd:
if (bv2bool(ZF)) {
  goto label_0x3634;
}

label_0x35df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x35e4:
t1_307 := RAX;
t2_308 := 5096bv64;
RAX := PLUS_64(RAX, t2_308);
CF := bool2bv(LT_64(RAX, t1_307));
OF := AND_1((bool2bv((t1_307[64:63]) == (t2_308[64:63]))), (XOR_1((t1_307[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_307)), t2_308)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x35ea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x35ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x35f4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x35fa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x35ff:
t_315 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_119;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_315, 4bv64)), t_315)), 2bv64)), (XOR_64((RSHIFT_64(t_315, 4bv64)), t_315)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_315, 4bv64)), t_315)), 2bv64)), (XOR_64((RSHIFT_64(t_315, 4bv64)), t_315)))))[1:0]));
SF := t_315[64:63];
ZF := bool2bv(0bv64 == t_315);

label_0x3602:
if (bv2bool(ZF)) {
  goto label_0x3605;
}

label_0x3604:
assume false;

label_0x3605:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x360a:
origDEST_319 := RAX;
origCOUNT_320 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), CF, LSHIFT_64(origDEST_319, (MINUS_64(64bv64, origCOUNT_320)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_320 == 1bv64)), origDEST_319[64:63], unconstrained_120));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_320 == 0bv64)), AF, unconstrained_121);

label_0x360e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3615:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3619:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x361e:
origDEST_325 := RCX;
origCOUNT_326 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_122));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_123);

label_0x3622:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_124;
SF := unconstrained_125;
AF := unconstrained_126;
PF := unconstrained_127;

label_0x3626:
if (bv2bool(CF)) {
  goto label_0x3629;
}

label_0x3628:
assume false;

label_0x3629:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x362e:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x3634:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_128;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3636:
goto label_0x3c82;

label_0x363b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3640:
t_331 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), t_331)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_331, (LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))))[1:0]));
SF := t_331[32:31];
ZF := bool2bv(0bv32 == t_331);

label_0x3647:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3899;
}

label_0x364d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3652:
RCX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x3654:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13913bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3659"} true;
call arbitrary_func();

label_0x3659:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x365c:
t_335 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_129;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)), 2bv32)), (XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)), 2bv32)), (XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)))))[1:0]));
SF := t_335[32:31];
ZF := bool2bv(0bv32 == t_335);

label_0x365e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3899;
}

label_0x3664:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3669:
t1_339 := RAX;
t2_340 := 4bv64;
RAX := PLUS_64(RAX, t2_340);
CF := bool2bv(LT_64(RAX, t1_339));
OF := AND_1((bool2bv((t1_339[64:63]) == (t2_340[64:63]))), (XOR_1((t1_339[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_339)), t2_340)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x366d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3672:
R9 := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x3675:
R8 := (0bv32 ++ 5000bv32);

label_0x367b:
RDX := (0bv32 ++ 1bv32);

label_0x3680:
RCX := RAX;

label_0x3683:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13960bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3688"} true;
call arbitrary_func();

label_0x3688:
mem := STORE_LE_32(mem, PLUS_64(RSP, 168bv64), RAX[32:0]);

label_0x368f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_130;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3691:
t_345 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_131;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))))[1:0]));
SF := t_345[32:31];
ZF := bool2bv(0bv32 == t_345);

label_0x3693:
if (bv2bool(ZF)) {
  goto label_0x3759;
}

label_0x3699:
t_349 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_349)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_349, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)), 2bv64)), (XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)), 2bv64)), (XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)))))[1:0]));
SF := t_349[64:63];
ZF := bool2bv(0bv64 == t_349);

label_0x36a2:
if (bv2bool(ZF)) {
  goto label_0x36f5;
}

label_0x36a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x36ac:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x36b2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x36b7:
t_355 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)), 2bv64)), (XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)), 2bv64)), (XOR_64((RSHIFT_64(t_355, 4bv64)), t_355)))))[1:0]));
SF := t_355[64:63];
ZF := bool2bv(0bv64 == t_355);

label_0x36ba:
if (bv2bool(ZF)) {
  goto label_0x36bd;
}

label_0x36bc:
assume false;

label_0x36bd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x36c5:
origDEST_359 := RAX;
origCOUNT_360 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), CF, LSHIFT_64(origDEST_359, (MINUS_64(64bv64, origCOUNT_360)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_360 == 1bv64)), origDEST_359[64:63], unconstrained_134));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), AF, unconstrained_135);

label_0x36c9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x36d0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x36d4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x36dc:
origDEST_365 := RCX;
origCOUNT_366 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), CF, LSHIFT_64(origDEST_365, (MINUS_64(64bv64, origCOUNT_366)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_366 == 1bv64)), origDEST_365[64:63], unconstrained_136));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_366 == 0bv64)), AF, unconstrained_137);

label_0x36e0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_138;
SF := unconstrained_139;
AF := unconstrained_140;
PF := unconstrained_141;

label_0x36e4:
if (bv2bool(CF)) {
  goto label_0x36e7;
}

label_0x36e6:
assume false;

label_0x36e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x36ef:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x36f5:
t_371 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_371)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_371, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_371, 4bv64)), t_371)), 2bv64)), (XOR_64((RSHIFT_64(t_371, 4bv64)), t_371)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_371, 4bv64)), t_371)), 2bv64)), (XOR_64((RSHIFT_64(t_371, 4bv64)), t_371)))))[1:0]));
SF := t_371[64:63];
ZF := bool2bv(0bv64 == t_371);

label_0x36fb:
if (bv2bool(ZF)) {
  goto label_0x3752;
}

label_0x36fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3702:
t1_375 := RAX;
t2_376 := 5096bv64;
RAX := PLUS_64(RAX, t2_376);
CF := bool2bv(LT_64(RAX, t1_375));
OF := AND_1((bool2bv((t1_375[64:63]) == (t2_376[64:63]))), (XOR_1((t1_375[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_375)), t2_376)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3708:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x370d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3712:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_142;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3718:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x371d:
t_383 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_143;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_383, 4bv64)), t_383)), 2bv64)), (XOR_64((RSHIFT_64(t_383, 4bv64)), t_383)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_383, 4bv64)), t_383)), 2bv64)), (XOR_64((RSHIFT_64(t_383, 4bv64)), t_383)))))[1:0]));
SF := t_383[64:63];
ZF := bool2bv(0bv64 == t_383);

label_0x3720:
if (bv2bool(ZF)) {
  goto label_0x3723;
}

label_0x3722:
assume false;

label_0x3723:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3728:
origDEST_387 := RAX;
origCOUNT_388 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), CF, LSHIFT_64(origDEST_387, (MINUS_64(64bv64, origCOUNT_388)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_388 == 1bv64)), origDEST_387[64:63], unconstrained_144));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), AF, unconstrained_145);

label_0x372c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3733:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3737:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x373c:
origDEST_393 := RCX;
origCOUNT_394 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), CF, LSHIFT_64(origDEST_393, (MINUS_64(64bv64, origCOUNT_394)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_394 == 1bv64)), origDEST_393[64:63], unconstrained_146));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), AF, unconstrained_147);

label_0x3740:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_148;
SF := unconstrained_149;
AF := unconstrained_150;
PF := unconstrained_151;

label_0x3744:
if (bv2bool(CF)) {
  goto label_0x3747;
}

label_0x3746:
assume false;

label_0x3747:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x374c:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x3752:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_152;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3754:
goto label_0x3c82;

label_0x3759:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x375e:
t1_399 := RAX;
t2_400 := 5004bv64;
RAX := PLUS_64(RAX, t2_400);
CF := bool2bv(LT_64(RAX, t1_399));
OF := AND_1((bool2bv((t1_399[64:63]) == (t2_400[64:63]))), (XOR_1((t1_399[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_399)), t2_400)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3764:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x3769:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x376e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_153;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3774:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3779:
t_407 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_154;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)), 2bv64)), (XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)), 2bv64)), (XOR_64((RSHIFT_64(t_407, 4bv64)), t_407)))))[1:0]));
SF := t_407[64:63];
ZF := bool2bv(0bv64 == t_407);

label_0x377c:
if (bv2bool(ZF)) {
  goto label_0x377f;
}

label_0x377e:
assume false;

label_0x377f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3784:
origDEST_411 := RAX;
origCOUNT_412 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), CF, LSHIFT_64(origDEST_411, (MINUS_64(64bv64, origCOUNT_412)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_412 == 1bv64)), origDEST_411[64:63], unconstrained_155));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), AF, unconstrained_156);

label_0x3788:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x378f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3793:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3798:
origDEST_417 := RCX;
origCOUNT_418 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), CF, LSHIFT_64(origDEST_417, (MINUS_64(64bv64, origCOUNT_418)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_418 == 1bv64)), origDEST_417[64:63], unconstrained_157));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), AF, unconstrained_158);

label_0x379c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_159;
SF := unconstrained_160;
AF := unconstrained_161;
PF := unconstrained_162;

label_0x37a0:
if (bv2bool(CF)) {
  goto label_0x37a3;
}

label_0x37a2:
assume false;

label_0x37a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x37a8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x37af:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x37b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x37b6:
t1_423 := RAX;
t2_424 := 5004bv64;
RAX := PLUS_64(RAX, t2_424);
CF := bool2bv(LT_64(RAX, t1_423));
OF := AND_1((bool2bv((t1_423[64:63]) == (t2_424[64:63]))), (XOR_1((t1_423[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_423)), t2_424)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37bc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x37c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x37c9:
t1_429 := RAX;
t2_430 := 5024bv64;
RAX := PLUS_64(RAX, t2_430);
CF := bool2bv(LT_64(RAX, t1_429));
OF := AND_1((bool2bv((t1_429[64:63]) == (t2_430[64:63]))), (XOR_1((t1_429[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_429)), t2_430)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37cf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x37d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x37d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_163;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x37e4:
t_437 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_164;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))))[1:0]));
SF := t_437[64:63];
ZF := bool2bv(0bv64 == t_437);

label_0x37e7:
if (bv2bool(ZF)) {
  goto label_0x37ea;
}

label_0x37e9:
assume false;

label_0x37ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x37ef:
origDEST_441 := RAX;
origCOUNT_442 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), CF, LSHIFT_64(origDEST_441, (MINUS_64(64bv64, origCOUNT_442)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_442 == 1bv64)), origDEST_441[64:63], unconstrained_165));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), AF, unconstrained_166);

label_0x37f3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x37fa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x37fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3803:
origDEST_447 := RCX;
origCOUNT_448 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), CF, LSHIFT_64(origDEST_447, (MINUS_64(64bv64, origCOUNT_448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_448 == 1bv64)), origDEST_447[64:63], unconstrained_167));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), AF, unconstrained_168);

label_0x3807:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_169;
SF := unconstrained_170;
AF := unconstrained_171;
PF := unconstrained_172;

label_0x380b:
if (bv2bool(CF)) {
  goto label_0x380e;
}

label_0x380d:
assume false;

label_0x380e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3813:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x381b:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x381d:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x381f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3824:
t1_453 := RAX;
t2_454 := 4bv64;
RAX := PLUS_64(RAX, t2_454);
CF := bool2bv(LT_64(RAX, t1_453));
OF := AND_1((bool2bv((t1_453[64:63]) == (t2_454[64:63]))), (XOR_1((t1_453[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_453)), t2_454)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3828:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x3830:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3835:
t1_459 := RAX;
t2_460 := 5016bv64;
RAX := PLUS_64(RAX, t2_460);
CF := bool2bv(LT_64(RAX, t1_459));
OF := AND_1((bool2bv((t1_459[64:63]) == (t2_460[64:63]))), (XOR_1((t1_459[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_459)), t2_460)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x383b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x3843:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x384b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_173;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3851:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3856:
t_467 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_174;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))))[1:0]));
SF := t_467[64:63];
ZF := bool2bv(0bv64 == t_467);

label_0x3859:
if (bv2bool(ZF)) {
  goto label_0x385c;
}

label_0x385b:
assume false;

label_0x385c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3864:
origDEST_471 := RAX;
origCOUNT_472 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), CF, LSHIFT_64(origDEST_471, (MINUS_64(64bv64, origCOUNT_472)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_472 == 1bv64)), origDEST_471[64:63], unconstrained_175));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), AF, unconstrained_176);

label_0x3868:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x386f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3873:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x387b:
origDEST_477 := RCX;
origCOUNT_478 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), CF, LSHIFT_64(origDEST_477, (MINUS_64(64bv64, origCOUNT_478)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_478 == 1bv64)), origDEST_477[64:63], unconstrained_177));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), AF, unconstrained_178);

label_0x387f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_179;
SF := unconstrained_180;
AF := unconstrained_181;
PF := unconstrained_182;

label_0x3883:
if (bv2bool(CF)) {
  goto label_0x3886;
}

label_0x3885:
assume false;

label_0x3886:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x388e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3896:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3899:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x389e:
t1_483 := RAX;
t2_484 := 5016bv64;
RAX := PLUS_64(RAX, t2_484);
CF := bool2bv(LT_64(RAX, t1_483));
OF := AND_1((bool2bv((t1_483[64:63]) == (t2_484[64:63]))), (XOR_1((t1_483[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_483)), t2_484)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38a4:
RCX := RAX;

label_0x38a7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14508bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x38ac"} true;
call arbitrary_func();

label_0x38ac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x38b0:
t_489 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_489)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_489, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_489, 4bv32)), t_489)), 2bv32)), (XOR_32((RSHIFT_32(t_489, 4bv32)), t_489)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_489, 4bv32)), t_489)), 2bv32)), (XOR_32((RSHIFT_32(t_489, 4bv32)), t_489)))))[1:0]));
SF := t_489[32:31];
ZF := bool2bv(0bv32 == t_489);

label_0x38b5:
if (bv2bool(ZF)) {
  goto label_0x3995;
}

label_0x38bb:
t_493 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_493)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_493, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_493, 4bv32)), t_493)), 2bv32)), (XOR_32((RSHIFT_32(t_493, 4bv32)), t_493)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_493, 4bv32)), t_493)), 2bv32)), (XOR_32((RSHIFT_32(t_493, 4bv32)), t_493)))))[1:0]));
SF := t_493[32:31];
ZF := bool2bv(0bv32 == t_493);

label_0x38c0:
if (bv2bool(ZF)) {
  goto label_0x3995;
}

label_0x38c6:
t_497 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_497)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_497, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)), 2bv64)), (XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)), 2bv64)), (XOR_64((RSHIFT_64(t_497, 4bv64)), t_497)))))[1:0]));
SF := t_497[64:63];
ZF := bool2bv(0bv64 == t_497);

label_0x38cf:
if (bv2bool(ZF)) {
  goto label_0x3922;
}

label_0x38d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x38d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_183;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x38e4:
t_503 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_184;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))))[1:0]));
SF := t_503[64:63];
ZF := bool2bv(0bv64 == t_503);

label_0x38e7:
if (bv2bool(ZF)) {
  goto label_0x38ea;
}

label_0x38e9:
assume false;

label_0x38ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x38f2:
origDEST_507 := RAX;
origCOUNT_508 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), CF, LSHIFT_64(origDEST_507, (MINUS_64(64bv64, origCOUNT_508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_508 == 1bv64)), origDEST_507[64:63], unconstrained_185));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), AF, unconstrained_186);

label_0x38f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x38fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3901:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3909:
origDEST_513 := RCX;
origCOUNT_514 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), CF, LSHIFT_64(origDEST_513, (MINUS_64(64bv64, origCOUNT_514)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_514 == 1bv64)), origDEST_513[64:63], unconstrained_187));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), AF, unconstrained_188);

label_0x390d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_189;
SF := unconstrained_190;
AF := unconstrained_191;
PF := unconstrained_192;

label_0x3911:
if (bv2bool(CF)) {
  goto label_0x3914;
}

label_0x3913:
assume false;

label_0x3914:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x391c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x3920:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3922:
t_519 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_519)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_519, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_519, 4bv64)), t_519)), 2bv64)), (XOR_64((RSHIFT_64(t_519, 4bv64)), t_519)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_519, 4bv64)), t_519)), 2bv64)), (XOR_64((RSHIFT_64(t_519, 4bv64)), t_519)))))[1:0]));
SF := t_519[64:63];
ZF := bool2bv(0bv64 == t_519);

label_0x3928:
if (bv2bool(ZF)) {
  goto label_0x398e;
}

label_0x392a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x392f:
t1_523 := RAX;
t2_524 := 5096bv64;
RAX := PLUS_64(RAX, t2_524);
CF := bool2bv(LT_64(RAX, t1_523));
OF := AND_1((bool2bv((t1_523[64:63]) == (t2_524[64:63]))), (XOR_1((t1_523[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_523)), t2_524)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3935:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x393d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x3945:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_193;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x394b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3950:
t_531 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_194;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))))[1:0]));
SF := t_531[64:63];
ZF := bool2bv(0bv64 == t_531);

label_0x3953:
if (bv2bool(ZF)) {
  goto label_0x3956;
}

label_0x3955:
assume false;

label_0x3956:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x395e:
origDEST_535 := RAX;
origCOUNT_536 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), CF, LSHIFT_64(origDEST_535, (MINUS_64(64bv64, origCOUNT_536)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_536 == 1bv64)), origDEST_535[64:63], unconstrained_195));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), AF, unconstrained_196);

label_0x3962:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3969:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x396d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x3975:
origDEST_541 := RCX;
origCOUNT_542 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), CF, LSHIFT_64(origDEST_541, (MINUS_64(64bv64, origCOUNT_542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_542 == 1bv64)), origDEST_541[64:63], unconstrained_197));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), AF, unconstrained_198);

label_0x3979:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_199;
SF := unconstrained_200;
AF := unconstrained_201;
PF := unconstrained_202;

label_0x397d:
if (bv2bool(CF)) {
  goto label_0x3980;
}

label_0x397f:
assume false;

label_0x3980:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x3988:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x398c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x398e:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_203;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3990:
goto label_0x3c82;

label_0x3995:
t_547 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_547)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_547, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)), 2bv32)), (XOR_32((RSHIFT_32(t_547, 4bv32)), t_547)))))[1:0]));
SF := t_547[32:31];
ZF := bool2bv(0bv32 == t_547);

label_0x399a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3aaa;
}

label_0x39a0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x39a5:
RCX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x39a7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14764bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x39ac"} true;
call arbitrary_func();

label_0x39ac:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x39af:
t_551 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_204;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)), 2bv32)), (XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)), 2bv32)), (XOR_32((RSHIFT_32(t_551, 4bv32)), t_551)))))[1:0]));
SF := t_551[32:31];
ZF := bool2bv(0bv32 == t_551);

label_0x39b1:
if (bv2bool(ZF)) {
  goto label_0x3aaa;
}

label_0x39b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x39bc:
t_555 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), t_555)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_555, (LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)), 2bv32)), (XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)), 2bv32)), (XOR_32((RSHIFT_32(t_555, 4bv32)), t_555)))))[1:0]));
SF := t_555[32:31];
ZF := bool2bv(0bv32 == t_555);

label_0x39c3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3aaa;
}

label_0x39c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x39ce:
t_559 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), t_559)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_559, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_559, 4bv32)), t_559)), 2bv32)), (XOR_32((RSHIFT_32(t_559, 4bv32)), t_559)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_559, 4bv32)), t_559)), 2bv32)), (XOR_32((RSHIFT_32(t_559, 4bv32)), t_559)))))[1:0]));
SF := t_559[32:31];
ZF := bool2bv(0bv32 == t_559);

label_0x39d5:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x3aaa;
}

label_0x39db:
t_563 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_563)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_563, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)), 2bv64)), (XOR_64((RSHIFT_64(t_563, 4bv64)), t_563)))))[1:0]));
SF := t_563[64:63];
ZF := bool2bv(0bv64 == t_563);

label_0x39e4:
if (bv2bool(ZF)) {
  goto label_0x3a37;
}

label_0x39e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x39ee:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_205;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x39f4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x39f9:
t_569 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_206;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_569, 4bv64)), t_569)), 2bv64)), (XOR_64((RSHIFT_64(t_569, 4bv64)), t_569)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_569, 4bv64)), t_569)), 2bv64)), (XOR_64((RSHIFT_64(t_569, 4bv64)), t_569)))))[1:0]));
SF := t_569[64:63];
ZF := bool2bv(0bv64 == t_569);

label_0x39fc:
if (bv2bool(ZF)) {
  goto label_0x39ff;
}

label_0x39fe:
assume false;

label_0x39ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3a07:
origDEST_573 := RAX;
origCOUNT_574 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), CF, LSHIFT_64(origDEST_573, (MINUS_64(64bv64, origCOUNT_574)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_574 == 1bv64)), origDEST_573[64:63], unconstrained_207));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_574 == 0bv64)), AF, unconstrained_208);

label_0x3a0b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3a12:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3a16:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3a1e:
origDEST_579 := RCX;
origCOUNT_580 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), CF, LSHIFT_64(origDEST_579, (MINUS_64(64bv64, origCOUNT_580)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_580 == 1bv64)), origDEST_579[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_580 == 0bv64)), AF, unconstrained_210);

label_0x3a22:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_211;
SF := unconstrained_212;
AF := unconstrained_213;
PF := unconstrained_214;

label_0x3a26:
if (bv2bool(CF)) {
  goto label_0x3a29;
}

label_0x3a28:
assume false;

label_0x3a29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3a31:
mem := STORE_LE_32(mem, RAX, 4294967289bv32);

label_0x3a37:
t_585 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_585)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_585, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)), 2bv64)), (XOR_64((RSHIFT_64(t_585, 4bv64)), t_585)))))[1:0]));
SF := t_585[64:63];
ZF := bool2bv(0bv64 == t_585);

label_0x3a3d:
if (bv2bool(ZF)) {
  goto label_0x3aa3;
}

label_0x3a3f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3a44:
t1_589 := RAX;
t2_590 := 5096bv64;
RAX := PLUS_64(RAX, t2_590);
CF := bool2bv(LT_64(RAX, t1_589));
OF := AND_1((bool2bv((t1_589[64:63]) == (t2_590[64:63]))), (XOR_1((t1_589[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_589)), t2_590)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3a4a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x3a52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3a5a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_215;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3a60:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3a65:
t_597 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_216;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_597, 4bv64)), t_597)), 2bv64)), (XOR_64((RSHIFT_64(t_597, 4bv64)), t_597)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_597, 4bv64)), t_597)), 2bv64)), (XOR_64((RSHIFT_64(t_597, 4bv64)), t_597)))))[1:0]));
SF := t_597[64:63];
ZF := bool2bv(0bv64 == t_597);

label_0x3a68:
if (bv2bool(ZF)) {
  goto label_0x3a6b;
}

label_0x3a6a:
assume false;

label_0x3a6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3a73:
origDEST_601 := RAX;
origCOUNT_602 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), CF, LSHIFT_64(origDEST_601, (MINUS_64(64bv64, origCOUNT_602)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_602 == 1bv64)), origDEST_601[64:63], unconstrained_217));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_602 == 0bv64)), AF, unconstrained_218);

label_0x3a77:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3a7e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3a82:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3a8a:
origDEST_607 := RCX;
origCOUNT_608 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), CF, LSHIFT_64(origDEST_607, (MINUS_64(64bv64, origCOUNT_608)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_608 == 1bv64)), origDEST_607[64:63], unconstrained_219));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_608 == 0bv64)), AF, unconstrained_220);

label_0x3a8e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_221;
SF := unconstrained_222;
AF := unconstrained_223;
PF := unconstrained_224;

label_0x3a92:
if (bv2bool(CF)) {
  goto label_0x3a95;
}

label_0x3a94:
assume false;

label_0x3a95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3a9d:
mem := STORE_LE_32(mem, RAX, 4294967289bv32);

label_0x3aa3:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_225;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3aa5:
goto label_0x3c82;

label_0x3aaa:
t_613 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_613)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_613, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_613, 4bv32)), t_613)), 2bv32)), (XOR_32((RSHIFT_32(t_613, 4bv32)), t_613)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_613, 4bv32)), t_613)), 2bv32)), (XOR_32((RSHIFT_32(t_613, 4bv32)), t_613)))))[1:0]));
SF := t_613[32:31];
ZF := bool2bv(0bv32 == t_613);

label_0x3aaf:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3b98;
}

label_0x3ab5:
t_617 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_617)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_617, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)), 2bv64)), (XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)), 2bv64)), (XOR_64((RSHIFT_64(t_617, 4bv64)), t_617)))))[1:0]));
SF := t_617[64:63];
ZF := bool2bv(0bv64 == t_617);

label_0x3abe:
if (bv2bool(ZF)) {
  goto label_0x3b11;
}

label_0x3ac0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3ac8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_226;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3ace:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3ad3:
t_623 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_227;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_623, 4bv64)), t_623)), 2bv64)), (XOR_64((RSHIFT_64(t_623, 4bv64)), t_623)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_623, 4bv64)), t_623)), 2bv64)), (XOR_64((RSHIFT_64(t_623, 4bv64)), t_623)))))[1:0]));
SF := t_623[64:63];
ZF := bool2bv(0bv64 == t_623);

label_0x3ad6:
if (bv2bool(ZF)) {
  goto label_0x3ad9;
}

label_0x3ad8:
assume false;

label_0x3ad9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3ae1:
origDEST_627 := RAX;
origCOUNT_628 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), CF, LSHIFT_64(origDEST_627, (MINUS_64(64bv64, origCOUNT_628)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_628 == 1bv64)), origDEST_627[64:63], unconstrained_228));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_628 == 0bv64)), AF, unconstrained_229);

label_0x3ae5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3aec:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3af0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3af8:
origDEST_633 := RCX;
origCOUNT_634 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), CF, LSHIFT_64(origDEST_633, (MINUS_64(64bv64, origCOUNT_634)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_634 == 1bv64)), origDEST_633[64:63], unconstrained_230));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_634 == 0bv64)), AF, unconstrained_231);

label_0x3afc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_232;
SF := unconstrained_233;
AF := unconstrained_234;
PF := unconstrained_235;

label_0x3b00:
if (bv2bool(CF)) {
  goto label_0x3b03;
}

label_0x3b02:
assume false;

label_0x3b03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3b0b:
mem := STORE_LE_32(mem, RAX, 4bv32);

label_0x3b11:
t_639 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_639)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_639, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))))[1:0]));
SF := t_639[64:63];
ZF := bool2bv(0bv64 == t_639);

label_0x3b17:
if (bv2bool(ZF)) {
  goto label_0x3b7d;
}

label_0x3b19:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3b1e:
t1_643 := RAX;
t2_644 := 5096bv64;
RAX := PLUS_64(RAX, t2_644);
CF := bool2bv(LT_64(RAX, t1_643));
OF := AND_1((bool2bv((t1_643[64:63]) == (t2_644[64:63]))), (XOR_1((t1_643[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_643)), t2_644)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3b24:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x3b2c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x3b34:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_236;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3b3a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3b3f:
t_651 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_237;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_651, 4bv64)), t_651)), 2bv64)), (XOR_64((RSHIFT_64(t_651, 4bv64)), t_651)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_651, 4bv64)), t_651)), 2bv64)), (XOR_64((RSHIFT_64(t_651, 4bv64)), t_651)))))[1:0]));
SF := t_651[64:63];
ZF := bool2bv(0bv64 == t_651);

label_0x3b42:
if (bv2bool(ZF)) {
  goto label_0x3b45;
}

label_0x3b44:
assume false;

label_0x3b45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x3b4d:
origDEST_655 := RAX;
origCOUNT_656 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), CF, LSHIFT_64(origDEST_655, (MINUS_64(64bv64, origCOUNT_656)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_656 == 1bv64)), origDEST_655[64:63], unconstrained_238));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_656 == 0bv64)), AF, unconstrained_239);

label_0x3b51:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3b58:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3b5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x3b64:
origDEST_661 := RCX;
origCOUNT_662 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), CF, LSHIFT_64(origDEST_661, (MINUS_64(64bv64, origCOUNT_662)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_662 == 1bv64)), origDEST_661[64:63], unconstrained_240));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_662 == 0bv64)), AF, unconstrained_241);

label_0x3b68:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_242;
SF := unconstrained_243;
AF := unconstrained_244;
PF := unconstrained_245;

label_0x3b6c:
if (bv2bool(CF)) {
  goto label_0x3b6f;
}

label_0x3b6e:
assume false;

label_0x3b6f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x3b77:
mem := STORE_LE_32(mem, RAX, 4bv32);

label_0x3b7d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3b82:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64)));

label_0x3b88:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 232bv64)));

label_0x3b8f:
t_667 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_667, (RAX[32:0])));
OF := AND_32((XOR_32(t_667, (RAX[32:0]))), (XOR_32(t_667, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_667)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3b91:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3b93:
goto label_0x3c82;

label_0x3b98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3b9d:
t_671 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), t_671)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_671, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_671, 4bv32)), t_671)), 2bv32)), (XOR_32((RSHIFT_32(t_671, 4bv32)), t_671)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_671, 4bv32)), t_671)), 2bv32)), (XOR_32((RSHIFT_32(t_671, 4bv32)), t_671)))))[1:0]));
SF := t_671[32:31];
ZF := bool2bv(0bv32 == t_671);

label_0x3ba4:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3c7b;
}

label_0x3baa:
t_675 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))), t_675)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_675, (LOAD_LE_64(mem, PLUS_64(RSP, 208bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)), 2bv64)), (XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)), 2bv64)), (XOR_64((RSHIFT_64(t_675, 4bv64)), t_675)))))[1:0]));
SF := t_675[64:63];
ZF := bool2bv(0bv64 == t_675);

label_0x3bb3:
if (bv2bool(ZF)) {
  goto label_0x3c06;
}

label_0x3bb5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3bbd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_246;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3bc3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3bc8:
t_681 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_247;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)), 2bv64)), (XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)), 2bv64)), (XOR_64((RSHIFT_64(t_681, 4bv64)), t_681)))))[1:0]));
SF := t_681[64:63];
ZF := bool2bv(0bv64 == t_681);

label_0x3bcb:
if (bv2bool(ZF)) {
  goto label_0x3bce;
}

label_0x3bcd:
assume false;

label_0x3bce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3bd6:
origDEST_685 := RAX;
origCOUNT_686 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), CF, LSHIFT_64(origDEST_685, (MINUS_64(64bv64, origCOUNT_686)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_686 == 1bv64)), origDEST_685[64:63], unconstrained_248));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_686 == 0bv64)), AF, unconstrained_249);

label_0x3bda:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3be1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3be5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3bed:
origDEST_691 := RCX;
origCOUNT_692 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), CF, LSHIFT_64(origDEST_691, (MINUS_64(64bv64, origCOUNT_692)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_692 == 1bv64)), origDEST_691[64:63], unconstrained_250));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_692 == 0bv64)), AF, unconstrained_251);

label_0x3bf1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_252;
SF := unconstrained_253;
AF := unconstrained_254;
PF := unconstrained_255;

label_0x3bf5:
if (bv2bool(CF)) {
  goto label_0x3bf8;
}

label_0x3bf7:
assume false;

label_0x3bf8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x3c00:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3c06:
t_697 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_697)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_697, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_697, 4bv64)), t_697)), 2bv64)), (XOR_64((RSHIFT_64(t_697, 4bv64)), t_697)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_697, 4bv64)), t_697)), 2bv64)), (XOR_64((RSHIFT_64(t_697, 4bv64)), t_697)))))[1:0]));
SF := t_697[64:63];
ZF := bool2bv(0bv64 == t_697);

label_0x3c0c:
if (bv2bool(ZF)) {
  goto label_0x3c72;
}

label_0x3c0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3c13:
t1_701 := RAX;
t2_702 := 5096bv64;
RAX := PLUS_64(RAX, t2_702);
CF := bool2bv(LT_64(RAX, t1_701));
OF := AND_1((bool2bv((t1_701[64:63]) == (t2_702[64:63]))), (XOR_1((t1_701[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_701)), t2_702)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3c19:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x3c21:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3c29:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_256;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3c2f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3c34:
t_709 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_257;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)), 2bv64)), (XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)), 2bv64)), (XOR_64((RSHIFT_64(t_709, 4bv64)), t_709)))))[1:0]));
SF := t_709[64:63];
ZF := bool2bv(0bv64 == t_709);

label_0x3c37:
if (bv2bool(ZF)) {
  goto label_0x3c3a;
}

label_0x3c39:
assume false;

label_0x3c3a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3c42:
origDEST_713 := RAX;
origCOUNT_714 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), CF, LSHIFT_64(origDEST_713, (MINUS_64(64bv64, origCOUNT_714)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_714 == 1bv64)), origDEST_713[64:63], unconstrained_258));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_714 == 0bv64)), AF, unconstrained_259);

label_0x3c46:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3c4d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3c51:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3c59:
origDEST_719 := RCX;
origCOUNT_720 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), CF, LSHIFT_64(origDEST_719, (MINUS_64(64bv64, origCOUNT_720)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_720 == 1bv64)), origDEST_719[64:63], unconstrained_260));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_720 == 0bv64)), AF, unconstrained_261);

label_0x3c5d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_262;
SF := unconstrained_263;
AF := unconstrained_264;
PF := unconstrained_265;

label_0x3c61:
if (bv2bool(CF)) {
  goto label_0x3c64;
}

label_0x3c63:
assume false;

label_0x3c64:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3c6c:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3c72:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 232bv64)));

label_0x3c79:
goto label_0x3c82;

label_0x3c7b:
goto label_0x3566;

label_0x3c80:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_266;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3c82:
t1_725 := RSP;
t2_726 := 200bv64;
RSP := PLUS_64(RSP, t2_726);
CF := bool2bv(LT_64(RSP, t1_725));
OF := AND_1((bool2bv((t1_725[64:63]) == (t2_726[64:63]))), (XOR_1((t1_725[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_725)), t2_726)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3c89:

ra_731 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_132,origCOUNT_138,origCOUNT_16,origCOUNT_160,origCOUNT_166,origCOUNT_186,origCOUNT_192,origCOUNT_214,origCOUNT_22,origCOUNT_220,origCOUNT_238,origCOUNT_244,origCOUNT_262,origCOUNT_268,origCOUNT_292,origCOUNT_298,origCOUNT_320,origCOUNT_326,origCOUNT_360,origCOUNT_366,origCOUNT_388,origCOUNT_394,origCOUNT_412,origCOUNT_418,origCOUNT_44,origCOUNT_442,origCOUNT_448,origCOUNT_472,origCOUNT_478,origCOUNT_50,origCOUNT_508,origCOUNT_514,origCOUNT_536,origCOUNT_542,origCOUNT_574,origCOUNT_580,origCOUNT_602,origCOUNT_608,origCOUNT_628,origCOUNT_634,origCOUNT_656,origCOUNT_662,origCOUNT_686,origCOUNT_692,origCOUNT_714,origCOUNT_720,origCOUNT_78,origCOUNT_84,origDEST_105,origDEST_111,origDEST_131,origDEST_137,origDEST_15,origDEST_159,origDEST_165,origDEST_185,origDEST_191,origDEST_21,origDEST_213,origDEST_219,origDEST_237,origDEST_243,origDEST_261,origDEST_267,origDEST_291,origDEST_297,origDEST_319,origDEST_325,origDEST_359,origDEST_365,origDEST_387,origDEST_393,origDEST_411,origDEST_417,origDEST_43,origDEST_441,origDEST_447,origDEST_471,origDEST_477,origDEST_49,origDEST_507,origDEST_513,origDEST_535,origDEST_541,origDEST_573,origDEST_579,origDEST_601,origDEST_607,origDEST_627,origDEST_633,origDEST_655,origDEST_661,origDEST_685,origDEST_691,origDEST_713,origDEST_719,origDEST_77,origDEST_83,ra_731,t1_147,t1_201,t1_225,t1_249,t1_307,t1_31,t1_339,t1_375,t1_399,t1_423,t1_429,t1_453,t1_459,t1_483,t1_523,t1_589,t1_643,t1_701,t1_725,t1_93,t2_148,t2_202,t2_226,t2_250,t2_308,t2_32,t2_340,t2_376,t2_400,t2_424,t2_430,t2_454,t2_460,t2_484,t2_524,t2_590,t2_644,t2_702,t2_726,t2_94,t_1,t_101,t_11,t_117,t_121,t_127,t_143,t_155,t_171,t_175,t_181,t_197,t_209,t_233,t_257,t_27,t_273,t_277,t_281,t_287,t_303,t_315,t_331,t_335,t_345,t_349,t_355,t_371,t_383,t_39,t_407,t_437,t_467,t_489,t_493,t_497,t_5,t_503,t_519,t_531,t_547,t_55,t_551,t_555,t_559,t_563,t_569,t_585,t_59,t_597,t_613,t_617,t_623,t_63,t_639,t_651,t_667,t_67,t_671,t_675,t_681,t_697,t_709,t_73,t_89;

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
var origCOUNT_106: bv64;
var origCOUNT_112: bv64;
var origCOUNT_132: bv64;
var origCOUNT_138: bv64;
var origCOUNT_16: bv64;
var origCOUNT_160: bv64;
var origCOUNT_166: bv64;
var origCOUNT_186: bv64;
var origCOUNT_192: bv64;
var origCOUNT_214: bv64;
var origCOUNT_22: bv64;
var origCOUNT_220: bv64;
var origCOUNT_238: bv64;
var origCOUNT_244: bv64;
var origCOUNT_262: bv64;
var origCOUNT_268: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_320: bv64;
var origCOUNT_326: bv64;
var origCOUNT_360: bv64;
var origCOUNT_366: bv64;
var origCOUNT_388: bv64;
var origCOUNT_394: bv64;
var origCOUNT_412: bv64;
var origCOUNT_418: bv64;
var origCOUNT_44: bv64;
var origCOUNT_442: bv64;
var origCOUNT_448: bv64;
var origCOUNT_472: bv64;
var origCOUNT_478: bv64;
var origCOUNT_50: bv64;
var origCOUNT_508: bv64;
var origCOUNT_514: bv64;
var origCOUNT_536: bv64;
var origCOUNT_542: bv64;
var origCOUNT_574: bv64;
var origCOUNT_580: bv64;
var origCOUNT_602: bv64;
var origCOUNT_608: bv64;
var origCOUNT_628: bv64;
var origCOUNT_634: bv64;
var origCOUNT_656: bv64;
var origCOUNT_662: bv64;
var origCOUNT_686: bv64;
var origCOUNT_692: bv64;
var origCOUNT_714: bv64;
var origCOUNT_720: bv64;
var origCOUNT_78: bv64;
var origCOUNT_84: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_131: bv64;
var origDEST_137: bv64;
var origDEST_15: bv64;
var origDEST_159: bv64;
var origDEST_165: bv64;
var origDEST_185: bv64;
var origDEST_191: bv64;
var origDEST_21: bv64;
var origDEST_213: bv64;
var origDEST_219: bv64;
var origDEST_237: bv64;
var origDEST_243: bv64;
var origDEST_261: bv64;
var origDEST_267: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_319: bv64;
var origDEST_325: bv64;
var origDEST_359: bv64;
var origDEST_365: bv64;
var origDEST_387: bv64;
var origDEST_393: bv64;
var origDEST_411: bv64;
var origDEST_417: bv64;
var origDEST_43: bv64;
var origDEST_441: bv64;
var origDEST_447: bv64;
var origDEST_471: bv64;
var origDEST_477: bv64;
var origDEST_49: bv64;
var origDEST_507: bv64;
var origDEST_513: bv64;
var origDEST_535: bv64;
var origDEST_541: bv64;
var origDEST_573: bv64;
var origDEST_579: bv64;
var origDEST_601: bv64;
var origDEST_607: bv64;
var origDEST_627: bv64;
var origDEST_633: bv64;
var origDEST_655: bv64;
var origDEST_661: bv64;
var origDEST_685: bv64;
var origDEST_691: bv64;
var origDEST_713: bv64;
var origDEST_719: bv64;
var origDEST_77: bv64;
var origDEST_83: bv64;
var ra_731: bv64;
var t1_147: bv64;
var t1_201: bv64;
var t1_225: bv64;
var t1_249: bv64;
var t1_307: bv64;
var t1_31: bv64;
var t1_339: bv64;
var t1_375: bv64;
var t1_399: bv64;
var t1_423: bv64;
var t1_429: bv64;
var t1_453: bv64;
var t1_459: bv64;
var t1_483: bv64;
var t1_523: bv64;
var t1_589: bv64;
var t1_643: bv64;
var t1_701: bv64;
var t1_725: bv64;
var t1_93: bv64;
var t2_148: bv64;
var t2_202: bv64;
var t2_226: bv64;
var t2_250: bv64;
var t2_308: bv64;
var t2_32: bv64;
var t2_340: bv64;
var t2_376: bv64;
var t2_400: bv64;
var t2_424: bv64;
var t2_430: bv64;
var t2_454: bv64;
var t2_460: bv64;
var t2_484: bv64;
var t2_524: bv64;
var t2_590: bv64;
var t2_644: bv64;
var t2_702: bv64;
var t2_726: bv64;
var t2_94: bv64;
var t_1: bv64;
var t_101: bv64;
var t_11: bv64;
var t_117: bv32;
var t_121: bv64;
var t_127: bv64;
var t_143: bv64;
var t_155: bv64;
var t_171: bv32;
var t_175: bv64;
var t_181: bv64;
var t_197: bv64;
var t_209: bv64;
var t_233: bv64;
var t_257: bv64;
var t_27: bv64;
var t_273: bv32;
var t_277: bv32;
var t_281: bv64;
var t_287: bv64;
var t_303: bv64;
var t_315: bv64;
var t_331: bv32;
var t_335: bv32;
var t_345: bv32;
var t_349: bv64;
var t_355: bv64;
var t_371: bv64;
var t_383: bv64;
var t_39: bv64;
var t_407: bv64;
var t_437: bv64;
var t_467: bv64;
var t_489: bv32;
var t_493: bv32;
var t_497: bv64;
var t_5: bv64;
var t_503: bv64;
var t_519: bv64;
var t_531: bv64;
var t_547: bv32;
var t_55: bv64;
var t_551: bv32;
var t_555: bv32;
var t_559: bv32;
var t_563: bv64;
var t_569: bv64;
var t_585: bv64;
var t_59: bv64;
var t_597: bv64;
var t_613: bv32;
var t_617: bv64;
var t_623: bv64;
var t_63: bv32;
var t_639: bv64;
var t_651: bv64;
var t_667: bv32;
var t_67: bv64;
var t_671: bv32;
var t_675: bv64;
var t_681: bv64;
var t_697: bv64;
var t_709: bv64;
var t_73: bv64;
var t_89: bv64;


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
