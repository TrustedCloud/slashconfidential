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
axiom _function_addr_low == 12272bv64;
axiom _function_addr_high == 13488bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2ff0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x2ff5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x2ff9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x2ffe:
t_1 := RSP;
RSP := MINUS_64(RSP, 168bv64);
CF := bool2bv(LT_64(t_1, 168bv64));
OF := AND_64((XOR_64(t_1, 168bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 168bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3005:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x300d:
t1_5 := RAX;
t2_6 := 332bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3013:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x3018:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x301d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3023:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3028:
t_13 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x302b:
if (bv2bool(ZF)) {
  goto label_0x302e;
}

label_0x302d:
assume false;

label_0x302e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x3033:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x3037:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x303e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3042:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x3047:
origDEST_23 := RCX;
origCOUNT_24 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x304b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x304f:
if (bv2bool(CF)) {
  goto label_0x3052;
}

label_0x3051:
assume false;

label_0x3052:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x3057:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x305e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3060:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3068:
t1_29 := RAX;
t2_30 := 336bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x306e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x3073:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3078:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x307e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3083:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x3086:
if (bv2bool(ZF)) {
  goto label_0x3089;
}

label_0x3088:
assume false;

label_0x3089:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x308e:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_14);

label_0x3092:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3099:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x309d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x30a2:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_16);

label_0x30a6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x30aa:
if (bv2bool(CF)) {
  goto label_0x30ad;
}

label_0x30ac:
assume false;

label_0x30ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x30b2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x30b9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x30bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x30c3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x30c9:
t_53 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_53, 1bv32)), (XOR_32(t_53, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_53)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x30cb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), RAX[32:0]);

label_0x30cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x30d7:
t1_57 := RAX;
t2_58 := 316bv64;
RAX := PLUS_64(RAX, t2_58);
CF := bool2bv(LT_64(RAX, t1_57));
OF := AND_1((bool2bv((t1_57[64:63]) == (t2_58[64:63]))), (XOR_1((t1_57[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_57)), t2_58)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30dd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x30e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x30e7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30ed:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x30f2:
t_65 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)), 2bv64)), (XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)), 2bv64)), (XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)))))[1:0]));
SF := t_65[64:63];
ZF := bool2bv(0bv64 == t_65);

label_0x30f5:
if (bv2bool(ZF)) {
  goto label_0x30f8;
}

label_0x30f7:
assume false;

label_0x30f8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x30fd:
origDEST_69 := RAX;
origCOUNT_70 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), CF, LSHIFT_64(origDEST_69, (MINUS_64(64bv64, origCOUNT_70)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_70 == 1bv64)), origDEST_69[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_70 == 0bv64)), AF, unconstrained_24);

label_0x3101:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3108:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x310c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3111:
origDEST_75 := RCX;
origCOUNT_76 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_26);

label_0x3115:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x3119:
if (bv2bool(CF)) {
  goto label_0x311c;
}

label_0x311b:
assume false;

label_0x311c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3121:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x3125:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3127:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x312f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 336bv64)));

label_0x3135:
t_81 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_81, 1bv32)), (XOR_32(t_81, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_81)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3137:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), RAX[32:0]);

label_0x313b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3143:
t1_85 := RAX;
t2_86 := 320bv64;
RAX := PLUS_64(RAX, t2_86);
CF := bool2bv(LT_64(RAX, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3149:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x314e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3153:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3159:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x315e:
t_93 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x3161:
if (bv2bool(ZF)) {
  goto label_0x3164;
}

label_0x3163:
assume false;

label_0x3164:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3169:
origDEST_97 := RAX;
origCOUNT_98 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_34);

label_0x316d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3174:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3178:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x317d:
origDEST_103 := RCX;
origCOUNT_104 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), CF, LSHIFT_64(origDEST_103, (MINUS_64(64bv64, origCOUNT_104)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_104 == 1bv64)), origDEST_103[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_104 == 0bv64)), AF, unconstrained_36);

label_0x3181:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x3185:
if (bv2bool(CF)) {
  goto label_0x3188;
}

label_0x3187:
assume false;

label_0x3188:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x318d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 124bv64)));

label_0x3191:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3193:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x319b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x31a3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x31a9:
t_109 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_109[32:0]);
OF := bool2bv(t_109 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_109 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_41;
SF := unconstrained_42;
ZF := unconstrained_43;
AF := unconstrained_44;

label_0x31b0:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x31b2:
origDEST_111 := RAX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, RSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_46);

label_0x31b6:
RCX := RAX;

label_0x31b9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12734bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x31be"} true;
call arbitrary_func();

label_0x31be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x31c6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x31ce:
t1_117 := RAX;
t2_118 := 32bv64;
RAX := PLUS_64(RAX, t2_118);
CF := bool2bv(LT_64(RAX, t1_117));
OF := AND_1((bool2bv((t1_117[64:63]) == (t2_118[64:63]))), (XOR_1((t1_117[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_117)), t2_118)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31d2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x31d7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x31dc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31e2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x31e7:
t_125 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))))[1:0]));
SF := t_125[64:63];
ZF := bool2bv(0bv64 == t_125);

label_0x31ea:
if (bv2bool(ZF)) {
  goto label_0x31ed;
}

label_0x31ec:
assume false;

label_0x31ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x31f2:
origDEST_129 := RAX;
origCOUNT_130 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), CF, LSHIFT_64(origDEST_129, (MINUS_64(64bv64, origCOUNT_130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_130 == 1bv64)), origDEST_129[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), AF, unconstrained_50);

label_0x31f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x31fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3201:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3206:
origDEST_135 := RCX;
origCOUNT_136 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_52);

label_0x320a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x320e:
if (bv2bool(CF)) {
  goto label_0x3211;
}

label_0x3210:
assume false;

label_0x3211:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3216:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x321e:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3221:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3229:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3231:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x3237:
t_141 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_141[32:0]);
OF := bool2bv(t_141 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_141 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_57;
SF := unconstrained_58;
ZF := unconstrained_59;
AF := unconstrained_60;

label_0x323e:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3240:
RCX := RAX;

label_0x3243:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 12872bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3248"} true;
call arbitrary_func();

label_0x3248:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x3250:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3258:
t1_143 := RAX;
t2_144 := 40bv64;
RAX := PLUS_64(RAX, t2_144);
CF := bool2bv(LT_64(RAX, t1_143));
OF := AND_1((bool2bv((t1_143[64:63]) == (t2_144[64:63]))), (XOR_1((t1_143[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_143)), t2_144)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x325c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x3261:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3266:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x326c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3271:
t_151 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))))[1:0]));
SF := t_151[64:63];
ZF := bool2bv(0bv64 == t_151);

label_0x3274:
if (bv2bool(ZF)) {
  goto label_0x3277;
}

label_0x3276:
assume false;

label_0x3277:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x327c:
origDEST_155 := RAX;
origCOUNT_156 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_64);

label_0x3280:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3287:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x328b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3290:
origDEST_161 := RCX;
origCOUNT_162 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_66);

label_0x3294:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x3298:
if (bv2bool(CF)) {
  goto label_0x329b;
}

label_0x329a:
assume false;

label_0x329b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x32a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x32a8:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x32ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x32b3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x32bb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x32c1:
t_167 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_167[32:0]);
OF := bool2bv(t_167 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_167 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_71;
SF := unconstrained_72;
ZF := unconstrained_73;
AF := unconstrained_74;

label_0x32c8:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x32ca:
origDEST_169 := RAX;
origCOUNT_170 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), CF, RSHIFT_64(origDEST_169, (MINUS_64(64bv64, origCOUNT_170)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), AF, unconstrained_76);

label_0x32cd:
RCX := RAX;

label_0x32d0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13013bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x32d5"} true;
call arbitrary_func();

label_0x32d5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x32dd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x32e5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x32ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x32ef:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_77;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x32f5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x32fa:
t_177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))))[1:0]));
SF := t_177[64:63];
ZF := bool2bv(0bv64 == t_177);

label_0x32fd:
if (bv2bool(ZF)) {
  goto label_0x3300;
}

label_0x32ff:
assume false;

label_0x3300:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3305:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_80);

label_0x3309:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3310:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3314:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3319:
origDEST_187 := RCX;
origCOUNT_188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_81));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_82);

label_0x331d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_83;
SF := unconstrained_84;
AF := unconstrained_85;
PF := unconstrained_86;

label_0x3321:
if (bv2bool(CF)) {
  goto label_0x3324;
}

label_0x3323:
assume false;

label_0x3324:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3329:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3331:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x3334:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x333c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3344:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 332bv64)));

label_0x334a:
t_193 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 336bv64)))))));
RAX := (0bv32 ++ t_193[32:0]);
OF := bool2bv(t_193 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_193 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_87;
SF := unconstrained_88;
ZF := unconstrained_89;
AF := unconstrained_90;

label_0x3351:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3353:
origDEST_195 := RAX;
origCOUNT_196 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), CF, RSHIFT_64(origDEST_195, (MINUS_64(64bv64, origCOUNT_196)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_196 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), AF, unconstrained_92);

label_0x3356:
R8 := RAX;

label_0x3359:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_93;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x335b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3363:
RCX := LOAD_LE_64(mem, RAX);

label_0x3366:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 13163bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x336b"} true;
call arbitrary_func();

label_0x336b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3373:
t1_201 := RAX;
t2_202 := 8bv64;
RAX := PLUS_64(RAX, t2_202);
CF := bool2bv(LT_64(RAX, t1_201));
OF := AND_1((bool2bv((t1_201[64:63]) == (t2_202[64:63]))), (XOR_1((t1_201[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_201)), t2_202)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3377:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x337c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3381:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3387:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x338c:
t_209 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))))[1:0]));
SF := t_209[64:63];
ZF := bool2bv(0bv64 == t_209);

label_0x338f:
if (bv2bool(ZF)) {
  goto label_0x3392;
}

label_0x3391:
assume false;

label_0x3392:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3397:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_97);

label_0x339b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x33a2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x33a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x33ab:
origDEST_219 := RCX;
origCOUNT_220 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), CF, LSHIFT_64(origDEST_219, (MINUS_64(64bv64, origCOUNT_220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv64)), origDEST_219[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), AF, unconstrained_99);

label_0x33af:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_100;
SF := unconstrained_101;
AF := unconstrained_102;
PF := unconstrained_103;

label_0x33b3:
if (bv2bool(CF)) {
  goto label_0x33b6;
}

label_0x33b5:
assume false;

label_0x33b6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_104;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x33b8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x33bd:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x33c0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x33c8:
goto label_0x33d4;

label_0x33ca:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x33ce:
t_225 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_225[32:31]) == (1bv32[32:31]))), (XOR_1((t_225[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_225)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x33d0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x33d4:
t_229 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_229)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_229, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)), 2bv32)), (XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)), 2bv32)), (XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)))))[1:0]));
SF := t_229[32:31];
ZF := bool2bv(0bv32 == t_229);

label_0x33dc:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x343b;
}

label_0x33de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x33e6:
t1_233 := RAX;
t2_234 := 48bv64;
RAX := PLUS_64(RAX, t2_234);
CF := bool2bv(LT_64(RAX, t1_233));
OF := AND_1((bool2bv((t1_233[64:63]) == (t2_234[64:63]))), (XOR_1((t1_233[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_233)), t2_234)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33ea:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x33ef:
t1_239 := RAX;
t2_240 := RCX;
RAX := PLUS_64(RAX, t2_240);
CF := bool2bv(LT_64(RAX, t1_239));
OF := AND_1((bool2bv((t1_239[64:63]) == (t2_240[64:63]))), (XOR_1((t1_239[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_239)), t2_240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x33f2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x33f7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x33fc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3402:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3407:
t_247 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))))[1:0]));
SF := t_247[64:63];
ZF := bool2bv(0bv64 == t_247);

label_0x340a:
if (bv2bool(ZF)) {
  goto label_0x340d;
}

label_0x340c:
assume false;

label_0x340d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3412:
origDEST_251 := RAX;
origCOUNT_252 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), CF, LSHIFT_64(origDEST_251, (MINUS_64(64bv64, origCOUNT_252)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv64)), origDEST_251[64:63], unconstrained_107));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), AF, unconstrained_108);

label_0x3416:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x341d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3421:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3426:
origDEST_257 := RCX;
origCOUNT_258 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_109));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_110);

label_0x342a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_111;
SF := unconstrained_112;
AF := unconstrained_113;
PF := unconstrained_114;

label_0x342e:
if (bv2bool(CF)) {
  goto label_0x3431;
}

label_0x3430:
assume false;

label_0x3431:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3436:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x3439:
goto label_0x33ca;

label_0x343b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3443:
t1_263 := RAX;
t2_264 := 48bv64;
RAX := PLUS_64(RAX, t2_264);
CF := bool2bv(LT_64(RAX, t1_263));
OF := AND_1((bool2bv((t1_263[64:63]) == (t2_264[64:63]))), (XOR_1((t1_263[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_263)), t2_264)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3447:
RCX := (0bv32 ++ 1bv32);

label_0x344c:
t_269 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RCX := t_269[64:0];
OF := bool2bv(t_269 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_269 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_115;
SF := unconstrained_116;
ZF := unconstrained_117;
AF := unconstrained_118;

label_0x3450:
t1_271 := RAX;
t2_272 := RCX;
RAX := PLUS_64(RAX, t2_272);
CF := bool2bv(LT_64(RAX, t1_271));
OF := AND_1((bool2bv((t1_271[64:63]) == (t2_272[64:63]))), (XOR_1((t1_271[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_271)), t2_272)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3453:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x3458:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x345d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_119;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3463:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3468:
t_279 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_120;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_279, 4bv64)), t_279)), 2bv64)), (XOR_64((RSHIFT_64(t_279, 4bv64)), t_279)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_279, 4bv64)), t_279)), 2bv64)), (XOR_64((RSHIFT_64(t_279, 4bv64)), t_279)))))[1:0]));
SF := t_279[64:63];
ZF := bool2bv(0bv64 == t_279);

label_0x346b:
if (bv2bool(ZF)) {
  goto label_0x346e;
}

label_0x346d:
assume false;

label_0x346e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3473:
origDEST_283 := RAX;
origCOUNT_284 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), CF, LSHIFT_64(origDEST_283, (MINUS_64(64bv64, origCOUNT_284)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_284 == 1bv64)), origDEST_283[64:63], unconstrained_121));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_284 == 0bv64)), AF, unconstrained_122);

label_0x3477:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x347e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3482:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3487:
origDEST_289 := RCX;
origCOUNT_290 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), CF, LSHIFT_64(origDEST_289, (MINUS_64(64bv64, origCOUNT_290)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_290 == 1bv64)), origDEST_289[64:63], unconstrained_123));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_290 == 0bv64)), AF, unconstrained_124);

label_0x348b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_125;
SF := unconstrained_126;
AF := unconstrained_127;
PF := unconstrained_128;

label_0x348f:
if (bv2bool(CF)) {
  goto label_0x3492;
}

label_0x3491:
assume false;

label_0x3492:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3497:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x349a:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x349c:
t1_295 := RSP;
t2_296 := 168bv64;
RSP := PLUS_64(RSP, t2_296);
CF := bool2bv(LT_64(RSP, t1_295));
OF := AND_1((bool2bv((t1_295[64:63]) == (t2_296[64:63]))), (XOR_1((t1_295[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_295)), t2_296)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x34a3:

ra_301 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_104,origCOUNT_112,origCOUNT_130,origCOUNT_136,origCOUNT_156,origCOUNT_162,origCOUNT_170,origCOUNT_18,origCOUNT_182,origCOUNT_188,origCOUNT_196,origCOUNT_214,origCOUNT_220,origCOUNT_24,origCOUNT_252,origCOUNT_258,origCOUNT_284,origCOUNT_290,origCOUNT_42,origCOUNT_48,origCOUNT_70,origCOUNT_76,origCOUNT_98,origDEST_103,origDEST_111,origDEST_129,origDEST_135,origDEST_155,origDEST_161,origDEST_169,origDEST_17,origDEST_181,origDEST_187,origDEST_195,origDEST_213,origDEST_219,origDEST_23,origDEST_251,origDEST_257,origDEST_283,origDEST_289,origDEST_41,origDEST_47,origDEST_69,origDEST_75,origDEST_97,ra_301,t1_117,t1_143,t1_201,t1_233,t1_239,t1_263,t1_271,t1_29,t1_295,t1_5,t1_57,t1_85,t2_118,t2_144,t2_202,t2_234,t2_240,t2_264,t2_272,t2_296,t2_30,t2_58,t2_6,t2_86,t_1,t_109,t_125,t_13,t_141,t_151,t_167,t_177,t_193,t_209,t_225,t_229,t_247,t_269,t_279,t_37,t_53,t_65,t_81,t_93;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_104: bv64;
var origCOUNT_112: bv64;
var origCOUNT_130: bv64;
var origCOUNT_136: bv64;
var origCOUNT_156: bv64;
var origCOUNT_162: bv64;
var origCOUNT_170: bv64;
var origCOUNT_18: bv64;
var origCOUNT_182: bv64;
var origCOUNT_188: bv64;
var origCOUNT_196: bv64;
var origCOUNT_214: bv64;
var origCOUNT_220: bv64;
var origCOUNT_24: bv64;
var origCOUNT_252: bv64;
var origCOUNT_258: bv64;
var origCOUNT_284: bv64;
var origCOUNT_290: bv64;
var origCOUNT_42: bv64;
var origCOUNT_48: bv64;
var origCOUNT_70: bv64;
var origCOUNT_76: bv64;
var origCOUNT_98: bv64;
var origDEST_103: bv64;
var origDEST_111: bv64;
var origDEST_129: bv64;
var origDEST_135: bv64;
var origDEST_155: bv64;
var origDEST_161: bv64;
var origDEST_169: bv64;
var origDEST_17: bv64;
var origDEST_181: bv64;
var origDEST_187: bv64;
var origDEST_195: bv64;
var origDEST_213: bv64;
var origDEST_219: bv64;
var origDEST_23: bv64;
var origDEST_251: bv64;
var origDEST_257: bv64;
var origDEST_283: bv64;
var origDEST_289: bv64;
var origDEST_41: bv64;
var origDEST_47: bv64;
var origDEST_69: bv64;
var origDEST_75: bv64;
var origDEST_97: bv64;
var ra_301: bv64;
var t1_117: bv64;
var t1_143: bv64;
var t1_201: bv64;
var t1_233: bv64;
var t1_239: bv64;
var t1_263: bv64;
var t1_271: bv64;
var t1_29: bv64;
var t1_295: bv64;
var t1_5: bv64;
var t1_57: bv64;
var t1_85: bv64;
var t2_118: bv64;
var t2_144: bv64;
var t2_202: bv64;
var t2_234: bv64;
var t2_240: bv64;
var t2_264: bv64;
var t2_272: bv64;
var t2_296: bv64;
var t2_30: bv64;
var t2_58: bv64;
var t2_6: bv64;
var t2_86: bv64;
var t_1: bv64;
var t_109: bv64;
var t_125: bv64;
var t_13: bv64;
var t_141: bv64;
var t_151: bv64;
var t_167: bv64;
var t_177: bv64;
var t_193: bv64;
var t_209: bv64;
var t_225: bv32;
var t_229: bv32;
var t_247: bv64;
var t_269: bv128;
var t_279: bv64;
var t_37: bv64;
var t_53: bv32;
var t_65: bv64;
var t_81: bv32;
var t_93: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(208bv64);
axiom policy(688bv64);
axiom policy(1184bv64);
axiom policy(3040bv64);
axiom policy(3232bv64);
axiom policy(3488bv64);
axiom policy(4240bv64);
axiom policy(4816bv64);
axiom policy(5840bv64);
axiom policy(6768bv64);
axiom policy(7760bv64);
axiom policy(8352bv64);
axiom policy(8720bv64);
axiom policy(10656bv64);
axiom policy(12272bv64);
axiom policy(13488bv64);
axiom policy(13872bv64);
