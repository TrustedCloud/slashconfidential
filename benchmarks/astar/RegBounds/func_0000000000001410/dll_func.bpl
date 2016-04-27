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
axiom _function_addr_low == 5136bv64;
axiom _function_addr_high == 7296bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1410:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x1415:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x141a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x141e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1423:
t_1 := RSP;
RSP := MINUS_64(RSP, 264bv64);
CF := bool2bv(LT_64(t_1, 264bv64));
OF := AND_64((XOR_64(t_1, 264bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 264bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x142a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1432:
t1_5 := RAX;
t2_6 := 48bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1436:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x143b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1440:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1446:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x144b:
t_13 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x144e:
if (bv2bool(ZF)) {
  goto label_0x1451;
}

label_0x1450:
assume false;

label_0x1451:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1456:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x145a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1461:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1465:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x146a:
origDEST_23 := RCX;
origCOUNT_24 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x146e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x1472:
if (bv2bool(CF)) {
  goto label_0x1475;
}

label_0x1474:
assume false;

label_0x1475:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x147a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x1481:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1483:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x148b:
t1_29 := RAX;
t2_30 := 52bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x148f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1494:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1499:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x149f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x14a4:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x14a7:
if (bv2bool(ZF)) {
  goto label_0x14aa;
}

label_0x14a9:
assume false;

label_0x14aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14af:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_14);

label_0x14b3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x14ba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x14be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14c3:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_16);

label_0x14c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x14cb:
if (bv2bool(CF)) {
  goto label_0x14ce;
}

label_0x14cd:
assume false;

label_0x14ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14d3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x14da:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x14dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x14e4:
t1_53 := RAX;
t2_54 := 40bv64;
RAX := PLUS_64(RAX, t2_54);
CF := bool2bv(LT_64(RAX, t1_53));
OF := AND_1((bool2bv((t1_53[64:63]) == (t2_54[64:63]))), (XOR_1((t1_53[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_53)), t2_54)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14e8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x14ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x14f2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14f8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x14fd:
t_61 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))))[1:0]));
SF := t_61[64:63];
ZF := bool2bv(0bv64 == t_61);

label_0x1500:
if (bv2bool(ZF)) {
  goto label_0x1503;
}

label_0x1502:
assume false;

label_0x1503:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1508:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_24);

label_0x150c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1513:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1517:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x151c:
origDEST_71 := RCX;
origCOUNT_72 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_26);

label_0x1520:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x1524:
if (bv2bool(CF)) {
  goto label_0x1527;
}

label_0x1526:
assume false;

label_0x1527:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x152c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x1534:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1537:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x153f:
t1_77 := RAX;
t2_78 := 96bv64;
RAX := PLUS_64(RAX, t2_78);
CF := bool2bv(LT_64(RAX, t1_77));
OF := AND_1((bool2bv((t1_77[64:63]) == (t2_78[64:63]))), (XOR_1((t1_77[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_77)), t2_78)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1543:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x1548:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x154d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1553:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1558:
t_85 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))))[1:0]));
SF := t_85[64:63];
ZF := bool2bv(0bv64 == t_85);

label_0x155b:
if (bv2bool(ZF)) {
  goto label_0x155e;
}

label_0x155d:
assume false;

label_0x155e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1563:
origDEST_89 := RAX;
origCOUNT_90 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, LSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), origDEST_89[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_34);

label_0x1567:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x156e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1572:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1577:
origDEST_95 := RCX;
origCOUNT_96 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), CF, LSHIFT_64(origDEST_95, (MINUS_64(64bv64, origCOUNT_96)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_96 == 1bv64)), origDEST_95[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), AF, unconstrained_36);

label_0x157b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x157f:
if (bv2bool(CF)) {
  goto label_0x1582;
}

label_0x1581:
assume false;

label_0x1582:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1587:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x158f:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1592:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x159a:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x159e:
t1_101 := RAX;
t2_102 := 32bv64;
RAX := PLUS_64(RAX, t2_102);
CF := bool2bv(LT_64(RAX, t1_101));
OF := AND_1((bool2bv((t1_101[64:63]) == (t2_102[64:63]))), (XOR_1((t1_101[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_101)), t2_102)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x15aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x15b2:
t1_107 := RAX;
t2_108 := 64bv64;
RAX := PLUS_64(RAX, t2_108);
CF := bool2bv(LT_64(RAX, t1_107));
OF := AND_1((bool2bv((t1_107[64:63]) == (t2_108[64:63]))), (XOR_1((t1_107[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_107)), t2_108)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15b6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x15bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x15c0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15c6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x15cb:
t_115 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))))[1:0]));
SF := t_115[64:63];
ZF := bool2bv(0bv64 == t_115);

label_0x15ce:
if (bv2bool(ZF)) {
  goto label_0x15d1;
}

label_0x15d0:
assume false;

label_0x15d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x15d6:
origDEST_119 := RAX;
origCOUNT_120 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), CF, LSHIFT_64(origDEST_119, (MINUS_64(64bv64, origCOUNT_120)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_120 == 1bv64)), origDEST_119[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), AF, unconstrained_44);

label_0x15da:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x15e1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x15e5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x15ea:
origDEST_125 := RCX;
origCOUNT_126 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, LSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), origDEST_125[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_46);

label_0x15ee:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x15f2:
if (bv2bool(CF)) {
  goto label_0x15f5;
}

label_0x15f4:
assume false;

label_0x15f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x15fa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x1602:
RCX := LOAD_LE_64(mem, RCX);

label_0x1605:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1608:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1610:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x1614:
t1_131 := RAX;
t2_132 := 40bv64;
RAX := PLUS_64(RAX, t2_132);
CF := bool2bv(LT_64(RAX, t1_131));
OF := AND_1((bool2bv((t1_131[64:63]) == (t2_132[64:63]))), (XOR_1((t1_131[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_131)), t2_132)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1618:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x1620:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1628:
t1_137 := RAX;
t2_138 := 72bv64;
RAX := PLUS_64(RAX, t2_138);
CF := bool2bv(LT_64(RAX, t1_137));
OF := AND_1((bool2bv((t1_137[64:63]) == (t2_138[64:63]))), (XOR_1((t1_137[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_137)), t2_138)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x162c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x1631:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1636:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x163c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1641:
t_145 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)), 2bv64)), (XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)), 2bv64)), (XOR_64((RSHIFT_64(t_145, 4bv64)), t_145)))))[1:0]));
SF := t_145[64:63];
ZF := bool2bv(0bv64 == t_145);

label_0x1644:
if (bv2bool(ZF)) {
  goto label_0x1647;
}

label_0x1646:
assume false;

label_0x1647:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x164c:
origDEST_149 := RAX;
origCOUNT_150 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_54);

label_0x1650:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1657:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x165b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1660:
origDEST_155 := RCX;
origCOUNT_156 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_56);

label_0x1664:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x1668:
if (bv2bool(CF)) {
  goto label_0x166b;
}

label_0x166a:
assume false;

label_0x166b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1670:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x1678:
RCX := LOAD_LE_64(mem, RCX);

label_0x167b:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x167e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1686:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x168a:
t1_161 := RAX;
t2_162 := 332bv64;
RAX := PLUS_64(RAX, t2_162);
CF := bool2bv(LT_64(RAX, t1_161));
OF := AND_1((bool2bv((t1_161[64:63]) == (t2_162[64:63]))), (XOR_1((t1_161[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_161)), t2_162)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1690:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x1698:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x16a0:
t1_167 := RAX;
t2_168 := 80bv64;
RAX := PLUS_64(RAX, t2_168);
CF := bool2bv(LT_64(RAX, t1_167));
OF := AND_1((bool2bv((t1_167[64:63]) == (t2_168[64:63]))), (XOR_1((t1_167[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_167)), t2_168)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16a4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x16a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x16ae:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x16b4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x16b9:
t_175 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))))[1:0]));
SF := t_175[64:63];
ZF := bool2bv(0bv64 == t_175);

label_0x16bc:
if (bv2bool(ZF)) {
  goto label_0x16bf;
}

label_0x16be:
assume false;

label_0x16bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x16c4:
origDEST_179 := RAX;
origCOUNT_180 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), CF, LSHIFT_64(origDEST_179, (MINUS_64(64bv64, origCOUNT_180)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_180 == 1bv64)), origDEST_179[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), AF, unconstrained_64);

label_0x16c8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x16cf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x16d3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x16d8:
origDEST_185 := RCX;
origCOUNT_186 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), CF, LSHIFT_64(origDEST_185, (MINUS_64(64bv64, origCOUNT_186)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv64)), origDEST_185[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), AF, unconstrained_66);

label_0x16dc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x16e0:
if (bv2bool(CF)) {
  goto label_0x16e3;
}

label_0x16e2:
assume false;

label_0x16e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x16e8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x16f0:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x16f2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x16f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x16fc:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x1700:
t1_191 := RAX;
t2_192 := 336bv64;
RAX := PLUS_64(RAX, t2_192);
CF := bool2bv(LT_64(RAX, t1_191));
OF := AND_1((bool2bv((t1_191[64:63]) == (t2_192[64:63]))), (XOR_1((t1_191[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_191)), t2_192)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1706:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x170e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1716:
t1_197 := RAX;
t2_198 := 84bv64;
RAX := PLUS_64(RAX, t2_198);
CF := bool2bv(LT_64(RAX, t1_197));
OF := AND_1((bool2bv((t1_197[64:63]) == (t2_198[64:63]))), (XOR_1((t1_197[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_197)), t2_198)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x171a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x171f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1724:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x172a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x172f:
t_205 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)), 2bv64)), (XOR_64((RSHIFT_64(t_205, 4bv64)), t_205)))))[1:0]));
SF := t_205[64:63];
ZF := bool2bv(0bv64 == t_205);

label_0x1732:
if (bv2bool(ZF)) {
  goto label_0x1735;
}

label_0x1734:
assume false;

label_0x1735:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x173a:
origDEST_209 := RAX;
origCOUNT_210 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), CF, LSHIFT_64(origDEST_209, (MINUS_64(64bv64, origCOUNT_210)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_210 == 1bv64)), origDEST_209[64:63], unconstrained_73));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_210 == 0bv64)), AF, unconstrained_74);

label_0x173e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1745:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1749:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x174e:
origDEST_215 := RCX;
origCOUNT_216 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), CF, LSHIFT_64(origDEST_215, (MINUS_64(64bv64, origCOUNT_216)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_216 == 1bv64)), origDEST_215[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_216 == 0bv64)), AF, unconstrained_76);

label_0x1752:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_77;
SF := unconstrained_78;
AF := unconstrained_79;
PF := unconstrained_80;

label_0x1756:
if (bv2bool(CF)) {
  goto label_0x1759;
}

label_0x1758:
assume false;

label_0x1759:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x175e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x1766:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1768:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x176a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1772:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x1776:
t1_221 := RAX;
t2_222 := 316bv64;
RAX := PLUS_64(RAX, t2_222);
CF := bool2bv(LT_64(RAX, t1_221));
OF := AND_1((bool2bv((t1_221[64:63]) == (t2_222[64:63]))), (XOR_1((t1_221[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_221)), t2_222)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x177c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x1784:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x178c:
t1_227 := RAX;
t2_228 := 88bv64;
RAX := PLUS_64(RAX, t2_228);
CF := bool2bv(LT_64(RAX, t1_227));
OF := AND_1((bool2bv((t1_227[64:63]) == (t2_228[64:63]))), (XOR_1((t1_227[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_227)), t2_228)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1790:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x1795:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x179a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_81;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17a0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17a5:
t_235 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))))[1:0]));
SF := t_235[64:63];
ZF := bool2bv(0bv64 == t_235);

label_0x17a8:
if (bv2bool(ZF)) {
  goto label_0x17ab;
}

label_0x17aa:
assume false;

label_0x17ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x17b0:
origDEST_239 := RAX;
origCOUNT_240 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_83));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_84);

label_0x17b4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x17bb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x17bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x17c4:
origDEST_245 := RCX;
origCOUNT_246 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_86);

label_0x17c8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_87;
SF := unconstrained_88;
AF := unconstrained_89;
PF := unconstrained_90;

label_0x17cc:
if (bv2bool(CF)) {
  goto label_0x17cf;
}

label_0x17ce:
assume false;

label_0x17cf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x17d4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x17dc:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x17de:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x17e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x17e8:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x17ec:
t1_251 := RAX;
t2_252 := 320bv64;
RAX := PLUS_64(RAX, t2_252);
CF := bool2bv(LT_64(RAX, t1_251));
OF := AND_1((bool2bv((t1_251[64:63]) == (t2_252[64:63]))), (XOR_1((t1_251[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_251)), t2_252)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17f2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RAX);

label_0x17fa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1802:
t1_257 := RAX;
t2_258 := 92bv64;
RAX := PLUS_64(RAX, t2_258);
CF := bool2bv(LT_64(RAX, t1_257));
OF := AND_1((bool2bv((t1_257[64:63]) == (t2_258[64:63]))), (XOR_1((t1_257[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_257)), t2_258)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1806:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x180e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1816:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x181c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1821:
t_265 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)), 2bv64)), (XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)), 2bv64)), (XOR_64((RSHIFT_64(t_265, 4bv64)), t_265)))))[1:0]));
SF := t_265[64:63];
ZF := bool2bv(0bv64 == t_265);

label_0x1824:
if (bv2bool(ZF)) {
  goto label_0x1827;
}

label_0x1826:
assume false;

label_0x1827:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x182f:
origDEST_269 := RAX;
origCOUNT_270 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_94);

label_0x1833:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x183a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x183e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1846:
origDEST_275 := RCX;
origCOUNT_276 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), CF, LSHIFT_64(origDEST_275, (MINUS_64(64bv64, origCOUNT_276)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_276 == 1bv64)), origDEST_275[64:63], unconstrained_95));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_276 == 0bv64)), AF, unconstrained_96);

label_0x184a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x184e:
if (bv2bool(CF)) {
  goto label_0x1851;
}

label_0x1850:
assume false;

label_0x1851:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1859:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x1861:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1863:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1865:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x186d:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 96bv64));

label_0x1871:
t1_281 := RAX;
t2_282 := 304bv64;
RAX := PLUS_64(RAX, t2_282);
CF := bool2bv(LT_64(RAX, t1_281));
OF := AND_1((bool2bv((t1_281[64:63]) == (t2_282[64:63]))), (XOR_1((t1_281[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_281)), t2_282)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1877:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0x187f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1887:
t1_287 := RAX;
t2_288 := 56bv64;
RAX := PLUS_64(RAX, t2_288);
CF := bool2bv(LT_64(RAX, t1_287));
OF := AND_1((bool2bv((t1_287[64:63]) == (t2_288[64:63]))), (XOR_1((t1_287[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_287)), t2_288)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x188b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x1893:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x189b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_101;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18a1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x18a6:
t_295 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_102;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)), 2bv64)), (XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)), 2bv64)), (XOR_64((RSHIFT_64(t_295, 4bv64)), t_295)))))[1:0]));
SF := t_295[64:63];
ZF := bool2bv(0bv64 == t_295);

label_0x18a9:
if (bv2bool(ZF)) {
  goto label_0x18ac;
}

label_0x18ab:
assume false;

label_0x18ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18b4:
origDEST_299 := RAX;
origCOUNT_300 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), CF, LSHIFT_64(origDEST_299, (MINUS_64(64bv64, origCOUNT_300)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_300 == 1bv64)), origDEST_299[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), AF, unconstrained_104);

label_0x18b8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x18bf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x18c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18cb:
origDEST_305 := RCX;
origCOUNT_306 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), CF, LSHIFT_64(origDEST_305, (MINUS_64(64bv64, origCOUNT_306)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_306 == 1bv64)), origDEST_305[64:63], unconstrained_105));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_306 == 0bv64)), AF, unconstrained_106);

label_0x18cf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_107;
SF := unconstrained_108;
AF := unconstrained_109;
PF := unconstrained_110;

label_0x18d3:
if (bv2bool(CF)) {
  goto label_0x18d6;
}

label_0x18d5:
assume false;

label_0x18d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x18de:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x18e6:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x18e8:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x18ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x18f2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x18fa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 56bv64)));

label_0x18fd:
t_311 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 56bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 56bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 56bv64)))))));
RAX := (0bv32 ++ t_311[32:0]);
OF := bool2bv(t_311 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_311 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_111;
SF := unconstrained_112;
ZF := unconstrained_113;
AF := unconstrained_114;

label_0x1901:
mem := STORE_LE_32(mem, PLUS_64(RSP, 184bv64), RAX[32:0]);

label_0x1908:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1910:
t1_313 := RAX;
t2_314 := 60bv64;
RAX := PLUS_64(RAX, t2_314);
CF := bool2bv(LT_64(RAX, t1_313));
OF := AND_1((bool2bv((t1_313[64:63]) == (t2_314[64:63]))), (XOR_1((t1_313[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_313)), t2_314)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1914:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x191c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1924:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_115;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x192a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x192f:
t_321 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)), 2bv64)), (XOR_64((RSHIFT_64(t_321, 4bv64)), t_321)))))[1:0]));
SF := t_321[64:63];
ZF := bool2bv(0bv64 == t_321);

label_0x1932:
if (bv2bool(ZF)) {
  goto label_0x1935;
}

label_0x1934:
assume false;

label_0x1935:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x193d:
origDEST_325 := RAX;
origCOUNT_326 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), CF, LSHIFT_64(origDEST_325, (MINUS_64(64bv64, origCOUNT_326)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_326 == 1bv64)), origDEST_325[64:63], unconstrained_117));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_326 == 0bv64)), AF, unconstrained_118);

label_0x1941:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1948:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x194c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1954:
origDEST_331 := RCX;
origCOUNT_332 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), CF, LSHIFT_64(origDEST_331, (MINUS_64(64bv64, origCOUNT_332)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_332 == 1bv64)), origDEST_331[64:63], unconstrained_119));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_332 == 0bv64)), AF, unconstrained_120);

label_0x1958:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_121;
SF := unconstrained_122;
AF := unconstrained_123;
PF := unconstrained_124;

label_0x195c:
if (bv2bool(CF)) {
  goto label_0x195f;
}

label_0x195e:
assume false;

label_0x195f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1967:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x196e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1970:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1978:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 104bv64))));

label_0x197c:
t_337 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_337, 4bv32)), t_337)), 2bv32)), (XOR_32((RSHIFT_32(t_337, 4bv32)), t_337)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_337, 4bv32)), t_337)), 2bv32)), (XOR_32((RSHIFT_32(t_337, 4bv32)), t_337)))))[1:0]));
SF := t_337[32:31];
ZF := bool2bv(0bv32 == t_337);

label_0x197e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x19ea;
}

label_0x1980:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1988:
t1_341 := RAX;
t2_342 := 36bv64;
RAX := PLUS_64(RAX, t2_342);
CF := bool2bv(LT_64(RAX, t1_341));
OF := AND_1((bool2bv((t1_341[64:63]) == (t2_342[64:63]))), (XOR_1((t1_341[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_341)), t2_342)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x198c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x1994:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x199c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x19a2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x19a7:
t_349 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)), 2bv64)), (XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)), 2bv64)), (XOR_64((RSHIFT_64(t_349, 4bv64)), t_349)))))[1:0]));
SF := t_349[64:63];
ZF := bool2bv(0bv64 == t_349);

label_0x19aa:
if (bv2bool(ZF)) {
  goto label_0x19ad;
}

label_0x19ac:
assume false;

label_0x19ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19b5:
origDEST_353 := RAX;
origCOUNT_354 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), CF, LSHIFT_64(origDEST_353, (MINUS_64(64bv64, origCOUNT_354)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_354 == 1bv64)), origDEST_353[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_354 == 0bv64)), AF, unconstrained_129);

label_0x19b9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x19c0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x19c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19cc:
origDEST_359 := RCX;
origCOUNT_360 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), CF, LSHIFT_64(origDEST_359, (MINUS_64(64bv64, origCOUNT_360)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_360 == 1bv64)), origDEST_359[64:63], unconstrained_130));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_360 == 0bv64)), AF, unconstrained_131);

label_0x19d0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_132;
SF := unconstrained_133;
AF := unconstrained_134;
PF := unconstrained_135;

label_0x19d4:
if (bv2bool(CF)) {
  goto label_0x19d7;
}

label_0x19d6:
assume false;

label_0x19d7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x19df:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x19e5:
goto label_0x1c72;

label_0x19ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x19f2:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 40bv64));

label_0x19f6:
t1_365 := RAX;
t2_366 := 16bv64;
RAX := PLUS_64(RAX, t2_366);
CF := bool2bv(LT_64(RAX, t1_365));
OF := AND_1((bool2bv((t1_365[64:63]) == (t2_366[64:63]))), (XOR_1((t1_365[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_365)), t2_366)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x19fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x1a02:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a0a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a10:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a15:
t_373 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_137;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_373, 4bv64)), t_373)), 2bv64)), (XOR_64((RSHIFT_64(t_373, 4bv64)), t_373)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_373, 4bv64)), t_373)), 2bv64)), (XOR_64((RSHIFT_64(t_373, 4bv64)), t_373)))))[1:0]));
SF := t_373[64:63];
ZF := bool2bv(0bv64 == t_373);

label_0x1a18:
if (bv2bool(ZF)) {
  goto label_0x1a1b;
}

label_0x1a1a:
assume false;

label_0x1a1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a23:
origDEST_377 := RAX;
origCOUNT_378 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), CF, LSHIFT_64(origDEST_377, (MINUS_64(64bv64, origCOUNT_378)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_378 == 1bv64)), origDEST_377[64:63], unconstrained_138));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_378 == 0bv64)), AF, unconstrained_139);

label_0x1a27:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a2e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a32:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a3a:
origDEST_383 := RCX;
origCOUNT_384 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), CF, LSHIFT_64(origDEST_383, (MINUS_64(64bv64, origCOUNT_384)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_384 == 1bv64)), origDEST_383[64:63], unconstrained_140));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), AF, unconstrained_141);

label_0x1a3e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_142;
SF := unconstrained_143;
AF := unconstrained_144;
PF := unconstrained_145;

label_0x1a42:
if (bv2bool(CF)) {
  goto label_0x1a45;
}

label_0x1a44:
assume false;

label_0x1a45:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a4d:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1a53:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1a5b:
RDX := (0bv32 ++ 128bv32);

label_0x1a60:
RCX := RAX;

label_0x1a63:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6760bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1a68"} true;
call arbitrary_func();

label_0x1a68:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1a70:
t1_389 := RAX;
t2_390 := 16bv64;
RAX := PLUS_64(RAX, t2_390);
CF := bool2bv(LT_64(RAX, t1_389));
OF := AND_1((bool2bv((t1_389[64:63]) == (t2_390[64:63]))), (XOR_1((t1_389[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_389)), t2_390)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a74:
RDX := (0bv32 ++ 128bv32);

label_0x1a79:
RCX := RAX;

label_0x1a7c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6785bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1a81"} true;
call arbitrary_func();

label_0x1a81:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x1a88:
t_395 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_395, 1bv32)), (XOR_32(t_395, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_395)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1a8a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x1a8e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x1a95:
t_399 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_399, 1bv32)), (XOR_32(t_399, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_399)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1a97:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x1a9b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x1aa2:
t_403 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_403[32:31]) == (1bv32[32:31]))), (XOR_1((t_403[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_403)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1aa4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x1aa8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 288bv64)));

label_0x1aaf:
t_407 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_407[32:31]) == (1bv32[32:31]))), (XOR_1((t_407[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_407)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1ab1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x1ab5:
t_411 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_411)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_411, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_411, 4bv32)), t_411)), 2bv32)), (XOR_32((RSHIFT_32(t_411, 4bv32)), t_411)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_411, 4bv32)), t_411)), 2bv32)), (XOR_32((RSHIFT_32(t_411, 4bv32)), t_411)))))[1:0]));
SF := t_411[32:31];
ZF := bool2bv(0bv32 == t_411);

label_0x1aba:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1ac4;
}

label_0x1abc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 0bv32);

label_0x1ac4:
t_415 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_415)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_415, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_415, 4bv32)), t_415)), 2bv32)), (XOR_32((RSHIFT_32(t_415, 4bv32)), t_415)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_415, 4bv32)), t_415)), 2bv32)), (XOR_32((RSHIFT_32(t_415, 4bv32)), t_415)))))[1:0]));
SF := t_415[32:31];
ZF := bool2bv(0bv32 == t_415);

label_0x1ac9:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1ad3;
}

label_0x1acb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 0bv32);

label_0x1ad3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1adb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 88bv64)));

label_0x1ade:
t_419 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_419)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_419, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)), 2bv32)), (XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)), 2bv32)), (XOR_32((RSHIFT_32(t_419, 4bv32)), t_419)))))[1:0]));
SF := t_419[32:31];
ZF := bool2bv(0bv32 == t_419);

label_0x1ae2:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1af3;
}

label_0x1ae4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1aec:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 88bv64)));

label_0x1aef:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x1af3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1afb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x1afe:
t_423 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_423)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_423, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)), 2bv32)), (XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)), 2bv32)), (XOR_32((RSHIFT_32(t_423, 4bv32)), t_423)))))[1:0]));
SF := t_423[32:31];
ZF := bool2bv(0bv32 == t_423);

label_0x1b02:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1b13;
}

label_0x1b04:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1b0c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 92bv64)));

label_0x1b0f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x1b13:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x1b17:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1b1b:
goto label_0x1b27;

label_0x1b1d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1b21:
t_427 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_427[32:31]) == (1bv32[32:31]))), (XOR_1((t_427[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_427)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1b23:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1b27:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x1b2b:
t_431 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_431)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_431, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)), 2bv32)), (XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)), 2bv32)), (XOR_32((RSHIFT_32(t_431, 4bv32)), t_431)))))[1:0]));
SF := t_431[32:31];
ZF := bool2bv(0bv32 == t_431);

label_0x1b2f:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x1b91;
}

label_0x1b31:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x1b35:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x1b39:
goto label_0x1b45;

label_0x1b3b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x1b3f:
t_435 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_435[32:31]) == (1bv32[32:31]))), (XOR_1((t_435[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_435)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1b41:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x1b45:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x1b49:
t_439 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_439)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_439, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)), 2bv32)), (XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)), 2bv32)), (XOR_32((RSHIFT_32(t_439, 4bv32)), t_439)))))[1:0]));
SF := t_439[32:31];
ZF := bool2bv(0bv32 == t_439);

label_0x1b4d:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x1b8f;
}

label_0x1b4f:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1b54:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x1b58:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1b60:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7013bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1b65"} true;
call arbitrary_func();

label_0x1b65:
t_443 := MINUS_64((LOAD_LE_64(mem, RAX)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RAX)), t_443)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_443, (LOAD_LE_64(mem, RAX)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)), 2bv64)), (XOR_64((RSHIFT_64(t_443, 4bv64)), t_443)))))[1:0]));
SF := t_443[64:63];
ZF := bool2bv(0bv64 == t_443);

label_0x1b69:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b8d;
}

label_0x1b6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1b73:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1b78:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x1b7d:
RDX := RAX;

label_0x1b80:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1b88:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7053bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1b8d"} true;
call arbitrary_func();

label_0x1b8d:
goto label_0x1b3b;

label_0x1b8f:
goto label_0x1b1d;

label_0x1b91:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1b99:
t1_447 := RAX;
t2_448 := 32bv64;
RAX := PLUS_64(RAX, t2_448);
CF := bool2bv(LT_64(RAX, t1_447));
OF := AND_1((bool2bv((t1_447[64:63]) == (t2_448[64:63]))), (XOR_1((t1_447[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_447)), t2_448)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b9d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x1ba5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1bad:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1bb3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1bb8:
t_455 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_455, 4bv64)), t_455)), 2bv64)), (XOR_64((RSHIFT_64(t_455, 4bv64)), t_455)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_455, 4bv64)), t_455)), 2bv64)), (XOR_64((RSHIFT_64(t_455, 4bv64)), t_455)))))[1:0]));
SF := t_455[64:63];
ZF := bool2bv(0bv64 == t_455);

label_0x1bbb:
if (bv2bool(ZF)) {
  goto label_0x1bbe;
}

label_0x1bbd:
assume false;

label_0x1bbe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1bc6:
origDEST_459 := RAX;
origCOUNT_460 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), CF, LSHIFT_64(origDEST_459, (MINUS_64(64bv64, origCOUNT_460)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_460 == 1bv64)), origDEST_459[64:63], unconstrained_148));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), AF, unconstrained_149);

label_0x1bca:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1bd1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1bd5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1bdd:
origDEST_465 := RCX;
origCOUNT_466 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), CF, LSHIFT_64(origDEST_465, (MINUS_64(64bv64, origCOUNT_466)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_466 == 1bv64)), origDEST_465[64:63], unconstrained_150));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), AF, unconstrained_151);

label_0x1be1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_152;
SF := unconstrained_153;
AF := unconstrained_154;
PF := unconstrained_155;

label_0x1be5:
if (bv2bool(CF)) {
  goto label_0x1be8;
}

label_0x1be7:
assume false;

label_0x1be8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1bf0:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x1bf3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1bfb:
t1_471 := RAX;
t2_472 := 8bv64;
RAX := PLUS_64(RAX, t2_472);
CF := bool2bv(LT_64(RAX, t1_471));
OF := AND_1((bool2bv((t1_471[64:63]) == (t2_472[64:63]))), (XOR_1((t1_471[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_471)), t2_472)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1bff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x1c07:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1c0f:
t1_477 := RAX;
t2_478 := 36bv64;
RAX := PLUS_64(RAX, t2_478);
CF := bool2bv(LT_64(RAX, t1_477));
OF := AND_1((bool2bv((t1_477[64:63]) == (t2_478[64:63]))), (XOR_1((t1_477[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_477)), t2_478)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c13:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x1c1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1c23:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c29:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1c2e:
t_485 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_485, 4bv64)), t_485)), 2bv64)), (XOR_64((RSHIFT_64(t_485, 4bv64)), t_485)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_485, 4bv64)), t_485)), 2bv64)), (XOR_64((RSHIFT_64(t_485, 4bv64)), t_485)))))[1:0]));
SF := t_485[64:63];
ZF := bool2bv(0bv64 == t_485);

label_0x1c31:
if (bv2bool(ZF)) {
  goto label_0x1c34;
}

label_0x1c33:
assume false;

label_0x1c34:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1c3c:
origDEST_489 := RAX;
origCOUNT_490 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), CF, LSHIFT_64(origDEST_489, (MINUS_64(64bv64, origCOUNT_490)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_490 == 1bv64)), origDEST_489[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), AF, unconstrained_159);

label_0x1c40:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1c47:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1c4b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1c53:
origDEST_495 := RCX;
origCOUNT_496 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), CF, LSHIFT_64(origDEST_495, (MINUS_64(64bv64, origCOUNT_496)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_496 == 1bv64)), origDEST_495[64:63], unconstrained_160));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_496 == 0bv64)), AF, unconstrained_161);

label_0x1c57:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_162;
SF := unconstrained_163;
AF := unconstrained_164;
PF := unconstrained_165;

label_0x1c5b:
if (bv2bool(CF)) {
  goto label_0x1c5e;
}

label_0x1c5d:
assume false;

label_0x1c5e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x1c66:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x1c6e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x1c70:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1c72:
t1_501 := RSP;
t2_502 := 264bv64;
RSP := PLUS_64(RSP, t2_502);
CF := bool2bv(LT_64(RSP, t1_501));
OF := AND_1((bool2bv((t1_501[64:63]) == (t2_502[64:63]))), (XOR_1((t1_501[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_501)), t2_502)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1c79:

ra_507 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_120,origCOUNT_126,origCOUNT_150,origCOUNT_156,origCOUNT_18,origCOUNT_180,origCOUNT_186,origCOUNT_210,origCOUNT_216,origCOUNT_24,origCOUNT_240,origCOUNT_246,origCOUNT_270,origCOUNT_276,origCOUNT_300,origCOUNT_306,origCOUNT_326,origCOUNT_332,origCOUNT_354,origCOUNT_360,origCOUNT_378,origCOUNT_384,origCOUNT_42,origCOUNT_460,origCOUNT_466,origCOUNT_48,origCOUNT_490,origCOUNT_496,origCOUNT_66,origCOUNT_72,origCOUNT_90,origCOUNT_96,origDEST_119,origDEST_125,origDEST_149,origDEST_155,origDEST_17,origDEST_179,origDEST_185,origDEST_209,origDEST_215,origDEST_23,origDEST_239,origDEST_245,origDEST_269,origDEST_275,origDEST_299,origDEST_305,origDEST_325,origDEST_331,origDEST_353,origDEST_359,origDEST_377,origDEST_383,origDEST_41,origDEST_459,origDEST_465,origDEST_47,origDEST_489,origDEST_495,origDEST_65,origDEST_71,origDEST_89,origDEST_95,ra_507,t1_101,t1_107,t1_131,t1_137,t1_161,t1_167,t1_191,t1_197,t1_221,t1_227,t1_251,t1_257,t1_281,t1_287,t1_29,t1_313,t1_341,t1_365,t1_389,t1_447,t1_471,t1_477,t1_5,t1_501,t1_53,t1_77,t2_102,t2_108,t2_132,t2_138,t2_162,t2_168,t2_192,t2_198,t2_222,t2_228,t2_252,t2_258,t2_282,t2_288,t2_30,t2_314,t2_342,t2_366,t2_390,t2_448,t2_472,t2_478,t2_502,t2_54,t2_6,t2_78,t_1,t_115,t_13,t_145,t_175,t_205,t_235,t_265,t_295,t_311,t_321,t_337,t_349,t_37,t_373,t_395,t_399,t_403,t_407,t_411,t_415,t_419,t_423,t_427,t_431,t_435,t_439,t_443,t_455,t_485,t_61,t_85;

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
var origCOUNT_120: bv64;
var origCOUNT_126: bv64;
var origCOUNT_150: bv64;
var origCOUNT_156: bv64;
var origCOUNT_18: bv64;
var origCOUNT_180: bv64;
var origCOUNT_186: bv64;
var origCOUNT_210: bv64;
var origCOUNT_216: bv64;
var origCOUNT_24: bv64;
var origCOUNT_240: bv64;
var origCOUNT_246: bv64;
var origCOUNT_270: bv64;
var origCOUNT_276: bv64;
var origCOUNT_300: bv64;
var origCOUNT_306: bv64;
var origCOUNT_326: bv64;
var origCOUNT_332: bv64;
var origCOUNT_354: bv64;
var origCOUNT_360: bv64;
var origCOUNT_378: bv64;
var origCOUNT_384: bv64;
var origCOUNT_42: bv64;
var origCOUNT_460: bv64;
var origCOUNT_466: bv64;
var origCOUNT_48: bv64;
var origCOUNT_490: bv64;
var origCOUNT_496: bv64;
var origCOUNT_66: bv64;
var origCOUNT_72: bv64;
var origCOUNT_90: bv64;
var origCOUNT_96: bv64;
var origDEST_119: bv64;
var origDEST_125: bv64;
var origDEST_149: bv64;
var origDEST_155: bv64;
var origDEST_17: bv64;
var origDEST_179: bv64;
var origDEST_185: bv64;
var origDEST_209: bv64;
var origDEST_215: bv64;
var origDEST_23: bv64;
var origDEST_239: bv64;
var origDEST_245: bv64;
var origDEST_269: bv64;
var origDEST_275: bv64;
var origDEST_299: bv64;
var origDEST_305: bv64;
var origDEST_325: bv64;
var origDEST_331: bv64;
var origDEST_353: bv64;
var origDEST_359: bv64;
var origDEST_377: bv64;
var origDEST_383: bv64;
var origDEST_41: bv64;
var origDEST_459: bv64;
var origDEST_465: bv64;
var origDEST_47: bv64;
var origDEST_489: bv64;
var origDEST_495: bv64;
var origDEST_65: bv64;
var origDEST_71: bv64;
var origDEST_89: bv64;
var origDEST_95: bv64;
var ra_507: bv64;
var t1_101: bv64;
var t1_107: bv64;
var t1_131: bv64;
var t1_137: bv64;
var t1_161: bv64;
var t1_167: bv64;
var t1_191: bv64;
var t1_197: bv64;
var t1_221: bv64;
var t1_227: bv64;
var t1_251: bv64;
var t1_257: bv64;
var t1_281: bv64;
var t1_287: bv64;
var t1_29: bv64;
var t1_313: bv64;
var t1_341: bv64;
var t1_365: bv64;
var t1_389: bv64;
var t1_447: bv64;
var t1_471: bv64;
var t1_477: bv64;
var t1_5: bv64;
var t1_501: bv64;
var t1_53: bv64;
var t1_77: bv64;
var t2_102: bv64;
var t2_108: bv64;
var t2_132: bv64;
var t2_138: bv64;
var t2_162: bv64;
var t2_168: bv64;
var t2_192: bv64;
var t2_198: bv64;
var t2_222: bv64;
var t2_228: bv64;
var t2_252: bv64;
var t2_258: bv64;
var t2_282: bv64;
var t2_288: bv64;
var t2_30: bv64;
var t2_314: bv64;
var t2_342: bv64;
var t2_366: bv64;
var t2_390: bv64;
var t2_448: bv64;
var t2_472: bv64;
var t2_478: bv64;
var t2_502: bv64;
var t2_54: bv64;
var t2_6: bv64;
var t2_78: bv64;
var t_1: bv64;
var t_115: bv64;
var t_13: bv64;
var t_145: bv64;
var t_175: bv64;
var t_205: bv64;
var t_235: bv64;
var t_265: bv64;
var t_295: bv64;
var t_311: bv64;
var t_321: bv64;
var t_337: bv32;
var t_349: bv64;
var t_37: bv64;
var t_373: bv64;
var t_395: bv32;
var t_399: bv32;
var t_403: bv32;
var t_407: bv32;
var t_411: bv32;
var t_415: bv32;
var t_419: bv32;
var t_423: bv32;
var t_427: bv32;
var t_431: bv32;
var t_435: bv32;
var t_439: bv32;
var t_443: bv64;
var t_455: bv64;
var t_485: bv64;
var t_61: bv64;
var t_85: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(896bv64);
axiom policy(1312bv64);
axiom policy(3344bv64);
axiom policy(4224bv64);
axiom policy(4608bv64);
axiom policy(5136bv64);
axiom policy(7296bv64);
