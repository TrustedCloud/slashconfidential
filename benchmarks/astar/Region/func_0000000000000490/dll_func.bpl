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
axiom _function_addr_low == 1168bv64;
axiom _function_addr_high == 2208bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x490:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x495:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x499:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x49e:
t_1 := RSP;
RSP := MINUS_64(RSP, 120bv64);
CF := bool2bv(LT_64(t_1, 120bv64));
OF := AND_64((XOR_64(t_1, 120bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 120bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4a2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4aa:
t1_5 := RAX;
t2_6 := 20bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x4b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x4b8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4be:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4c3:
t_13 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x4c6:
if (bv2bool(ZF)) {
  goto label_0x4c9;
}

label_0x4c8:
assume false;

label_0x4c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x4ce:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x4d2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4d9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4dd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x4e2:
origDEST_23 := RCX;
origCOUNT_24 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x4e6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x4ea:
if (bv2bool(CF)) {
  goto label_0x4ed;
}

label_0x4ec:
assume false;

label_0x4ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x4f2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x4f9:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x503:
t1_29 := RAX;
t2_30 := 20bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x507:
t1_35 := RAX;
t2_36 := 4bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x50b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x510:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x515:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x51b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x520:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x523:
if (bv2bool(ZF)) {
  goto label_0x526;
}

label_0x525:
assume false;

label_0x526:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x52b:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_14);

label_0x52f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x536:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x53a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x53f:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_16);

label_0x543:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x547:
if (bv2bool(CF)) {
  goto label_0x54a;
}

label_0x549:
assume false;

label_0x54a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x54f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x556:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x558:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x560:
t1_59 := RAX;
t2_60 := 16bv64;
RAX := PLUS_64(RAX, t2_60);
CF := bool2bv(LT_64(RAX, t1_59));
OF := AND_1((bool2bv((t1_59[64:63]) == (t2_60[64:63]))), (XOR_1((t1_59[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_59)), t2_60)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x564:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x569:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x56e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x574:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x579:
t_67 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x57c:
if (bv2bool(ZF)) {
  goto label_0x57f;
}

label_0x57e:
assume false;

label_0x57f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x584:
origDEST_71 := RAX;
origCOUNT_72 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_24);

label_0x588:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x58f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x593:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x598:
origDEST_77 := RCX;
origCOUNT_78 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_26);

label_0x59c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x5a0:
if (bv2bool(CF)) {
  goto label_0x5a3;
}

label_0x5a2:
assume false;

label_0x5a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x5a8:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x5ae:
RDX := (0bv32 ++ 128bv32);

label_0x5b3:
RCX := PLUS_64((PLUS_64(0bv64, 1466bv64)), 0bv64)[64:0];

label_0x5ba:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1471bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5bf"} true;
call arbitrary_func();

label_0x5bf:
RDX := (0bv32 ++ 128bv32);

label_0x5c4:
RCX := PLUS_64((PLUS_64(0bv64, 1483bv64)), 0bv64)[64:0];

label_0x5cb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1488bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5d0"} true;
call arbitrary_func();

label_0x5d0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x5d8:
t1_83 := RAX;
t2_84 := 40bv64;
RAX := PLUS_64(RAX, t2_84);
CF := bool2bv(LT_64(RAX, t1_83));
OF := AND_1((bool2bv((t1_83[64:63]) == (t2_84[64:63]))), (XOR_1((t1_83[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_83)), t2_84)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5dc:
RDX := (0bv32 ++ 4bv32);

label_0x5e1:
RCX := RAX;

label_0x5e4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1513bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5e9"} true;
call arbitrary_func();

label_0x5e9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x5f0:
t_89 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_89, 1bv32)), (XOR_32(t_89, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_89)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5f2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x5f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x5fd:
t_93 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_93, 1bv32)), (XOR_32(t_93, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_93)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5ff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x603:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x60a:
t_97 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_97[32:31]) == (1bv32[32:31]))), (XOR_1((t_97[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_97)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x60c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x610:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x617:
t_101 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_101[32:31]) == (1bv32[32:31]))), (XOR_1((t_101[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_101)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x619:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x61d:
t_105 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_105)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_105, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))))[1:0]));
SF := t_105[32:31];
ZF := bool2bv(0bv32 == t_105);

label_0x622:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x62c;
}

label_0x624:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 0bv32);

label_0x62c:
t_109 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_109)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_109, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)), 2bv32)), (XOR_32((RSHIFT_32(t_109, 4bv32)), t_109)))))[1:0]));
SF := t_109[32:31];
ZF := bool2bv(0bv32 == t_109);

label_0x631:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x63b;
}

label_0x633:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 0bv32);

label_0x63b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x643:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x647:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 316bv64)));

label_0x64d:
t_113 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_113)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_113, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))))[1:0]));
SF := t_113[32:31];
ZF := bool2bv(0bv32 == t_113);

label_0x651:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x669;
}

label_0x653:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x65b:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x65f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 316bv64)));

label_0x665:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x669:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x671:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x675:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 320bv64)));

label_0x67b:
t_117 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_117)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_117, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x67f:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x697;
}

label_0x681:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x689:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x68d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 320bv64)));

label_0x693:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x697:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x69b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x69f:
goto label_0x6ab;

label_0x6a1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x6a5:
t_121 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_121[32:31]) == (1bv32[32:31]))), (XOR_1((t_121[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_121)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6a7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x6ab:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x6af:
t_125 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_125)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_125, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))))[1:0]));
SF := t_125[32:31];
ZF := bool2bv(0bv32 == t_125);

label_0x6b3:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x715;
}

label_0x6b5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x6b9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x6bd:
goto label_0x6c9;

label_0x6bf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x6c3:
t_129 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_129[32:31]) == (1bv32[32:31]))), (XOR_1((t_129[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_129)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x6c5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x6c9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x6cd:
t_133 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_133)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_133, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0x6d1:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x713;
}

label_0x6d3:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x6d8:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x6dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x6e4:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x6e8:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1773bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x6ed"} true;
call arbitrary_func();

label_0x6ed:
t_137 := MINUS_64((LOAD_LE_64(mem, RAX)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RAX)), t_137)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_137, (LOAD_LE_64(mem, RAX)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)), 2bv64)), (XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)), 2bv64)), (XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)))))[1:0]));
SF := t_137[64:63];
ZF := bool2bv(0bv64 == t_137);

label_0x6f1:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x711;
}

label_0x6f3:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x6f8:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x6fd:
RDX := PLUS_64((PLUS_64(0bv64, 1796bv64)), 0bv64)[64:0];

label_0x704:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x70c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1809bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x711"} true;
call arbitrary_func();

label_0x711:
goto label_0x6bf;

label_0x713:
goto label_0x6a1;

label_0x715:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(8bv64, 1819bv64)), 0bv64)));

label_0x71b:
mem := STORE_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1825bv64)), 0bv64), RAX[32:0]);

label_0x721:
t_141 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1831bv64)), 1bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1831bv64)), 1bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1831bv64)), 1bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1831bv64)), 1bv64))), t_141)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_141, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 1831bv64)), 1bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))))[1:0]));
SF := t_141[32:31];
ZF := bool2bv(0bv32 == t_141);

label_0x728:
if (bv2bool(ZF)) {
  goto label_0x77f;
}

label_0x72a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x732:
t1_145 := RAX;
t2_146 := 4bv64;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x736:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x73b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x740:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x746:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x74b:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0x74e:
if (bv2bool(ZF)) {
  goto label_0x751;
}

label_0x750:
assume false;

label_0x751:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x756:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_34);

label_0x75a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x761:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x765:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x76a:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_36);

label_0x76e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x772:
if (bv2bool(CF)) {
  goto label_0x775;
}

label_0x774:
assume false;

label_0x775:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x77a:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x77d:
goto label_0x7ef;

label_0x77f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x787:
t1_169 := RAX;
t2_170 := 4bv64;
RAX := PLUS_64(RAX, t2_170);
CF := bool2bv(LT_64(RAX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x78b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x790:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x795:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x79b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7a0:
t_177 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)), 2bv64)), (XOR_64((RSHIFT_64(t_177, 4bv64)), t_177)))))[1:0]));
SF := t_177[64:63];
ZF := bool2bv(0bv64 == t_177);

label_0x7a3:
if (bv2bool(ZF)) {
  goto label_0x7a6;
}

label_0x7a5:
assume false;

label_0x7a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7ab:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_44);

label_0x7af:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7b6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7ba:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7bf:
origDEST_187 := RCX;
origCOUNT_188 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_46);

label_0x7c3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x7c7:
if (bv2bool(CF)) {
  goto label_0x7ca;
}

label_0x7c9:
assume false;

label_0x7ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7cf:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x7d2:
RCX := PLUS_64((PLUS_64(0bv64, 2009bv64)), 0bv64)[64:0];

label_0x7d9:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2014bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7de"} true;
call arbitrary_func();

label_0x7de:
RCX := PLUS_64((PLUS_64(0bv64, 2021bv64)), 0bv64)[64:0];

label_0x7e5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2026bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x7ea"} true;
call arbitrary_func();

label_0x7ea:
goto label_0x889;

label_0x7ef:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(0bv64, 2037bv64)), 1bv64), 0bv8);

label_0x7f6:
t_193 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2044bv64)), 1bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2044bv64)), 1bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2044bv64)), 1bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2044bv64)), 1bv64))), t_193)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_193, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2044bv64)), 1bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)), 2bv32)), (XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)), 2bv32)), (XOR_32((RSHIFT_32(t_193, 4bv32)), t_193)))))[1:0]));
SF := t_193[32:31];
ZF := bool2bv(0bv32 == t_193);

label_0x7fd:
if (bv2bool(ZF)) {
  goto label_0x871;
}

label_0x7ff:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64((PLUS_64(0bv64, 2054bv64)), 0bv64))));

label_0x806:
t_197 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_197, 4bv32)), t_197)), 2bv32)), (XOR_32((RSHIFT_32(t_197, 4bv32)), t_197)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_197, 4bv32)), t_197)), 2bv32)), (XOR_32((RSHIFT_32(t_197, 4bv32)), t_197)))))[1:0]));
SF := t_197[32:31];
ZF := bool2bv(0bv32 == t_197);

label_0x808:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x838;
}

label_0x80a:
R8 := PLUS_64((PLUS_64(0bv64, 2065bv64)), 0bv64)[64:0];

label_0x811:
RDX := PLUS_64((PLUS_64(0bv64, 2072bv64)), 0bv64)[64:0];

label_0x818:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x820:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2085bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x825"} true;
call arbitrary_func();

label_0x825:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x82a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(8bv64, 2096bv64)), 0bv64)));

label_0x830:
mem := STORE_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2102bv64)), 0bv64), RAX[32:0]);

label_0x836:
goto label_0x864;

label_0x838:
R8 := PLUS_64((PLUS_64(0bv64, 2111bv64)), 0bv64)[64:0];

label_0x83f:
RDX := PLUS_64((PLUS_64(0bv64, 2118bv64)), 0bv64)[64:0];

label_0x846:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x84e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2131bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x853"} true;
call arbitrary_func();

label_0x853:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x858:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(8bv64, 2142bv64)), 0bv64)));

label_0x85e:
mem := STORE_LE_32(mem, PLUS_64((PLUS_64(0bv64, 2148bv64)), 0bv64), RAX[32:0]);

label_0x864:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x869:
mem := STORE_LE_8(mem, PLUS_64((PLUS_64(0bv64, 2159bv64)), 0bv64), RAX[32:0][8:0]);

label_0x86f:
goto label_0x7f6;

label_0x871:
RCX := PLUS_64((PLUS_64(0bv64, 2168bv64)), 0bv64)[64:0];

label_0x878:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2173bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x87d"} true;
call arbitrary_func();

label_0x87d:
RCX := PLUS_64((PLUS_64(0bv64, 2180bv64)), 0bv64)[64:0];

label_0x884:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 2185bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x889"} true;
call arbitrary_func();

label_0x889:
t1_201 := RSP;
t2_202 := 120bv64;
RSP := PLUS_64(RSP, t2_202);
CF := bool2bv(LT_64(RSP, t1_201));
OF := AND_1((bool2bv((t1_201[64:63]) == (t2_202[64:63]))), (XOR_1((t1_201[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_201)), t2_202)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x88d:

ra_207 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_158,origCOUNT_164,origCOUNT_18,origCOUNT_182,origCOUNT_188,origCOUNT_24,origCOUNT_48,origCOUNT_54,origCOUNT_72,origCOUNT_78,origDEST_157,origDEST_163,origDEST_17,origDEST_181,origDEST_187,origDEST_23,origDEST_47,origDEST_53,origDEST_71,origDEST_77,ra_207,t1_145,t1_169,t1_201,t1_29,t1_35,t1_5,t1_59,t1_83,t2_146,t2_170,t2_202,t2_30,t2_36,t2_6,t2_60,t2_84,t_1,t_101,t_105,t_109,t_113,t_117,t_121,t_125,t_129,t_13,t_133,t_137,t_141,t_153,t_177,t_193,t_197,t_43,t_67,t_89,t_93,t_97;

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
var origCOUNT_158: bv64;
var origCOUNT_164: bv64;
var origCOUNT_18: bv64;
var origCOUNT_182: bv64;
var origCOUNT_188: bv64;
var origCOUNT_24: bv64;
var origCOUNT_48: bv64;
var origCOUNT_54: bv64;
var origCOUNT_72: bv64;
var origCOUNT_78: bv64;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_17: bv64;
var origDEST_181: bv64;
var origDEST_187: bv64;
var origDEST_23: bv64;
var origDEST_47: bv64;
var origDEST_53: bv64;
var origDEST_71: bv64;
var origDEST_77: bv64;
var ra_207: bv64;
var t1_145: bv64;
var t1_169: bv64;
var t1_201: bv64;
var t1_29: bv64;
var t1_35: bv64;
var t1_5: bv64;
var t1_59: bv64;
var t1_83: bv64;
var t2_146: bv64;
var t2_170: bv64;
var t2_202: bv64;
var t2_30: bv64;
var t2_36: bv64;
var t2_6: bv64;
var t2_60: bv64;
var t2_84: bv64;
var t_1: bv64;
var t_101: bv32;
var t_105: bv32;
var t_109: bv32;
var t_113: bv32;
var t_117: bv32;
var t_121: bv32;
var t_125: bv32;
var t_129: bv32;
var t_13: bv64;
var t_133: bv32;
var t_137: bv64;
var t_141: bv32;
var t_153: bv64;
var t_177: bv64;
var t_193: bv32;
var t_197: bv32;
var t_43: bv64;
var t_67: bv64;
var t_89: bv32;
var t_93: bv32;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(752bv64);
axiom policy(1168bv64);
axiom policy(2208bv64);
axiom policy(2336bv64);
