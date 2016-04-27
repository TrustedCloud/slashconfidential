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
axiom _function_addr_low == 6080bv64;
axiom _function_addr_high == 7248bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x17c0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x17c5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x17ca:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x17ce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x17d3:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x17d7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x17dc:
t1_5 := RAX;
t2_6 := 4396bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17e2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x17e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x17ec:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x17f2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x17f7:
t_13 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x17fa:
if (bv2bool(ZF)) {
  goto label_0x17fd;
}

label_0x17fc:
assume false;

label_0x17fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1802:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x1806:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x180d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1811:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1816:
origDEST_23 := RCX;
origCOUNT_24 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x181a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x181e:
if (bv2bool(CF)) {
  goto label_0x1821;
}

label_0x1820:
assume false;

label_0x1821:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1826:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x182a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x182c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1831:
t1_29 := RAX;
t2_30 := 4400bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1837:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x183c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1841:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1847:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x184c:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x184f:
if (bv2bool(ZF)) {
  goto label_0x1852;
}

label_0x1851:
assume false;

label_0x1852:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1857:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_14);

label_0x185b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1862:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1866:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x186b:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_16);

label_0x186f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x1873:
if (bv2bool(CF)) {
  goto label_0x1876;
}

label_0x1875:
assume false;

label_0x1876:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x187b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x1882:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1884:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1889:
t1_53 := RAX;
t2_54 := 4388bv64;
RAX := PLUS_64(RAX, t2_54);
CF := bool2bv(LT_64(RAX, t1_53));
OF := AND_1((bool2bv((t1_53[64:63]) == (t2_54[64:63]))), (XOR_1((t1_53[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_53)), t2_54)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x188f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1894:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1899:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x189f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x18a4:
t_61 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))))[1:0]));
SF := t_61[64:63];
ZF := bool2bv(0bv64 == t_61);

label_0x18a7:
if (bv2bool(ZF)) {
  goto label_0x18aa;
}

label_0x18a9:
assume false;

label_0x18aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x18af:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_24);

label_0x18b3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x18ba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x18be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x18c3:
origDEST_71 := RCX;
origCOUNT_72 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_26);

label_0x18c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x18cb:
if (bv2bool(CF)) {
  goto label_0x18ce;
}

label_0x18cd:
assume false;

label_0x18ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x18d3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x18da:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x18dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x18e1:
t1_77 := RAX;
t2_78 := 4392bv64;
RAX := PLUS_64(RAX, t2_78);
CF := bool2bv(LT_64(RAX, t1_77));
OF := AND_1((bool2bv((t1_77[64:63]) == (t2_78[64:63]))), (XOR_1((t1_77[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_77)), t2_78)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x18ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x18f1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18f7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x18fc:
t_85 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)), 2bv64)), (XOR_64((RSHIFT_64(t_85, 4bv64)), t_85)))))[1:0]));
SF := t_85[64:63];
ZF := bool2bv(0bv64 == t_85);

label_0x18ff:
if (bv2bool(ZF)) {
  goto label_0x1902;
}

label_0x1901:
assume false;

label_0x1902:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1907:
origDEST_89 := RAX;
origCOUNT_90 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, LSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), origDEST_89[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_34);

label_0x190b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1912:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1916:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x191b:
origDEST_95 := RCX;
origCOUNT_96 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), CF, LSHIFT_64(origDEST_95, (MINUS_64(64bv64, origCOUNT_96)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_96 == 1bv64)), origDEST_95[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), AF, unconstrained_36);

label_0x191f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x1923:
if (bv2bool(CF)) {
  goto label_0x1926;
}

label_0x1925:
assume false;

label_0x1926:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x192b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x1932:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1934:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x193c:
goto label_0x1948;

label_0x193e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1942:
t_101 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_101[32:31]) == (1bv32[32:31]))), (XOR_1((t_101[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_101)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1944:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1948:
t_105 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_105)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_105, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))))[1:0]));
SF := t_105[32:31];
ZF := bool2bv(0bv32 == t_105);

label_0x1950:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x19cb;
}

label_0x1952:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x1957:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x195f:
t1_109 := RCX;
t2_110 := RAX;
RCX := PLUS_64(RCX, t2_110);
CF := bool2bv(LT_64(RCX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1962:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RCX);

label_0x1967:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x196c:
t1_115 := RAX;
t2_116 := 18bv64;
RAX := PLUS_64(RAX, t2_116);
CF := bool2bv(LT_64(RAX, t1_115));
OF := AND_1((bool2bv((t1_115[64:63]) == (t2_116[64:63]))), (XOR_1((t1_115[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_115)), t2_116)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1970:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x1975:
t1_121 := RAX;
t2_122 := RCX;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1978:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x197d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1982:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1988:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x198d:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x1990:
if (bv2bool(ZF)) {
  goto label_0x1993;
}

label_0x1992:
assume false;

label_0x1993:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1998:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_44);

label_0x199c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x19a3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x19a7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x19ac:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_46);

label_0x19b0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_47;
SF := unconstrained_48;
AF := unconstrained_49;
PF := unconstrained_50;

label_0x19b4:
if (bv2bool(CF)) {
  goto label_0x19b7;
}

label_0x19b6:
assume false;

label_0x19b7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x19bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x19c1:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x19c4:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x19c6:
goto label_0x193e;

label_0x19cb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x19d2:
t_145 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))), t_145)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_145, (LOAD_LE_32(mem, PLUS_64(RSP, 120bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0x19d6:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1aaa;
}

label_0x19dc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x19e3:
t_149 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))), t_149)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_149, (LOAD_LE_32(mem, PLUS_64(RSP, 128bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))))[1:0]));
SF := t_149[32:31];
ZF := bool2bv(0bv32 == t_149);

label_0x19ea:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1aaa;
}

label_0x19f0:
RCX := (0bv32 ++ 8bv32);

label_0x19f5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6650bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x19fa"} true;
call arbitrary_func();

label_0x19fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x19ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a07:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a0d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a12:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x1a15:
if (bv2bool(ZF)) {
  goto label_0x1a18;
}

label_0x1a17:
assume false;

label_0x1a18:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a20:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_54);

label_0x1a24:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a2b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a2f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a37:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_56);

label_0x1a3b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x1a3f:
if (bv2bool(CF)) {
  goto label_0x1a42;
}

label_0x1a41:
assume false;

label_0x1a42:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1a4a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1a4f:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x1a52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a5a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a60:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1a65:
t_173 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)), 2bv64)), (XOR_64((RSHIFT_64(t_173, 4bv64)), t_173)))))[1:0]));
SF := t_173[64:63];
ZF := bool2bv(0bv64 == t_173);

label_0x1a68:
if (bv2bool(ZF)) {
  goto label_0x1a6b;
}

label_0x1a6a:
assume false;

label_0x1a6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a73:
origDEST_177 := RAX;
origCOUNT_178 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), CF, LSHIFT_64(origDEST_177, (MINUS_64(64bv64, origCOUNT_178)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_178 == 1bv64)), origDEST_177[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), AF, unconstrained_64);

label_0x1a77:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1a7e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1a82:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a8a:
origDEST_183 := RCX;
origCOUNT_184 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_66);

label_0x1a8e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x1a92:
if (bv2bool(CF)) {
  goto label_0x1a95;
}

label_0x1a94:
assume false;

label_0x1a95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1a9d:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1aa3:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x1aa5:
goto label_0x1c43;

label_0x1aaa:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x1ab2:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x1ab6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1abb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6848bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1ac0"} true;
call arbitrary_func();

label_0x1ac0:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1ac3:
t_189 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_71;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)), 2bv32)), (XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)), 2bv32)), (XOR_32((RSHIFT_32(t_189, 4bv32)), t_189)))))[1:0]));
SF := t_189[32:31];
ZF := bool2bv(0bv32 == t_189);

label_0x1ac5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b75;
}

label_0x1acb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1ad3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_72;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ad9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1ade:
t_195 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_73;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))))[1:0]));
SF := t_195[64:63];
ZF := bool2bv(0bv64 == t_195);

label_0x1ae1:
if (bv2bool(ZF)) {
  goto label_0x1ae4;
}

label_0x1ae3:
assume false;

label_0x1ae4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1aec:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_74));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_75);

label_0x1af0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1af7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1afb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1b03:
origDEST_205 := RCX;
origCOUNT_206 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_77);

label_0x1b07:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_78;
SF := unconstrained_79;
AF := unconstrained_80;
PF := unconstrained_81;

label_0x1b0b:
if (bv2bool(CF)) {
  goto label_0x1b0e;
}

label_0x1b0d:
assume false;

label_0x1b0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1b16:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x1b1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1b25:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_82;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b2b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1b30:
t_213 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_83;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))))[1:0]));
SF := t_213[64:63];
ZF := bool2bv(0bv64 == t_213);

label_0x1b33:
if (bv2bool(ZF)) {
  goto label_0x1b36;
}

label_0x1b35:
assume false;

label_0x1b36:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1b3e:
origDEST_217 := RAX;
origCOUNT_218 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), CF, LSHIFT_64(origDEST_217, (MINUS_64(64bv64, origCOUNT_218)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv64)), origDEST_217[64:63], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), AF, unconstrained_85);

label_0x1b42:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1b49:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1b4d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1b55:
origDEST_223 := RCX;
origCOUNT_224 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), CF, LSHIFT_64(origDEST_223, (MINUS_64(64bv64, origCOUNT_224)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_224 == 1bv64)), origDEST_223[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), AF, unconstrained_87);

label_0x1b59:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_88;
SF := unconstrained_89;
AF := unconstrained_90;
PF := unconstrained_91;

label_0x1b5d:
if (bv2bool(CF)) {
  goto label_0x1b60;
}

label_0x1b5f:
assume false;

label_0x1b60:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1b68:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1b6e:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_92;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1b70:
goto label_0x1c43;

label_0x1b75:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1b7d:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1b85:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1b8a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7055bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1b8f"} true;
call arbitrary_func();

label_0x1b8f:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x1b92:
t_229 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_93;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)), 2bv32)), (XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)), 2bv32)), (XOR_32((RSHIFT_32(t_229, 4bv32)), t_229)))))[1:0]));
SF := t_229[32:31];
ZF := bool2bv(0bv32 == t_229);

label_0x1b94:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c41;
}

label_0x1b9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1ba2:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ba8:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1bad:
t_235 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))))[1:0]));
SF := t_235[64:63];
ZF := bool2bv(0bv64 == t_235);

label_0x1bb0:
if (bv2bool(ZF)) {
  goto label_0x1bb3;
}

label_0x1bb2:
assume false;

label_0x1bb3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1bbb:
origDEST_239 := RAX;
origCOUNT_240 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_97);

label_0x1bbf:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1bc6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1bca:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1bd2:
origDEST_245 := RCX;
origCOUNT_246 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_99);

label_0x1bd6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_100;
SF := unconstrained_101;
AF := unconstrained_102;
PF := unconstrained_103;

label_0x1bda:
if (bv2bool(CF)) {
  goto label_0x1bdd;
}

label_0x1bdc:
assume false;

label_0x1bdd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x1be5:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x1bec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1bf4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_104;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1bfa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1bff:
t_253 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))))[1:0]));
SF := t_253[64:63];
ZF := bool2bv(0bv64 == t_253);

label_0x1c02:
if (bv2bool(ZF)) {
  goto label_0x1c05;
}

label_0x1c04:
assume false;

label_0x1c05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1c0d:
origDEST_257 := RAX;
origCOUNT_258 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_106));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_107);

label_0x1c11:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1c18:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1c1c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1c24:
origDEST_263 := RCX;
origCOUNT_264 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_109);

label_0x1c28:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_110;
SF := unconstrained_111;
AF := unconstrained_112;
PF := unconstrained_113;

label_0x1c2c:
if (bv2bool(CF)) {
  goto label_0x1c2f;
}

label_0x1c2e:
assume false;

label_0x1c2f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x1c37:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1c3d:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_114;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1c3f:
goto label_0x1c43;

label_0x1c41:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x1c43:
t1_269 := RSP;
t2_270 := 104bv64;
RSP := PLUS_64(RSP, t2_270);
CF := bool2bv(LT_64(RSP, t1_269));
OF := AND_1((bool2bv((t1_269[64:63]) == (t2_270[64:63]))), (XOR_1((t1_269[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_269)), t2_270)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1c47:

ra_275 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_134,origCOUNT_140,origCOUNT_160,origCOUNT_166,origCOUNT_178,origCOUNT_18,origCOUNT_184,origCOUNT_200,origCOUNT_206,origCOUNT_218,origCOUNT_224,origCOUNT_24,origCOUNT_240,origCOUNT_246,origCOUNT_258,origCOUNT_264,origCOUNT_42,origCOUNT_48,origCOUNT_66,origCOUNT_72,origCOUNT_90,origCOUNT_96,origDEST_133,origDEST_139,origDEST_159,origDEST_165,origDEST_17,origDEST_177,origDEST_183,origDEST_199,origDEST_205,origDEST_217,origDEST_223,origDEST_23,origDEST_239,origDEST_245,origDEST_257,origDEST_263,origDEST_41,origDEST_47,origDEST_65,origDEST_71,origDEST_89,origDEST_95,ra_275,t1_109,t1_115,t1_121,t1_269,t1_29,t1_5,t1_53,t1_77,t2_110,t2_116,t2_122,t2_270,t2_30,t2_54,t2_6,t2_78,t_1,t_101,t_105,t_129,t_13,t_145,t_149,t_155,t_173,t_189,t_195,t_213,t_229,t_235,t_253,t_37,t_61,t_85;

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
var origCOUNT_134: bv64;
var origCOUNT_140: bv64;
var origCOUNT_160: bv64;
var origCOUNT_166: bv64;
var origCOUNT_178: bv64;
var origCOUNT_18: bv64;
var origCOUNT_184: bv64;
var origCOUNT_200: bv64;
var origCOUNT_206: bv64;
var origCOUNT_218: bv64;
var origCOUNT_224: bv64;
var origCOUNT_24: bv64;
var origCOUNT_240: bv64;
var origCOUNT_246: bv64;
var origCOUNT_258: bv64;
var origCOUNT_264: bv64;
var origCOUNT_42: bv64;
var origCOUNT_48: bv64;
var origCOUNT_66: bv64;
var origCOUNT_72: bv64;
var origCOUNT_90: bv64;
var origCOUNT_96: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_159: bv64;
var origDEST_165: bv64;
var origDEST_17: bv64;
var origDEST_177: bv64;
var origDEST_183: bv64;
var origDEST_199: bv64;
var origDEST_205: bv64;
var origDEST_217: bv64;
var origDEST_223: bv64;
var origDEST_23: bv64;
var origDEST_239: bv64;
var origDEST_245: bv64;
var origDEST_257: bv64;
var origDEST_263: bv64;
var origDEST_41: bv64;
var origDEST_47: bv64;
var origDEST_65: bv64;
var origDEST_71: bv64;
var origDEST_89: bv64;
var origDEST_95: bv64;
var ra_275: bv64;
var t1_109: bv64;
var t1_115: bv64;
var t1_121: bv64;
var t1_269: bv64;
var t1_29: bv64;
var t1_5: bv64;
var t1_53: bv64;
var t1_77: bv64;
var t2_110: bv64;
var t2_116: bv64;
var t2_122: bv64;
var t2_270: bv64;
var t2_30: bv64;
var t2_54: bv64;
var t2_6: bv64;
var t2_78: bv64;
var t_1: bv64;
var t_101: bv32;
var t_105: bv32;
var t_129: bv64;
var t_13: bv64;
var t_145: bv32;
var t_149: bv32;
var t_155: bv64;
var t_173: bv64;
var t_189: bv32;
var t_195: bv64;
var t_213: bv64;
var t_229: bv32;
var t_235: bv64;
var t_253: bv64;
var t_37: bv64;
var t_61: bv64;
var t_85: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(64bv64);
axiom policy(448bv64);
axiom policy(1680bv64);
axiom policy(2128bv64);
axiom policy(3744bv64);
axiom policy(6080bv64);
axiom policy(7248bv64);
axiom policy(8560bv64);
axiom policy(9472bv64);
axiom policy(9664bv64);
