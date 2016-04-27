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
axiom _function_addr_low == 17728bv64;
axiom _function_addr_high == 19952bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x4540:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x4545:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x454a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x454f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x4554:
t_1 := RSP;
RSP := MINUS_64(RSP, 168bv64);
CF := bool2bv(LT_64(t_1, 168bv64));
OF := AND_64((XOR_64(t_1, 168bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 168bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x455b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x4563:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x4568:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x4571:
if (bv2bool(ZF)) {
  goto label_0x45c4;
}

label_0x4573:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x457b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4581:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4586:
t_11 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x4589:
if (bv2bool(ZF)) {
  goto label_0x458c;
}

label_0x458b:
assume false;

label_0x458c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4594:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_4);

label_0x4598:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x459f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x45a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x45ab:
origDEST_21 := RCX;
origCOUNT_22 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_6);

label_0x45af:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x45b3:
if (bv2bool(CF)) {
  goto label_0x45b6;
}

label_0x45b5:
assume false;

label_0x45b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x45be:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x45c4:
t_27 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_27)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_27, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x45ca:
if (bv2bool(ZF)) {
  goto label_0x4621;
}

label_0x45cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x45d1:
t1_31 := RAX;
t2_32 := 5096bv64;
RAX := PLUS_64(RAX, t2_32);
CF := bool2bv(LT_64(RAX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x45d7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x45dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x45e1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x45e7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x45ec:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x45ef:
if (bv2bool(ZF)) {
  goto label_0x45f2;
}

label_0x45f1:
assume false;

label_0x45f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x45f7:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0x45fb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4602:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4606:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x460b:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_16);

label_0x460f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x4613:
if (bv2bool(CF)) {
  goto label_0x4616;
}

label_0x4615:
assume false;

label_0x4616:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x461b:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4621:
t_55 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_55)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_55, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))))[1:0]));
SF := t_55[64:63];
ZF := bool2bv(0bv64 == t_55);

label_0x4627:
if (bv2bool(ZF)) {
  goto label_0x4642;
}

label_0x4629:
t_59 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_59)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_59, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))))[1:0]));
SF := t_59[64:63];
ZF := bool2bv(0bv64 == t_59);

label_0x4632:
if (bv2bool(ZF)) {
  goto label_0x4642;
}

label_0x4634:
t_63 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_63)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_63, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x463c:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x4700;
}

label_0x4642:
t_67 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_67)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_67, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)), 2bv64)), (XOR_64((RSHIFT_64(t_67, 4bv64)), t_67)))))[1:0]));
SF := t_67[64:63];
ZF := bool2bv(0bv64 == t_67);

label_0x464b:
if (bv2bool(ZF)) {
  goto label_0x469e;
}

label_0x464d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4655:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x465b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4660:
t_73 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)), 2bv64)), (XOR_64((RSHIFT_64(t_73, 4bv64)), t_73)))))[1:0]));
SF := t_73[64:63];
ZF := bool2bv(0bv64 == t_73);

label_0x4663:
if (bv2bool(ZF)) {
  goto label_0x4666;
}

label_0x4665:
assume false;

label_0x4666:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x466e:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_24);

label_0x4672:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4679:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x467d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4685:
origDEST_83 := RCX;
origCOUNT_84 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), CF, LSHIFT_64(origDEST_83, (MINUS_64(64bv64, origCOUNT_84)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_84 == 1bv64)), origDEST_83[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_84 == 0bv64)), AF, unconstrained_26);

label_0x4689:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x468d:
if (bv2bool(CF)) {
  goto label_0x4690;
}

label_0x468f:
assume false;

label_0x4690:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4698:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x469e:
t_89 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_89)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_89, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))))[1:0]));
SF := t_89[64:63];
ZF := bool2bv(0bv64 == t_89);

label_0x46a4:
if (bv2bool(ZF)) {
  goto label_0x46fb;
}

label_0x46a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x46ab:
t1_93 := RAX;
t2_94 := 5096bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x46b1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x46b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x46bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x46c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x46c6:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x46c9:
if (bv2bool(ZF)) {
  goto label_0x46cc;
}

label_0x46cb:
assume false;

label_0x46cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x46d1:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_34);

label_0x46d5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x46dc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x46e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x46e5:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_36);

label_0x46e9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x46ed:
if (bv2bool(CF)) {
  goto label_0x46f0;
}

label_0x46ef:
assume false;

label_0x46f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x46f5:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x46fb:
goto label_0x4ddf;

label_0x4700:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4705:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 5008bv64))));

label_0x470c:
t_117 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x470e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x47d2;
}

label_0x4714:
t_121 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_121)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_121, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)), 2bv64)), (XOR_64((RSHIFT_64(t_121, 4bv64)), t_121)))))[1:0]));
SF := t_121[64:63];
ZF := bool2bv(0bv64 == t_121);

label_0x471d:
if (bv2bool(ZF)) {
  goto label_0x4770;
}

label_0x471f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4727:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x472d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4732:
t_127 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)), 2bv64)), (XOR_64((RSHIFT_64(t_127, 4bv64)), t_127)))))[1:0]));
SF := t_127[64:63];
ZF := bool2bv(0bv64 == t_127);

label_0x4735:
if (bv2bool(ZF)) {
  goto label_0x4738;
}

label_0x4737:
assume false;

label_0x4738:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4740:
origDEST_131 := RAX;
origCOUNT_132 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), CF, LSHIFT_64(origDEST_131, (MINUS_64(64bv64, origCOUNT_132)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_132 == 1bv64)), origDEST_131[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_132 == 0bv64)), AF, unconstrained_45);

label_0x4744:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x474b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x474f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4757:
origDEST_137 := RCX;
origCOUNT_138 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), CF, LSHIFT_64(origDEST_137, (MINUS_64(64bv64, origCOUNT_138)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_138 == 1bv64)), origDEST_137[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_138 == 0bv64)), AF, unconstrained_47);

label_0x475b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0x475f:
if (bv2bool(CF)) {
  goto label_0x4762;
}

label_0x4761:
assume false;

label_0x4762:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x476a:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x4770:
t_143 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_143)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_143, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x4776:
if (bv2bool(ZF)) {
  goto label_0x47cd;
}

label_0x4778:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x477d:
t1_147 := RAX;
t2_148 := 5096bv64;
RAX := PLUS_64(RAX, t2_148);
CF := bool2bv(LT_64(RAX, t1_147));
OF := AND_1((bool2bv((t1_147[64:63]) == (t2_148[64:63]))), (XOR_1((t1_147[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_147)), t2_148)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4783:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x4788:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x478d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4793:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4798:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_53;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x479b:
if (bv2bool(ZF)) {
  goto label_0x479e;
}

label_0x479d:
assume false;

label_0x479e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x47a3:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_54));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_55);

label_0x47a7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x47ae:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x47b2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x47b7:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_57);

label_0x47bb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_58;
SF := unconstrained_59;
AF := unconstrained_60;
PF := unconstrained_61;

label_0x47bf:
if (bv2bool(CF)) {
  goto label_0x47c2;
}

label_0x47c1:
assume false;

label_0x47c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x47c7:
mem := STORE_LE_32(mem, RAX, 4294967295bv32);

label_0x47cd:
goto label_0x4ddf;

label_0x47d2:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_62;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x47d4:
t_171 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)), 2bv32)), (XOR_32((RSHIFT_32(t_171, 4bv32)), t_171)))))[1:0]));
SF := t_171[32:31];
ZF := bool2bv(0bv32 == t_171);

label_0x47d6:
if (bv2bool(ZF)) {
  goto label_0x489a;
}

label_0x47dc:
t_175 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_175)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_175, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)), 2bv64)), (XOR_64((RSHIFT_64(t_175, 4bv64)), t_175)))))[1:0]));
SF := t_175[64:63];
ZF := bool2bv(0bv64 == t_175);

label_0x47e5:
if (bv2bool(ZF)) {
  goto label_0x4838;
}

label_0x47e7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x47ef:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_64;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x47f5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x47fa:
t_181 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)), 2bv64)), (XOR_64((RSHIFT_64(t_181, 4bv64)), t_181)))))[1:0]));
SF := t_181[64:63];
ZF := bool2bv(0bv64 == t_181);

label_0x47fd:
if (bv2bool(ZF)) {
  goto label_0x4800;
}

label_0x47ff:
assume false;

label_0x4800:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4808:
origDEST_185 := RAX;
origCOUNT_186 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), CF, LSHIFT_64(origDEST_185, (MINUS_64(64bv64, origCOUNT_186)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_186 == 1bv64)), origDEST_185[64:63], unconstrained_66));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_186 == 0bv64)), AF, unconstrained_67);

label_0x480c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4813:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4817:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x481f:
origDEST_191 := RCX;
origCOUNT_192 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_68));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_69);

label_0x4823:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_70;
SF := unconstrained_71;
AF := unconstrained_72;
PF := unconstrained_73;

label_0x4827:
if (bv2bool(CF)) {
  goto label_0x482a;
}

label_0x4829:
assume false;

label_0x482a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4832:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x4838:
t_197 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_197)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_197, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))))[1:0]));
SF := t_197[64:63];
ZF := bool2bv(0bv64 == t_197);

label_0x483e:
if (bv2bool(ZF)) {
  goto label_0x4895;
}

label_0x4840:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4845:
t1_201 := RAX;
t2_202 := 5096bv64;
RAX := PLUS_64(RAX, t2_202);
CF := bool2bv(LT_64(RAX, t1_201));
OF := AND_1((bool2bv((t1_201[64:63]) == (t2_202[64:63]))), (XOR_1((t1_201[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_201)), t2_202)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x484b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x4850:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x4855:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_74;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x485b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4860:
t_209 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))))[1:0]));
SF := t_209[64:63];
ZF := bool2bv(0bv64 == t_209);

label_0x4863:
if (bv2bool(ZF)) {
  goto label_0x4866;
}

label_0x4865:
assume false;

label_0x4866:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x486b:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_77);

label_0x486f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4876:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x487a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x487f:
origDEST_219 := RCX;
origCOUNT_220 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), CF, LSHIFT_64(origDEST_219, (MINUS_64(64bv64, origCOUNT_220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv64)), origDEST_219[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), AF, unconstrained_79);

label_0x4883:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_80;
SF := unconstrained_81;
AF := unconstrained_82;
PF := unconstrained_83;

label_0x4887:
if (bv2bool(CF)) {
  goto label_0x488a;
}

label_0x4889:
assume false;

label_0x488a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x488f:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x4895:
goto label_0x4ddf;

label_0x489a:
t_225 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_225)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_225, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)), 2bv32)), (XOR_32((RSHIFT_32(t_225, 4bv32)), t_225)))))[1:0]));
SF := t_225[32:31];
ZF := bool2bv(0bv32 == t_225);

label_0x48a2:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4966;
}

label_0x48a8:
t_229 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_229)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_229, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))))[1:0]));
SF := t_229[64:63];
ZF := bool2bv(0bv64 == t_229);

label_0x48b1:
if (bv2bool(ZF)) {
  goto label_0x4904;
}

label_0x48b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x48bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_84;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x48c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x48c6:
t_235 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_85;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)), 2bv64)), (XOR_64((RSHIFT_64(t_235, 4bv64)), t_235)))))[1:0]));
SF := t_235[64:63];
ZF := bool2bv(0bv64 == t_235);

label_0x48c9:
if (bv2bool(ZF)) {
  goto label_0x48cc;
}

label_0x48cb:
assume false;

label_0x48cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x48d4:
origDEST_239 := RAX;
origCOUNT_240 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_86));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_87);

label_0x48d8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x48df:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x48e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x48eb:
origDEST_245 := RCX;
origCOUNT_246 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), CF, LSHIFT_64(origDEST_245, (MINUS_64(64bv64, origCOUNT_246)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_246 == 1bv64)), origDEST_245[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_246 == 0bv64)), AF, unconstrained_89);

label_0x48ef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_90;
SF := unconstrained_91;
AF := unconstrained_92;
PF := unconstrained_93;

label_0x48f3:
if (bv2bool(CF)) {
  goto label_0x48f6;
}

label_0x48f5:
assume false;

label_0x48f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x48fe:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4904:
t_251 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_251)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_251, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))))[1:0]));
SF := t_251[64:63];
ZF := bool2bv(0bv64 == t_251);

label_0x490a:
if (bv2bool(ZF)) {
  goto label_0x4961;
}

label_0x490c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4911:
t1_255 := RAX;
t2_256 := 5096bv64;
RAX := PLUS_64(RAX, t2_256);
CF := bool2bv(LT_64(RAX, t1_255));
OF := AND_1((bool2bv((t1_255[64:63]) == (t2_256[64:63]))), (XOR_1((t1_255[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_255)), t2_256)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4917:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x491c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x4921:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_94;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4927:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x492c:
t_263 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_95;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)), 2bv64)), (XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)), 2bv64)), (XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)))))[1:0]));
SF := t_263[64:63];
ZF := bool2bv(0bv64 == t_263);

label_0x492f:
if (bv2bool(ZF)) {
  goto label_0x4932;
}

label_0x4931:
assume false;

label_0x4932:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x4937:
origDEST_267 := RAX;
origCOUNT_268 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), CF, LSHIFT_64(origDEST_267, (MINUS_64(64bv64, origCOUNT_268)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_268 == 1bv64)), origDEST_267[64:63], unconstrained_96));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_268 == 0bv64)), AF, unconstrained_97);

label_0x493b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4942:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4946:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x494b:
origDEST_273 := RCX;
origCOUNT_274 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), CF, LSHIFT_64(origDEST_273, (MINUS_64(64bv64, origCOUNT_274)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_274 == 1bv64)), origDEST_273[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_274 == 0bv64)), AF, unconstrained_99);

label_0x494f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_100;
SF := unconstrained_101;
AF := unconstrained_102;
PF := unconstrained_103;

label_0x4953:
if (bv2bool(CF)) {
  goto label_0x4956;
}

label_0x4955:
assume false;

label_0x4956:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x495b:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4961:
goto label_0x4ddf;

label_0x4966:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x496b:
t1_279 := RAX;
t2_280 := 5024bv64;
RAX := PLUS_64(RAX, t2_280);
CF := bool2bv(LT_64(RAX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4971:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x4976:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x497b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_104;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4981:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4986:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_105;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x4989:
if (bv2bool(ZF)) {
  goto label_0x498c;
}

label_0x498b:
assume false;

label_0x498c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x4991:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_106));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_107);

label_0x4995:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x499c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x49a0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x49a5:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_109);

label_0x49a9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_110;
SF := unconstrained_111;
AF := unconstrained_112;
PF := unconstrained_113;

label_0x49ad:
if (bv2bool(CF)) {
  goto label_0x49b0;
}

label_0x49af:
assume false;

label_0x49b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x49b5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x49bc:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x49be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x49c3:
t1_303 := RAX;
t2_304 := 5016bv64;
RAX := PLUS_64(RAX, t2_304);
CF := bool2bv(LT_64(RAX, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x49ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x49d3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_114;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x49d9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x49de:
t_311 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_115;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))))[1:0]));
SF := t_311[64:63];
ZF := bool2bv(0bv64 == t_311);

label_0x49e1:
if (bv2bool(ZF)) {
  goto label_0x49e4;
}

label_0x49e3:
assume false;

label_0x49e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x49e9:
origDEST_315 := RAX;
origCOUNT_316 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_116));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_117);

label_0x49ed:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x49f4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x49f8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x49fd:
origDEST_321 := RCX;
origCOUNT_322 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), CF, LSHIFT_64(origDEST_321, (MINUS_64(64bv64, origCOUNT_322)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_322 == 1bv64)), origDEST_321[64:63], unconstrained_118));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), AF, unconstrained_119);

label_0x4a01:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_120;
SF := unconstrained_121;
AF := unconstrained_122;
PF := unconstrained_123;

label_0x4a05:
if (bv2bool(CF)) {
  goto label_0x4a08;
}

label_0x4a07:
assume false;

label_0x4a08:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x4a0d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4a15:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x4a18:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_124;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4a1a:
t_327 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_327)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_327, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))))[1:0]));
SF := t_327[32:31];
ZF := bool2bv(0bv32 == t_327);

label_0x4a1d:
if (bv2bool(ZF)) {
  goto label_0x4ddf;
}

label_0x4a23:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4a28:
t1_331 := RAX;
t2_332 := 5048bv64;
RAX := PLUS_64(RAX, t2_332);
CF := bool2bv(LT_64(RAX, t1_331));
OF := AND_1((bool2bv((t1_331[64:63]) == (t2_332[64:63]))), (XOR_1((t1_331[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_331)), t2_332)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a2e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x4a33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x4a38:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_125;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a3e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4a43:
t_339 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)), 2bv64)), (XOR_64((RSHIFT_64(t_339, 4bv64)), t_339)))))[1:0]));
SF := t_339[64:63];
ZF := bool2bv(0bv64 == t_339);

label_0x4a46:
if (bv2bool(ZF)) {
  goto label_0x4a49;
}

label_0x4a48:
assume false;

label_0x4a49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x4a4e:
origDEST_343 := RAX;
origCOUNT_344 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), CF, LSHIFT_64(origDEST_343, (MINUS_64(64bv64, origCOUNT_344)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_344 == 1bv64)), origDEST_343[64:63], unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_344 == 0bv64)), AF, unconstrained_128);

label_0x4a52:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4a59:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4a5d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x4a62:
origDEST_349 := RCX;
origCOUNT_350 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, LSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), origDEST_349[64:63], unconstrained_129));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_130);

label_0x4a66:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_131;
SF := unconstrained_132;
AF := unconstrained_133;
PF := unconstrained_134;

label_0x4a6a:
if (bv2bool(CF)) {
  goto label_0x4a6d;
}

label_0x4a6c:
assume false;

label_0x4a6d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x4a72:
mem := STORE_LE_32(mem, RAX, 5000bv32);

label_0x4a78:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4a7d:
t1_355 := RAX;
t2_356 := 4bv64;
RAX := PLUS_64(RAX, t2_356);
CF := bool2bv(LT_64(RAX, t1_355));
OF := AND_1((bool2bv((t1_355[64:63]) == (t2_356[64:63]))), (XOR_1((t1_355[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_355)), t2_356)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a81:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x4a89:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4a8e:
t1_361 := RAX;
t2_362 := 5040bv64;
RAX := PLUS_64(RAX, t2_362);
CF := bool2bv(LT_64(RAX, t1_361));
OF := AND_1((bool2bv((t1_361[64:63]) == (t2_362[64:63]))), (XOR_1((t1_361[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_361)), t2_362)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4a94:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x4a99:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4a9e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_135;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4aa4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4aa9:
t_369 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)), 2bv64)), (XOR_64((RSHIFT_64(t_369, 4bv64)), t_369)))))[1:0]));
SF := t_369[64:63];
ZF := bool2bv(0bv64 == t_369);

label_0x4aac:
if (bv2bool(ZF)) {
  goto label_0x4aaf;
}

label_0x4aae:
assume false;

label_0x4aaf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4ab4:
origDEST_373 := RAX;
origCOUNT_374 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), CF, LSHIFT_64(origDEST_373, (MINUS_64(64bv64, origCOUNT_374)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_374 == 1bv64)), origDEST_373[64:63], unconstrained_137));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), AF, unconstrained_138);

label_0x4ab8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4abf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ac3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4ac8:
origDEST_379 := RCX;
origCOUNT_380 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), CF, LSHIFT_64(origDEST_379, (MINUS_64(64bv64, origCOUNT_380)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_380 == 1bv64)), origDEST_379[64:63], unconstrained_139));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_380 == 0bv64)), AF, unconstrained_140);

label_0x4acc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_141;
SF := unconstrained_142;
AF := unconstrained_143;
PF := unconstrained_144;

label_0x4ad0:
if (bv2bool(CF)) {
  goto label_0x4ad3;
}

label_0x4ad2:
assume false;

label_0x4ad3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4ad8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x4ae0:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x4ae3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4ae8:
t1_385 := RAX;
t2_386 := 5016bv64;
RAX := PLUS_64(RAX, t2_386);
CF := bool2bv(LT_64(RAX, t1_385));
OF := AND_1((bool2bv((t1_385[64:63]) == (t2_386[64:63]))), (XOR_1((t1_385[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_385)), t2_386)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4aee:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_145;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4af0:
RCX := RAX;

label_0x4af3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 19192bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4af8"} true;
call arbitrary_func();

label_0x4af8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x4afc:
t_391 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_391)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_391, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_391, 4bv32)), t_391)), 2bv32)), (XOR_32((RSHIFT_32(t_391, 4bv32)), t_391)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_391, 4bv32)), t_391)), 2bv32)), (XOR_32((RSHIFT_32(t_391, 4bv32)), t_391)))))[1:0]));
SF := t_391[32:31];
ZF := bool2bv(0bv32 == t_391);

label_0x4b01:
if (bv2bool(ZF)) {
  goto label_0x4bc5;
}

label_0x4b07:
t_395 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_395)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_395, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)), 2bv64)), (XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)), 2bv64)), (XOR_64((RSHIFT_64(t_395, 4bv64)), t_395)))))[1:0]));
SF := t_395[64:63];
ZF := bool2bv(0bv64 == t_395);

label_0x4b10:
if (bv2bool(ZF)) {
  goto label_0x4b63;
}

label_0x4b12:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4b1a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4b20:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4b25:
t_401 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))))[1:0]));
SF := t_401[64:63];
ZF := bool2bv(0bv64 == t_401);

label_0x4b28:
if (bv2bool(ZF)) {
  goto label_0x4b2b;
}

label_0x4b2a:
assume false;

label_0x4b2b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4b33:
origDEST_405 := RAX;
origCOUNT_406 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), CF, LSHIFT_64(origDEST_405, (MINUS_64(64bv64, origCOUNT_406)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_406 == 1bv64)), origDEST_405[64:63], unconstrained_148));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), AF, unconstrained_149);

label_0x4b37:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4b3e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4b42:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4b4a:
origDEST_411 := RCX;
origCOUNT_412 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), CF, LSHIFT_64(origDEST_411, (MINUS_64(64bv64, origCOUNT_412)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_412 == 1bv64)), origDEST_411[64:63], unconstrained_150));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), AF, unconstrained_151);

label_0x4b4e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_152;
SF := unconstrained_153;
AF := unconstrained_154;
PF := unconstrained_155;

label_0x4b52:
if (bv2bool(CF)) {
  goto label_0x4b55;
}

label_0x4b54:
assume false;

label_0x4b55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4b5d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x4b61:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4b63:
t_417 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_417)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_417, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)), 2bv64)), (XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)), 2bv64)), (XOR_64((RSHIFT_64(t_417, 4bv64)), t_417)))))[1:0]));
SF := t_417[64:63];
ZF := bool2bv(0bv64 == t_417);

label_0x4b69:
if (bv2bool(ZF)) {
  goto label_0x4bc0;
}

label_0x4b6b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4b70:
t1_421 := RAX;
t2_422 := 5096bv64;
RAX := PLUS_64(RAX, t2_422);
CF := bool2bv(LT_64(RAX, t1_421));
OF := AND_1((bool2bv((t1_421[64:63]) == (t2_422[64:63]))), (XOR_1((t1_421[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_421)), t2_422)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4b76:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x4b7b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4b80:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4b86:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4b8b:
t_429 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)), 2bv64)), (XOR_64((RSHIFT_64(t_429, 4bv64)), t_429)))))[1:0]));
SF := t_429[64:63];
ZF := bool2bv(0bv64 == t_429);

label_0x4b8e:
if (bv2bool(ZF)) {
  goto label_0x4b91;
}

label_0x4b90:
assume false;

label_0x4b91:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4b96:
origDEST_433 := RAX;
origCOUNT_434 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), CF, LSHIFT_64(origDEST_433, (MINUS_64(64bv64, origCOUNT_434)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_434 == 1bv64)), origDEST_433[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_434 == 0bv64)), AF, unconstrained_159);

label_0x4b9a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4ba1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ba5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4baa:
origDEST_439 := RCX;
origCOUNT_440 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), CF, LSHIFT_64(origDEST_439, (MINUS_64(64bv64, origCOUNT_440)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_440 == 1bv64)), origDEST_439[64:63], unconstrained_160));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_440 == 0bv64)), AF, unconstrained_161);

label_0x4bae:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_162;
SF := unconstrained_163;
AF := unconstrained_164;
PF := unconstrained_165;

label_0x4bb2:
if (bv2bool(CF)) {
  goto label_0x4bb5;
}

label_0x4bb4:
assume false;

label_0x4bb5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4bba:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x4bbe:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4bc0:
goto label_0x4ddf;

label_0x4bc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4bca:
t_445 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), 5000bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))), t_445)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_445, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), 5000bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_445, 4bv32)), t_445)), 2bv32)), (XOR_32((RSHIFT_32(t_445, 4bv32)), t_445)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_445, 4bv32)), t_445)), 2bv32)), (XOR_32((RSHIFT_32(t_445, 4bv32)), t_445)))))[1:0]));
SF := t_445[32:31];
ZF := bool2bv(0bv32 == t_445);

label_0x4bd4:
if (bv2bool(NOT_1(CF))) {
  goto label_0x4cfe;
}

label_0x4bda:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4bdf:
RCX := (0bv32 ++ 5000bv32);

label_0x4be4:
t_449 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64)))));
CF := bool2bv(LT_32(t_449, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64)))));
OF := AND_32((XOR_32(t_449, (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))), (XOR_32(t_449, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_449)), (LOAD_LE_32(mem, PLUS_64(RAX, 5048bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4bea:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4bec:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x4bf0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4bf5:
t1_453 := RAX;
t2_454 := 4bv64;
RAX := PLUS_64(RAX, t2_454);
CF := bool2bv(LT_64(RAX, t1_453));
OF := AND_1((bool2bv((t1_453[64:63]) == (t2_454[64:63]))), (XOR_1((t1_453[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_453)), t2_454)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4bf9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4bfe:
R9 := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x4c01:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x4c06:
RDX := (0bv32 ++ 1bv32);

label_0x4c0b:
RCX := RAX;

label_0x4c0e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 19475bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4c13"} true;
call arbitrary_func();

label_0x4c13:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x4c1a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x4c21:
t_459 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_459)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_459, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_459, 4bv32)), t_459)), 2bv32)), (XOR_32((RSHIFT_32(t_459, 4bv32)), t_459)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_459, 4bv32)), t_459)), 2bv32)), (XOR_32((RSHIFT_32(t_459, 4bv32)), t_459)))))[1:0]));
SF := t_459[32:31];
ZF := bool2bv(0bv32 == t_459);

label_0x4c25:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4c31;
}

label_0x4c27:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_166;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4c29:
t_463 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)), 2bv32)), (XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)), 2bv32)), (XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)))))[1:0]));
SF := t_463[32:31];
ZF := bool2bv(0bv32 == t_463);

label_0x4c2b:
if (bv2bool(ZF)) {
  goto label_0x4cfe;
}

label_0x4c31:
t_467 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_467)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_467, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))))[1:0]));
SF := t_467[64:63];
ZF := bool2bv(0bv64 == t_467);

label_0x4c3a:
if (bv2bool(ZF)) {
  goto label_0x4c8d;
}

label_0x4c3c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4c44:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_168;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4c4a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4c4f:
t_473 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_169;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))))[1:0]));
SF := t_473[64:63];
ZF := bool2bv(0bv64 == t_473);

label_0x4c52:
if (bv2bool(ZF)) {
  goto label_0x4c55;
}

label_0x4c54:
assume false;

label_0x4c55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4c5d:
origDEST_477 := RAX;
origCOUNT_478 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), CF, LSHIFT_64(origDEST_477, (MINUS_64(64bv64, origCOUNT_478)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_478 == 1bv64)), origDEST_477[64:63], unconstrained_170));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), AF, unconstrained_171);

label_0x4c61:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4c68:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4c6c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4c74:
origDEST_483 := RCX;
origCOUNT_484 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), CF, LSHIFT_64(origDEST_483, (MINUS_64(64bv64, origCOUNT_484)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_484 == 1bv64)), origDEST_483[64:63], unconstrained_172));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), AF, unconstrained_173);

label_0x4c78:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_174;
SF := unconstrained_175;
AF := unconstrained_176;
PF := unconstrained_177;

label_0x4c7c:
if (bv2bool(CF)) {
  goto label_0x4c7f;
}

label_0x4c7e:
assume false;

label_0x4c7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4c87:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x4c8d:
t_489 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_489)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_489, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))))[1:0]));
SF := t_489[64:63];
ZF := bool2bv(0bv64 == t_489);

label_0x4c93:
if (bv2bool(ZF)) {
  goto label_0x4cf9;
}

label_0x4c95:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4c9a:
t1_493 := RAX;
t2_494 := 5096bv64;
RAX := PLUS_64(RAX, t2_494);
CF := bool2bv(LT_64(RAX, t1_493));
OF := AND_1((bool2bv((t1_493[64:63]) == (t2_494[64:63]))), (XOR_1((t1_493[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_493)), t2_494)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4ca0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x4ca8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4cb0:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_178;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4cb6:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4cbb:
t_501 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_179;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))))[1:0]));
SF := t_501[64:63];
ZF := bool2bv(0bv64 == t_501);

label_0x4cbe:
if (bv2bool(ZF)) {
  goto label_0x4cc1;
}

label_0x4cc0:
assume false;

label_0x4cc1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4cc9:
origDEST_505 := RAX;
origCOUNT_506 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), CF, LSHIFT_64(origDEST_505, (MINUS_64(64bv64, origCOUNT_506)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_506 == 1bv64)), origDEST_505[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), AF, unconstrained_181);

label_0x4ccd:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4cd4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4cd8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4ce0:
origDEST_511 := RCX;
origCOUNT_512 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), CF, LSHIFT_64(origDEST_511, (MINUS_64(64bv64, origCOUNT_512)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_512 == 1bv64)), origDEST_511[64:63], unconstrained_182));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), AF, unconstrained_183);

label_0x4ce4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_184;
SF := unconstrained_185;
AF := unconstrained_186;
PF := unconstrained_187;

label_0x4ce8:
if (bv2bool(CF)) {
  goto label_0x4ceb;
}

label_0x4cea:
assume false;

label_0x4ceb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4cf3:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x4cf9:
goto label_0x4ddf;

label_0x4cfe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4d03:
t_517 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))), t_517)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_517, (LOAD_LE_32(mem, PLUS_64(RAX, 5024bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_517, 4bv32)), t_517)), 2bv32)), (XOR_32((RSHIFT_32(t_517, 4bv32)), t_517)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_517, 4bv32)), t_517)), 2bv32)), (XOR_32((RSHIFT_32(t_517, 4bv32)), t_517)))))[1:0]));
SF := t_517[32:31];
ZF := bool2bv(0bv32 == t_517);

label_0x4d0a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4dda;
}

label_0x4d10:
t_521 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))), t_521)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_521, (LOAD_LE_64(mem, PLUS_64(RSP, 176bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_521, 4bv64)), t_521)), 2bv64)), (XOR_64((RSHIFT_64(t_521, 4bv64)), t_521)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_521, 4bv64)), t_521)), 2bv64)), (XOR_64((RSHIFT_64(t_521, 4bv64)), t_521)))))[1:0]));
SF := t_521[64:63];
ZF := bool2bv(0bv64 == t_521);

label_0x4d19:
if (bv2bool(ZF)) {
  goto label_0x4d6c;
}

label_0x4d1b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4d23:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_188;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d29:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4d2e:
t_527 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_189;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)), 2bv64)), (XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)), 2bv64)), (XOR_64((RSHIFT_64(t_527, 4bv64)), t_527)))))[1:0]));
SF := t_527[64:63];
ZF := bool2bv(0bv64 == t_527);

label_0x4d31:
if (bv2bool(ZF)) {
  goto label_0x4d34;
}

label_0x4d33:
assume false;

label_0x4d34:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4d3c:
origDEST_531 := RAX;
origCOUNT_532 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), CF, LSHIFT_64(origDEST_531, (MINUS_64(64bv64, origCOUNT_532)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_532 == 1bv64)), origDEST_531[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_532 == 0bv64)), AF, unconstrained_191);

label_0x4d40:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4d47:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4d4b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4d53:
origDEST_537 := RCX;
origCOUNT_538 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), CF, LSHIFT_64(origDEST_537, (MINUS_64(64bv64, origCOUNT_538)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_538 == 1bv64)), origDEST_537[64:63], unconstrained_192));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_538 == 0bv64)), AF, unconstrained_193);

label_0x4d57:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_194;
SF := unconstrained_195;
AF := unconstrained_196;
PF := unconstrained_197;

label_0x4d5b:
if (bv2bool(CF)) {
  goto label_0x4d5e;
}

label_0x4d5d:
assume false;

label_0x4d5e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x4d66:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4d6c:
t_543 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_543)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_543, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_543, 4bv64)), t_543)), 2bv64)), (XOR_64((RSHIFT_64(t_543, 4bv64)), t_543)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_543, 4bv64)), t_543)), 2bv64)), (XOR_64((RSHIFT_64(t_543, 4bv64)), t_543)))))[1:0]));
SF := t_543[64:63];
ZF := bool2bv(0bv64 == t_543);

label_0x4d72:
if (bv2bool(ZF)) {
  goto label_0x4dd8;
}

label_0x4d74:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4d79:
t1_547 := RAX;
t2_548 := 5096bv64;
RAX := PLUS_64(RAX, t2_548);
CF := bool2bv(LT_64(RAX, t1_547));
OF := AND_1((bool2bv((t1_547[64:63]) == (t2_548[64:63]))), (XOR_1((t1_547[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_547)), t2_548)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x4d87:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4d8f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_198;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4d95:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4d9a:
t_555 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_199;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_555, 4bv64)), t_555)), 2bv64)), (XOR_64((RSHIFT_64(t_555, 4bv64)), t_555)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_555, 4bv64)), t_555)), 2bv64)), (XOR_64((RSHIFT_64(t_555, 4bv64)), t_555)))))[1:0]));
SF := t_555[64:63];
ZF := bool2bv(0bv64 == t_555);

label_0x4d9d:
if (bv2bool(ZF)) {
  goto label_0x4da0;
}

label_0x4d9f:
assume false;

label_0x4da0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4da8:
origDEST_559 := RAX;
origCOUNT_560 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), CF, LSHIFT_64(origDEST_559, (MINUS_64(64bv64, origCOUNT_560)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_560 == 1bv64)), origDEST_559[64:63], unconstrained_200));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), AF, unconstrained_201);

label_0x4dac:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4db3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4db7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4dbf:
origDEST_565 := RCX;
origCOUNT_566 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), CF, LSHIFT_64(origDEST_565, (MINUS_64(64bv64, origCOUNT_566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_566 == 1bv64)), origDEST_565[64:63], unconstrained_202));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), AF, unconstrained_203);

label_0x4dc3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_204;
SF := unconstrained_205;
AF := unconstrained_206;
PF := unconstrained_207;

label_0x4dc7:
if (bv2bool(CF)) {
  goto label_0x4dca;
}

label_0x4dc9:
assume false;

label_0x4dca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4dd2:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4dd8:
goto label_0x4ddf;

label_0x4dda:
goto label_0x4a18;

label_0x4ddf:
t1_571 := RSP;
t2_572 := 168bv64;
RSP := PLUS_64(RSP, t2_572);
CF := bool2bv(LT_64(RSP, t1_571));
OF := AND_1((bool2bv((t1_571[64:63]) == (t2_572[64:63]))), (XOR_1((t1_571[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_571)), t2_572)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4de6:

ra_577 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_132,origCOUNT_138,origCOUNT_16,origCOUNT_160,origCOUNT_166,origCOUNT_186,origCOUNT_192,origCOUNT_214,origCOUNT_22,origCOUNT_220,origCOUNT_240,origCOUNT_246,origCOUNT_268,origCOUNT_274,origCOUNT_292,origCOUNT_298,origCOUNT_316,origCOUNT_322,origCOUNT_344,origCOUNT_350,origCOUNT_374,origCOUNT_380,origCOUNT_406,origCOUNT_412,origCOUNT_434,origCOUNT_44,origCOUNT_440,origCOUNT_478,origCOUNT_484,origCOUNT_50,origCOUNT_506,origCOUNT_512,origCOUNT_532,origCOUNT_538,origCOUNT_560,origCOUNT_566,origCOUNT_78,origCOUNT_84,origDEST_105,origDEST_111,origDEST_131,origDEST_137,origDEST_15,origDEST_159,origDEST_165,origDEST_185,origDEST_191,origDEST_21,origDEST_213,origDEST_219,origDEST_239,origDEST_245,origDEST_267,origDEST_273,origDEST_291,origDEST_297,origDEST_315,origDEST_321,origDEST_343,origDEST_349,origDEST_373,origDEST_379,origDEST_405,origDEST_411,origDEST_43,origDEST_433,origDEST_439,origDEST_477,origDEST_483,origDEST_49,origDEST_505,origDEST_511,origDEST_531,origDEST_537,origDEST_559,origDEST_565,origDEST_77,origDEST_83,ra_577,t1_147,t1_201,t1_255,t1_279,t1_303,t1_31,t1_331,t1_355,t1_361,t1_385,t1_421,t1_453,t1_493,t1_547,t1_571,t1_93,t2_148,t2_202,t2_256,t2_280,t2_304,t2_32,t2_332,t2_356,t2_362,t2_386,t2_422,t2_454,t2_494,t2_548,t2_572,t2_94,t_1,t_101,t_11,t_117,t_121,t_127,t_143,t_155,t_171,t_175,t_181,t_197,t_209,t_225,t_229,t_235,t_251,t_263,t_27,t_287,t_311,t_327,t_339,t_369,t_39,t_391,t_395,t_401,t_417,t_429,t_445,t_449,t_459,t_463,t_467,t_473,t_489,t_5,t_501,t_517,t_521,t_527,t_543,t_55,t_555,t_59,t_63,t_67,t_73,t_89;

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
var origCOUNT_240: bv64;
var origCOUNT_246: bv64;
var origCOUNT_268: bv64;
var origCOUNT_274: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_316: bv64;
var origCOUNT_322: bv64;
var origCOUNT_344: bv64;
var origCOUNT_350: bv64;
var origCOUNT_374: bv64;
var origCOUNT_380: bv64;
var origCOUNT_406: bv64;
var origCOUNT_412: bv64;
var origCOUNT_434: bv64;
var origCOUNT_44: bv64;
var origCOUNT_440: bv64;
var origCOUNT_478: bv64;
var origCOUNT_484: bv64;
var origCOUNT_50: bv64;
var origCOUNT_506: bv64;
var origCOUNT_512: bv64;
var origCOUNT_532: bv64;
var origCOUNT_538: bv64;
var origCOUNT_560: bv64;
var origCOUNT_566: bv64;
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
var origDEST_239: bv64;
var origDEST_245: bv64;
var origDEST_267: bv64;
var origDEST_273: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_315: bv64;
var origDEST_321: bv64;
var origDEST_343: bv64;
var origDEST_349: bv64;
var origDEST_373: bv64;
var origDEST_379: bv64;
var origDEST_405: bv64;
var origDEST_411: bv64;
var origDEST_43: bv64;
var origDEST_433: bv64;
var origDEST_439: bv64;
var origDEST_477: bv64;
var origDEST_483: bv64;
var origDEST_49: bv64;
var origDEST_505: bv64;
var origDEST_511: bv64;
var origDEST_531: bv64;
var origDEST_537: bv64;
var origDEST_559: bv64;
var origDEST_565: bv64;
var origDEST_77: bv64;
var origDEST_83: bv64;
var ra_577: bv64;
var t1_147: bv64;
var t1_201: bv64;
var t1_255: bv64;
var t1_279: bv64;
var t1_303: bv64;
var t1_31: bv64;
var t1_331: bv64;
var t1_355: bv64;
var t1_361: bv64;
var t1_385: bv64;
var t1_421: bv64;
var t1_453: bv64;
var t1_493: bv64;
var t1_547: bv64;
var t1_571: bv64;
var t1_93: bv64;
var t2_148: bv64;
var t2_202: bv64;
var t2_256: bv64;
var t2_280: bv64;
var t2_304: bv64;
var t2_32: bv64;
var t2_332: bv64;
var t2_356: bv64;
var t2_362: bv64;
var t2_386: bv64;
var t2_422: bv64;
var t2_454: bv64;
var t2_494: bv64;
var t2_548: bv64;
var t2_572: bv64;
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
var t_225: bv32;
var t_229: bv64;
var t_235: bv64;
var t_251: bv64;
var t_263: bv64;
var t_27: bv64;
var t_287: bv64;
var t_311: bv64;
var t_327: bv32;
var t_339: bv64;
var t_369: bv64;
var t_39: bv64;
var t_391: bv32;
var t_395: bv64;
var t_401: bv64;
var t_417: bv64;
var t_429: bv64;
var t_445: bv32;
var t_449: bv32;
var t_459: bv32;
var t_463: bv32;
var t_467: bv64;
var t_473: bv64;
var t_489: bv64;
var t_5: bv64;
var t_501: bv64;
var t_517: bv32;
var t_521: bv64;
var t_527: bv64;
var t_543: bv64;
var t_55: bv64;
var t_555: bv64;
var t_59: bv64;
var t_63: bv32;
var t_67: bv64;
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
