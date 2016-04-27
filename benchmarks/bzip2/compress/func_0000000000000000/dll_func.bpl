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
axiom _function_addr_low == 0bv64;
axiom _function_addr_high == 1264bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0:
mem := STORE_LE_8(mem, PLUS_64(RSP, 16bv64), RDX[32:0][8:0]);

label_0x4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x9:
t_1 := RSP;
RSP := MINUS_64(RSP, 120bv64);
CF := bool2bv(LT_64(t_1, 120bv64));
OF := AND_64((XOR_64(t_1, 120bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 120bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x15:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x19:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x261;
}

label_0x1f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x27:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 648bv64)));

label_0x2d:
RAX := (0bv32 ++ NOT_32((RAX[32:0])));

label_0x2f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 88bv64), RAX[32:0]);

label_0x33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3b:
t1_9 := RAX;
t2_10 := 648bv64;
RAX := PLUS_64(RAX, t2_10);
CF := bool2bv(LT_64(RAX, t1_9));
OF := AND_1((bool2bv((t1_9[64:63]) == (t2_10[64:63]))), (XOR_1((t1_9[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_9)), t2_10)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x46:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x51:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x56:
t_17 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))))[1:0]));
SF := t_17[64:63];
ZF := bool2bv(0bv64 == t_17);

label_0x59:
if (bv2bool(ZF)) {
  goto label_0x5c;
}

label_0x5b:
assume false;

label_0x5c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x61:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_4);

label_0x65:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x6c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x70:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x75:
origDEST_27 := RCX;
origCOUNT_28 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), CF, LSHIFT_64(origDEST_27, (MINUS_64(64bv64, origCOUNT_28)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_28 == 1bv64)), origDEST_27[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), AF, unconstrained_6);

label_0x79:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x7d:
if (bv2bool(CF)) {
  goto label_0x80;
}

label_0x7f:
assume false;

label_0x80:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x85:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 88bv64)));

label_0x89:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x93:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 652bv64)));

label_0x99:
origDEST_33 := RAX[32:0];
origCOUNT_34 := AND_32(1bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(1bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), CF, RSHIFT_32(origDEST_33, (MINUS_32(32bv32, origCOUNT_34)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv32)), AF, unconstrained_12);

label_0x9b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xa3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 652bv64)));

label_0xa9:
origDEST_39 := RCX[32:0];
origCOUNT_40 := AND_32(31bv32, (MINUS_32(32bv32, 1bv32)));
RCX := (0bv32 ++ RSHIFT_32((RCX[32:0]), (AND_32(31bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), CF, LSHIFT_32(origDEST_39, (MINUS_32(32bv32, origCOUNT_40)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv32)), origDEST_39[32:31], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), SF, RCX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), ZF, bool2bv(0bv32 == (RCX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), AF, unconstrained_14);

label_0xac:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xae:
mem := STORE_LE_32(mem, PLUS_64(RSP, 92bv64), RAX[32:0]);

label_0xb2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0xba:
t1_47 := RAX;
t2_48 := 652bv64;
RAX := PLUS_64(RAX, t2_48);
CF := bool2bv(LT_64(RAX, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xc0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0xc5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xca:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd5:
t_55 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)), 2bv64)), (XOR_64((RSHIFT_64(t_55, 4bv64)), t_55)))))[1:0]));
SF := t_55[64:63];
ZF := bool2bv(0bv64 == t_55);

label_0xd8:
if (bv2bool(ZF)) {
  goto label_0xdb;
}

label_0xda:
assume false;

label_0xdb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xe0:
origDEST_59 := RAX;
origCOUNT_60 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_19);

label_0xe4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xeb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xf4:
origDEST_65 := RCX;
origCOUNT_66 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_21);

label_0xf8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_22;
SF := unconstrained_23;
AF := unconstrained_24;
PF := unconstrained_25;

label_0xfc:
if (bv2bool(CF)) {
  goto label_0xff;
}

label_0xfe:
assume false;

label_0xff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x104:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 92bv64)));

label_0x108:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x10a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x112:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x11a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 648bv64)));

label_0x120:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 652bv64)));

label_0x126:
RAX := (0bv32 ++ XOR_32((RAX[32:0]), (RCX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x128:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0x12c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x134:
t1_73 := RAX;
t2_74 := 652bv64;
RAX := PLUS_64(RAX, t2_74);
CF := bool2bv(LT_64(RAX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x13f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x144:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x14f:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0x152:
if (bv2bool(ZF)) {
  goto label_0x155;
}

label_0x154:
assume false;

label_0x155:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15a:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_30);

label_0x15e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x165:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x169:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x16e:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_32);

label_0x172:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x176:
if (bv2bool(CF)) {
  goto label_0x179;
}

label_0x178:
assume false;

label_0x179:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x17e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x182:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x184:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x18c:
t_97 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), t_97)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_97, (LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))))[1:0]));
SF := t_97[32:31];
ZF := bool2bv(0bv32 == t_97);

label_0x193:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1eb;
}

label_0x195:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x19d:
t1_101 := RAX;
t2_102 := 116bv64;
RAX := PLUS_64(RAX, t2_102);
CF := bool2bv(LT_64(RAX, t1_101));
OF := AND_1((bool2bv((t1_101[64:63]) == (t2_102[64:63]))), (XOR_1((t1_101[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_101)), t2_102)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1a1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x1a6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1ab:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1b6:
t_109 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_38;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))))[1:0]));
SF := t_109[64:63];
ZF := bool2bv(0bv64 == t_109);

label_0x1b9:
if (bv2bool(ZF)) {
  goto label_0x1bc;
}

label_0x1bb:
assume false;

label_0x1bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1c1:
origDEST_113 := RAX;
origCOUNT_114 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_40);

label_0x1c5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1cc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1d0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1d5:
origDEST_119 := RCX;
origCOUNT_120 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), CF, LSHIFT_64(origDEST_119, (MINUS_64(64bv64, origCOUNT_120)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_120 == 1bv64)), origDEST_119[64:63], unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), AF, unconstrained_42);

label_0x1d9:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_43;
SF := unconstrained_44;
AF := unconstrained_45;
PF := unconstrained_46;

label_0x1dd:
if (bv2bool(CF)) {
  goto label_0x1e0;
}

label_0x1df:
assume false;

label_0x1e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1e5:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x1eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x1f3:
t_125 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), t_125)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_125, (LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))))[1:0]));
SF := t_125[32:31];
ZF := bool2bv(0bv32 == t_125);

label_0x1fa:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x254;
}

label_0x1fc:
RCX := (0bv32 ++ 2bv32);

label_0x201:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 518bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x206"} true;
call arbitrary_func();

label_0x206:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x20e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 108bv64)));

label_0x211:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RCX[32:0]);

label_0x215:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x21d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 652bv64)));

label_0x223:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RCX[32:0]);

label_0x227:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x22f:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 648bv64)));

label_0x236:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x23e:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 660bv64)));

label_0x245:
RDX := PLUS_64((PLUS_64(0bv64, 588bv64)), 0bv64)[64:0];

label_0x24c:
RCX := RAX;

label_0x24f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 596bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x254"} true;
call arbitrary_func();

label_0x254:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x25c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 609bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x261"} true;
call arbitrary_func();

label_0x261:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x269:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 108bv64)))));

label_0x26d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x275:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 32bv64));

label_0x279:
t1_129 := RCX;
t2_130 := RAX;
RCX := PLUS_64(RCX, t2_130);
CF := bool2bv(LT_64(RCX, t1_129));
OF := AND_1((bool2bv((t1_129[64:63]) == (t2_130[64:63]))), (XOR_1((t1_129[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_129)), t2_130)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x27c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RCX);

label_0x281:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x289:
t1_135 := RAX;
t2_136 := 80bv64;
RAX := PLUS_64(RAX, t2_136);
CF := bool2bv(LT_64(RAX, t1_135));
OF := AND_1((bool2bv((t1_135[64:63]) == (t2_136[64:63]))), (XOR_1((t1_135[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_135)), t2_136)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x28d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x292:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x297:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2a2:
t_143 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x2a5:
if (bv2bool(ZF)) {
  goto label_0x2a8;
}

label_0x2a7:
assume false;

label_0x2a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2ad:
origDEST_147 := RAX;
origCOUNT_148 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), CF, LSHIFT_64(origDEST_147, (MINUS_64(64bv64, origCOUNT_148)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_148 == 1bv64)), origDEST_147[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), AF, unconstrained_50);

label_0x2b1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2b8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2bc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2c1:
origDEST_153 := RCX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_52);

label_0x2c5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x2c9:
if (bv2bool(CF)) {
  goto label_0x2cc;
}

label_0x2cb:
assume false;

label_0x2cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2d1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2d6:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2e1:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RAX, 660bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x2e8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x345;
}

label_0x2ea:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2f2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 759bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2f7"} true;
call arbitrary_func();

label_0x2f7:
RDX := (RDX[64:8]) ++ 66bv8;

label_0x2f9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x301:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 774bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x306"} true;
call arbitrary_func();

label_0x306:
RDX := (RDX[64:8]) ++ 90bv8;

label_0x308:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x310:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 789bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x315"} true;
call arbitrary_func();

label_0x315:
RDX := (RDX[64:8]) ++ 104bv8;

label_0x317:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x31f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 804bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x324"} true;
call arbitrary_func();

label_0x324:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x32c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 664bv64)));

label_0x332:
t1_163 := RAX[32:0];
t2_164 := 48bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_164));
CF := bool2bv(LT_32((RAX[32:0]), t1_163));
OF := AND_1((bool2bv((t1_163[32:31]) == (t2_164[32:31]))), (XOR_1((t1_163[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_163)), t2_164)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x335:
RDX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x338:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x340:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 837bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x345"} true;
call arbitrary_func();

label_0x345:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x34d:
t_169 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))), t_169)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_169, (LOAD_LE_32(mem, PLUS_64(RAX, 108bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))))[1:0]));
SF := t_169[32:31];
ZF := bool2bv(0bv32 == t_169);

label_0x351:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x419;
}

label_0x357:
RDX := (RDX[64:8]) ++ 49bv8;

label_0x359:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x361:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 870bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x366"} true;
call arbitrary_func();

label_0x366:
RDX := (RDX[64:8]) ++ 65bv8;

label_0x368:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x370:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 885bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x375"} true;
call arbitrary_func();

label_0x375:
RDX := (RDX[64:8]) ++ 89bv8;

label_0x377:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x37f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 900bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x384"} true;
call arbitrary_func();

label_0x384:
RDX := (RDX[64:8]) ++ 38bv8;

label_0x386:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x38e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 915bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x393"} true;
call arbitrary_func();

label_0x393:
RDX := (RDX[64:8]) ++ 83bv8;

label_0x395:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x39d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 930bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3a2"} true;
call arbitrary_func();

label_0x3a2:
RDX := (RDX[64:8]) ++ 89bv8;

label_0x3a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3ac:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 945bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3b1"} true;
call arbitrary_func();

label_0x3b1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3b9:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 648bv64)));

label_0x3bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3c7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 972bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3cc"} true;
call arbitrary_func();

label_0x3cc:
R8 := (0bv32 ++ 0bv32);
AF := unconstrained_57;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3cf:
RDX := (0bv32 ++ 1bv32);

label_0x3d4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3dc:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 993bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3e1"} true;
call arbitrary_func();

label_0x3e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3e9:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 48bv64)));

label_0x3ed:
RDX := (0bv32 ++ 24bv32);

label_0x3f2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3fa:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1023bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3ff"} true;
call arbitrary_func();

label_0x3ff:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x407:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1036bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x40c"} true;
call arbitrary_func();

label_0x40c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x414:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1049bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x419"} true;
call arbitrary_func();

label_0x419:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 136bv64))));

label_0x421:
t_173 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))))[1:0]));
SF := t_173[32:31];
ZF := bool2bv(0bv32 == t_173);

label_0x423:
if (bv2bool(ZF)) {
  goto label_0x4e4;
}

label_0x429:
RDX := (RDX[64:8]) ++ 23bv8;

label_0x42b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x433:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1080bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x438"} true;
call arbitrary_func();

label_0x438:
RDX := (RDX[64:8]) ++ 114bv8;

label_0x43a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x442:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1095bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x447"} true;
call arbitrary_func();

label_0x447:
RDX := (RDX[64:8]) ++ 69bv8;

label_0x449:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x451:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1110bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x456"} true;
call arbitrary_func();

label_0x456:
RDX := (RDX[64:8]) ++ 56bv8;

label_0x458:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x460:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1125bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x465"} true;
call arbitrary_func();

label_0x465:
RDX := (RDX[64:8]) ++ 80bv8;

label_0x467:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x46f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1140bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x474"} true;
call arbitrary_func();

label_0x474:
RDX := (RDX[64:8]) ++ 144bv8;

label_0x476:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x47e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1155bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x483"} true;
call arbitrary_func();

label_0x483:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x48b:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 652bv64)));

label_0x491:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x499:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1182bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x49e"} true;
call arbitrary_func();

label_0x49e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4a6:
t_177 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))), t_177)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_177, (LOAD_LE_32(mem, PLUS_64(RAX, 656bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))))[1:0]));
SF := t_177[32:31];
ZF := bool2bv(0bv32 == t_177);

label_0x4ad:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x4d7;
}

label_0x4af:
RCX := (0bv32 ++ 2bv32);

label_0x4b4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1209bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4b9"} true;
call arbitrary_func();

label_0x4b9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4c1:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 652bv64)));

label_0x4c8:
RDX := PLUS_64((PLUS_64(0bv64, 1231bv64)), 0bv64)[64:0];

label_0x4cf:
RCX := RAX;

label_0x4d2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1239bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4d7"} true;
call arbitrary_func();

label_0x4d7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4df:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1252bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4e4"} true;
call arbitrary_func();

label_0x4e4:
t1_181 := RSP;
t2_182 := 120bv64;
RSP := PLUS_64(RSP, t2_182);
CF := bool2bv(LT_64(RSP, t1_181));
OF := AND_1((bool2bv((t1_181[64:63]) == (t2_182[64:63]))), (XOR_1((t1_181[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_181)), t2_182)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4e8:

ra_187 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_114,origCOUNT_120,origCOUNT_148,origCOUNT_154,origCOUNT_22,origCOUNT_28,origCOUNT_34,origCOUNT_40,origCOUNT_60,origCOUNT_66,origCOUNT_86,origCOUNT_92,origDEST_113,origDEST_119,origDEST_147,origDEST_153,origDEST_21,origDEST_27,origDEST_33,origDEST_39,origDEST_59,origDEST_65,origDEST_85,origDEST_91,ra_187,t1_101,t1_129,t1_135,t1_163,t1_181,t1_47,t1_73,t1_9,t2_10,t2_102,t2_130,t2_136,t2_164,t2_182,t2_48,t2_74,t_1,t_109,t_125,t_143,t_159,t_169,t_17,t_173,t_177,t_5,t_55,t_81,t_97;

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
var origCOUNT_114: bv64;
var origCOUNT_120: bv64;
var origCOUNT_148: bv64;
var origCOUNT_154: bv64;
var origCOUNT_22: bv64;
var origCOUNT_28: bv64;
var origCOUNT_34: bv32;
var origCOUNT_40: bv32;
var origCOUNT_60: bv64;
var origCOUNT_66: bv64;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_113: bv64;
var origDEST_119: bv64;
var origDEST_147: bv64;
var origDEST_153: bv64;
var origDEST_21: bv64;
var origDEST_27: bv64;
var origDEST_33: bv32;
var origDEST_39: bv32;
var origDEST_59: bv64;
var origDEST_65: bv64;
var origDEST_85: bv64;
var origDEST_91: bv64;
var ra_187: bv64;
var t1_101: bv64;
var t1_129: bv64;
var t1_135: bv64;
var t1_163: bv32;
var t1_181: bv64;
var t1_47: bv64;
var t1_73: bv64;
var t1_9: bv64;
var t2_10: bv64;
var t2_102: bv64;
var t2_130: bv64;
var t2_136: bv64;
var t2_164: bv32;
var t2_182: bv64;
var t2_48: bv64;
var t2_74: bv64;
var t_1: bv64;
var t_109: bv64;
var t_125: bv32;
var t_143: bv64;
var t_159: bv32;
var t_169: bv32;
var t_17: bv64;
var t_173: bv32;
var t_177: bv32;
var t_5: bv32;
var t_55: bv64;
var t_81: bv64;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1264bv64);
axiom policy(1456bv64);
axiom policy(1920bv64);
axiom policy(2624bv64);
axiom policy(2768bv64);
axiom policy(2816bv64);
axiom policy(3200bv64);
axiom policy(6800bv64);
