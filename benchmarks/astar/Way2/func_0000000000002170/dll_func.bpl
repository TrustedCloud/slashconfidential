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
axiom _function_addr_low == 8560bv64;
axiom _function_addr_high == 9472bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2170:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x2175:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x2179:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x217e:
t_1 := RSP;
RSP := MINUS_64(RSP, 136bv64);
CF := bool2bv(LT_64(t_1, 136bv64));
OF := AND_64((XOR_64(t_1, 136bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 136bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2185:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x218d:
t1_5 := RAX;
t2_6 := 4424bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2193:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x2198:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x219d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21a3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x21a8:
t_13 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x21ab:
if (bv2bool(ZF)) {
  goto label_0x21ae;
}

label_0x21ad:
assume false;

label_0x21ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x21b3:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x21b7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x21be:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x21c2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x21c7:
origDEST_23 := RCX;
origCOUNT_24 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x21cb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x21cf:
if (bv2bool(CF)) {
  goto label_0x21d2;
}

label_0x21d1:
assume false;

label_0x21d2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x21d7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x21de:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x21e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x21e8:
t1_29 := RAX;
t2_30 := 4428bv64;
RAX := PLUS_64(RAX, t2_30);
CF := bool2bv(LT_64(RAX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21ee:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x21f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x21f8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21fe:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2203:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x2206:
if (bv2bool(ZF)) {
  goto label_0x2209;
}

label_0x2208:
assume false;

label_0x2209:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x220e:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_14);

label_0x2212:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2219:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x221d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2222:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_16);

label_0x2226:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x222a:
if (bv2bool(CF)) {
  goto label_0x222d;
}

label_0x222c:
assume false;

label_0x222d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x2232:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x2239:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x223b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x2243:
goto label_0x224f;

label_0x2245:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x2249:
t_53 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_53[32:31]) == (1bv32[32:31]))), (XOR_1((t_53[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_53)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x224b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x224f:
t_57 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 256bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_57)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_57, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 256bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))))[1:0]));
SF := t_57[32:31];
ZF := bool2bv(0bv32 == t_57);

label_0x2257:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x2281;
}

label_0x2259:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x225e:
t_61 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(16bv64[64:63]) ,(1bv64 ++ 16bv64) ,(0bv64 ++ 16bv64)))));
RAX := t_61[64:0];
OF := bool2bv(t_61 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_61 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_21;
SF := unconstrained_22;
ZF := unconstrained_23;
AF := unconstrained_24;

label_0x2262:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x226a:
RAX := PLUS_64((PLUS_64(RCX, RAX)), 280bv64)[64:0];

label_0x2272:
RDX := (0bv32 ++ 128bv32);

label_0x2277:
RCX := RAX;

label_0x227a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 8831bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x227f"} true;
call arbitrary_func();

label_0x227f:
goto label_0x2245;

label_0x2281:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2289:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x228f:
t_63 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_63, 1bv32)), (XOR_32(t_63, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_63)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2291:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), RAX[32:0]);

label_0x2295:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x229d:
t1_67 := RAX;
t2_68 := 4408bv64;
RAX := PLUS_64(RAX, t2_68);
CF := bool2bv(LT_64(RAX, t1_67));
OF := AND_1((bool2bv((t1_67[64:63]) == (t2_68[64:63]))), (XOR_1((t1_67[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_67)), t2_68)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x22a3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x22a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x22ad:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x22b3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x22b8:
t_75 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))))[1:0]));
SF := t_75[64:63];
ZF := bool2bv(0bv64 == t_75);

label_0x22bb:
if (bv2bool(ZF)) {
  goto label_0x22be;
}

label_0x22bd:
assume false;

label_0x22be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x22c3:
origDEST_79 := RAX;
origCOUNT_80 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_28);

label_0x22c7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x22ce:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x22d2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x22d7:
origDEST_85 := RCX;
origCOUNT_86 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_30);

label_0x22db:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x22df:
if (bv2bool(CF)) {
  goto label_0x22e2;
}

label_0x22e1:
assume false;

label_0x22e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x22e7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0x22eb:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x22ed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x22f5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4428bv64)));

label_0x22fb:
t_91 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_91, 1bv32)), (XOR_32(t_91, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_91)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x22fd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 100bv64), RAX[32:0]);

label_0x2301:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2309:
t1_95 := RAX;
t2_96 := 4412bv64;
RAX := PLUS_64(RAX, t2_96);
CF := bool2bv(LT_64(RAX, t1_95));
OF := AND_1((bool2bv((t1_95[64:63]) == (t2_96[64:63]))), (XOR_1((t1_95[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_95)), t2_96)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x230f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x2314:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2319:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x231f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2324:
t_103 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))))[1:0]));
SF := t_103[64:63];
ZF := bool2bv(0bv64 == t_103);

label_0x2327:
if (bv2bool(ZF)) {
  goto label_0x232a;
}

label_0x2329:
assume false;

label_0x232a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x232f:
origDEST_107 := RAX;
origCOUNT_108 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_38);

label_0x2333:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x233a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x233e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2343:
origDEST_113 := RCX;
origCOUNT_114 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_40);

label_0x2347:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x234b:
if (bv2bool(CF)) {
  goto label_0x234e;
}

label_0x234d:
assume false;

label_0x234e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2353:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 100bv64)));

label_0x2357:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2359:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2361:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2369:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x236f:
t_119 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_119[32:0]);
OF := bool2bv(t_119 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_119 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_45;
SF := unconstrained_46;
ZF := unconstrained_47;
AF := unconstrained_48;

label_0x2376:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2378:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, RSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_50);

label_0x237c:
RCX := RAX;

label_0x237f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 9092bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2384"} true;
call arbitrary_func();

label_0x2384:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x2389:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2391:
t1_127 := RAX;
t2_128 := 8bv64;
RAX := PLUS_64(RAX, t2_128);
CF := bool2bv(LT_64(RAX, t1_127));
OF := AND_1((bool2bv((t1_127[64:63]) == (t2_128[64:63]))), (XOR_1((t1_127[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_127)), t2_128)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2395:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x239a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x239f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x23a5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x23aa:
t_135 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)), 2bv64)), (XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)), 2bv64)), (XOR_64((RSHIFT_64(t_135, 4bv64)), t_135)))))[1:0]));
SF := t_135[64:63];
ZF := bool2bv(0bv64 == t_135);

label_0x23ad:
if (bv2bool(ZF)) {
  goto label_0x23b0;
}

label_0x23af:
assume false;

label_0x23b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x23b5:
origDEST_139 := RAX;
origCOUNT_140 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_53));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_54);

label_0x23b9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x23c0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x23c4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x23c9:
origDEST_145 := RCX;
origCOUNT_146 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), CF, LSHIFT_64(origDEST_145, (MINUS_64(64bv64, origCOUNT_146)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_146 == 1bv64)), origDEST_145[64:63], unconstrained_55));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_146 == 0bv64)), AF, unconstrained_56);

label_0x23cd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_57;
SF := unconstrained_58;
AF := unconstrained_59;
PF := unconstrained_60;

label_0x23d1:
if (bv2bool(CF)) {
  goto label_0x23d4;
}

label_0x23d3:
assume false;

label_0x23d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x23d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x23de:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x23e1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x23e9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x23f1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x23f7:
t_151 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_151[32:0]);
OF := bool2bv(t_151 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_151 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_61;
SF := unconstrained_62;
ZF := unconstrained_63;
AF := unconstrained_64;

label_0x23fe:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x2400:
origDEST_153 := RAX;
origCOUNT_154 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, RSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_66);

label_0x2404:
R8 := RAX;

label_0x2407:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_67;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2409:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2411:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x2415:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 9242bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x241a"} true;
call arbitrary_func();

label_0x241a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2422:
t1_159 := RAX;
t2_160 := 16bv64;
RAX := PLUS_64(RAX, t2_160);
CF := bool2bv(LT_64(RAX, t1_159));
OF := AND_1((bool2bv((t1_159[64:63]) == (t2_160[64:63]))), (XOR_1((t1_159[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_159)), t2_160)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2426:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x242b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2430:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2436:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x243b:
t_167 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)), 2bv64)), (XOR_64((RSHIFT_64(t_167, 4bv64)), t_167)))))[1:0]));
SF := t_167[64:63];
ZF := bool2bv(0bv64 == t_167);

label_0x243e:
if (bv2bool(ZF)) {
  goto label_0x2441;
}

label_0x2440:
assume false;

label_0x2441:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2446:
origDEST_171 := RAX;
origCOUNT_172 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), CF, LSHIFT_64(origDEST_171, (MINUS_64(64bv64, origCOUNT_172)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_172 == 1bv64)), origDEST_171[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_172 == 0bv64)), AF, unconstrained_71);

label_0x244a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2451:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2455:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x245a:
origDEST_177 := RCX;
origCOUNT_178 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), CF, LSHIFT_64(origDEST_177, (MINUS_64(64bv64, origCOUNT_178)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_178 == 1bv64)), origDEST_177[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_178 == 0bv64)), AF, unconstrained_73);

label_0x245e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x2462:
if (bv2bool(CF)) {
  goto label_0x2465;
}

label_0x2464:
assume false;

label_0x2465:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_78;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2467:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x246c:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0x246f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2477:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x247f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)));

label_0x2485:
t_183 := TIMES_64(((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4428bv64)))))));
RAX := (0bv32 ++ t_183[32:0]);
OF := bool2bv(t_183 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
CF := bool2bv(t_183 != ((ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])))));
PF := unconstrained_79;
SF := unconstrained_80;
ZF := unconstrained_81;
AF := unconstrained_82;

label_0x248c:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x248e:
RCX := RAX;

label_0x2491:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 9366bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2496"} true;
call arbitrary_func();

label_0x2496:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x249b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x24a3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x24a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24ad:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_83;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x24b3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x24b8:
t_187 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_84;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))))[1:0]));
SF := t_187[64:63];
ZF := bool2bv(0bv64 == t_187);

label_0x24bb:
if (bv2bool(ZF)) {
  goto label_0x24be;
}

label_0x24bd:
assume false;

label_0x24be:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24c3:
origDEST_191 := RAX;
origCOUNT_192 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_85));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_86);

label_0x24c7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x24ce:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x24d2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24d7:
origDEST_197 := RCX;
origCOUNT_198 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), CF, LSHIFT_64(origDEST_197, (MINUS_64(64bv64, origCOUNT_198)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_198 == 1bv64)), origDEST_197[64:63], unconstrained_87));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), AF, unconstrained_88);

label_0x24db:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_89;
SF := unconstrained_90;
AF := unconstrained_91;
PF := unconstrained_92;

label_0x24df:
if (bv2bool(CF)) {
  goto label_0x24e2;
}

label_0x24e1:
assume false;

label_0x24e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24e7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x24ec:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x24ef:
RAX := (RAX[64:8]) ++ 1bv8;

label_0x24f1:
t1_203 := RSP;
t2_204 := 136bv64;
RSP := PLUS_64(RSP, t2_204);
CF := bool2bv(LT_64(RSP, t1_203));
OF := AND_1((bool2bv((t1_203[64:63]) == (t2_204[64:63]))), (XOR_1((t1_203[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_203)), t2_204)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x24f8:

ra_209 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_108,origCOUNT_114,origCOUNT_122,origCOUNT_140,origCOUNT_146,origCOUNT_154,origCOUNT_172,origCOUNT_178,origCOUNT_18,origCOUNT_192,origCOUNT_198,origCOUNT_24,origCOUNT_42,origCOUNT_48,origCOUNT_80,origCOUNT_86,origDEST_107,origDEST_113,origDEST_121,origDEST_139,origDEST_145,origDEST_153,origDEST_17,origDEST_171,origDEST_177,origDEST_191,origDEST_197,origDEST_23,origDEST_41,origDEST_47,origDEST_79,origDEST_85,ra_209,t1_127,t1_159,t1_203,t1_29,t1_5,t1_67,t1_95,t2_128,t2_160,t2_204,t2_30,t2_6,t2_68,t2_96,t_1,t_103,t_119,t_13,t_135,t_151,t_167,t_183,t_187,t_37,t_53,t_57,t_61,t_63,t_75,t_91;

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
var origCOUNT_108: bv64;
var origCOUNT_114: bv64;
var origCOUNT_122: bv64;
var origCOUNT_140: bv64;
var origCOUNT_146: bv64;
var origCOUNT_154: bv64;
var origCOUNT_172: bv64;
var origCOUNT_178: bv64;
var origCOUNT_18: bv64;
var origCOUNT_192: bv64;
var origCOUNT_198: bv64;
var origCOUNT_24: bv64;
var origCOUNT_42: bv64;
var origCOUNT_48: bv64;
var origCOUNT_80: bv64;
var origCOUNT_86: bv64;
var origDEST_107: bv64;
var origDEST_113: bv64;
var origDEST_121: bv64;
var origDEST_139: bv64;
var origDEST_145: bv64;
var origDEST_153: bv64;
var origDEST_17: bv64;
var origDEST_171: bv64;
var origDEST_177: bv64;
var origDEST_191: bv64;
var origDEST_197: bv64;
var origDEST_23: bv64;
var origDEST_41: bv64;
var origDEST_47: bv64;
var origDEST_79: bv64;
var origDEST_85: bv64;
var ra_209: bv64;
var t1_127: bv64;
var t1_159: bv64;
var t1_203: bv64;
var t1_29: bv64;
var t1_5: bv64;
var t1_67: bv64;
var t1_95: bv64;
var t2_128: bv64;
var t2_160: bv64;
var t2_204: bv64;
var t2_30: bv64;
var t2_6: bv64;
var t2_68: bv64;
var t2_96: bv64;
var t_1: bv64;
var t_103: bv64;
var t_119: bv64;
var t_13: bv64;
var t_135: bv64;
var t_151: bv64;
var t_167: bv64;
var t_183: bv64;
var t_187: bv64;
var t_37: bv64;
var t_53: bv32;
var t_57: bv32;
var t_61: bv128;
var t_63: bv32;
var t_75: bv64;
var t_91: bv32;


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
