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
axiom _function_addr_low == 15504bv64;
axiom _function_addr_high == 17728bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x3c90:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x3c95:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x3c9a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x3c9e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x3ca3:
t_1 := RSP;
RSP := MINUS_64(RSP, 184bv64);
CF := bool2bv(LT_64(t_1, 184bv64));
OF := AND_64((XOR_64(t_1, 184bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 184bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3caa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 224bv64)));

label_0x3cb1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x3cb5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), 0bv64);

label_0x3cbe:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x3cc7:
if (bv2bool(ZF)) {
  goto label_0x3d1a;
}

label_0x3cc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3cd1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3cd7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3cdc:
t_11 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x3cdf:
if (bv2bool(ZF)) {
  goto label_0x3ce2;
}

label_0x3ce1:
assume false;

label_0x3ce2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3cea:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_4);

label_0x3cee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3cf5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3cf9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3d01:
origDEST_21 := RCX;
origCOUNT_22 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_6);

label_0x3d05:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x3d09:
if (bv2bool(CF)) {
  goto label_0x3d0c;
}

label_0x3d0b:
assume false;

label_0x3d0c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3d14:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3d1a:
t_27 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_27)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_27, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x3d20:
if (bv2bool(ZF)) {
  goto label_0x3d77;
}

label_0x3d22:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3d27:
t1_31 := RAX;
t2_32 := 5096bv64;
RAX := PLUS_64(RAX, t2_32);
CF := bool2bv(LT_64(RAX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3d2d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x3d32:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3d37:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3d3d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3d42:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x3d45:
if (bv2bool(ZF)) {
  goto label_0x3d48;
}

label_0x3d47:
assume false;

label_0x3d48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3d4d:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0x3d51:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3d58:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3d5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3d61:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_16);

label_0x3d65:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x3d69:
if (bv2bool(CF)) {
  goto label_0x3d6c;
}

label_0x3d6b:
assume false;

label_0x3d6c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x3d71:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x3d77:
t_55 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))), t_55)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_55, (LOAD_LE_32(mem, PLUS_64(RSP, 200bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))))[1:0]));
SF := t_55[32:31];
ZF := bool2bv(0bv32 == t_55);

label_0x3d7f:
if (bv2bool(ZF)) {
  goto label_0x3dbe;
}

label_0x3d81:
t_59 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), t_59)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_59, (LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))))[1:0]));
SF := t_59[32:31];
ZF := bool2bv(0bv32 == t_59);

label_0x3d89:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x3dbe;
}

label_0x3d8b:
t_63 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 9bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 9bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), 9bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))), t_63)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_63, (LOAD_LE_32(mem, PLUS_64(RSP, 208bv64))))), 9bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x3d93:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x3dbe;
}

label_0x3d95:
t_67 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_67)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_67, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))))[1:0]));
SF := t_67[32:31];
ZF := bool2bv(0bv32 == t_67);

label_0x3d9a:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x3dbe;
}

label_0x3d9c:
t_71 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 250bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_71)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_71, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 250bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))))[1:0]));
SF := t_71[32:31];
ZF := bool2bv(0bv32 == t_71);

label_0x3da4:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x3dbe;
}

label_0x3da6:
t_75 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), t_75)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_75, (LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))))[1:0]));
SF := t_75[32:31];
ZF := bool2bv(0bv32 == t_75);

label_0x3dae:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x3dbe;
}

label_0x3db0:
t_79 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))), t_79)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_79, (LOAD_LE_32(mem, PLUS_64(RSP, 216bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))))[1:0]));
SF := t_79[32:31];
ZF := bool2bv(0bv32 == t_79);

label_0x3db8:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3e7e;
}

label_0x3dbe:
t_83 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_83)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_83, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0x3dc7:
if (bv2bool(ZF)) {
  goto label_0x3e1a;
}

label_0x3dc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3dd1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3dd7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3ddc:
t_89 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)), 2bv64)), (XOR_64((RSHIFT_64(t_89, 4bv64)), t_89)))))[1:0]));
SF := t_89[64:63];
ZF := bool2bv(0bv64 == t_89);

label_0x3ddf:
if (bv2bool(ZF)) {
  goto label_0x3de2;
}

label_0x3de1:
assume false;

label_0x3de2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3dea:
origDEST_93 := RAX;
origCOUNT_94 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), CF, LSHIFT_64(origDEST_93, (MINUS_64(64bv64, origCOUNT_94)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_94 == 1bv64)), origDEST_93[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_94 == 0bv64)), AF, unconstrained_24);

label_0x3dee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3df5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3df9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3e01:
origDEST_99 := RCX;
origCOUNT_100 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), CF, LSHIFT_64(origDEST_99, (MINUS_64(64bv64, origCOUNT_100)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_100 == 1bv64)), origDEST_99[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), AF, unconstrained_26);

label_0x3e05:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x3e09:
if (bv2bool(CF)) {
  goto label_0x3e0c;
}

label_0x3e0b:
assume false;

label_0x3e0c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3e14:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x3e1a:
t_105 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_105)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_105, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)), 2bv64)), (XOR_64((RSHIFT_64(t_105, 4bv64)), t_105)))))[1:0]));
SF := t_105[64:63];
ZF := bool2bv(0bv64 == t_105);

label_0x3e20:
if (bv2bool(ZF)) {
  goto label_0x3e77;
}

label_0x3e22:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3e27:
t1_109 := RAX;
t2_110 := 5096bv64;
RAX := PLUS_64(RAX, t2_110);
CF := bool2bv(LT_64(RAX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3e2d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x3e32:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3e37:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3e3d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3e42:
t_117 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x3e45:
if (bv2bool(ZF)) {
  goto label_0x3e48;
}

label_0x3e47:
assume false;

label_0x3e48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3e4d:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_34);

label_0x3e51:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3e58:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3e5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3e61:
origDEST_127 := RCX;
origCOUNT_128 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_36);

label_0x3e65:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x3e69:
if (bv2bool(CF)) {
  goto label_0x3e6c;
}

label_0x3e6b:
assume false;

label_0x3e6c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x3e71:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x3e77:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_41;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3e79:
goto label_0x452f;

label_0x3e7e:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3e80:
t_133 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0x3e82:
if (bv2bool(ZF)) {
  goto label_0x3f48;
}

label_0x3e88:
t_137 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_137)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_137, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)), 2bv64)), (XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)), 2bv64)), (XOR_64((RSHIFT_64(t_137, 4bv64)), t_137)))))[1:0]));
SF := t_137[64:63];
ZF := bool2bv(0bv64 == t_137);

label_0x3e91:
if (bv2bool(ZF)) {
  goto label_0x3ee4;
}

label_0x3e93:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3e9b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3ea1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3ea6:
t_143 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)), 2bv64)), (XOR_64((RSHIFT_64(t_143, 4bv64)), t_143)))))[1:0]));
SF := t_143[64:63];
ZF := bool2bv(0bv64 == t_143);

label_0x3ea9:
if (bv2bool(ZF)) {
  goto label_0x3eac;
}

label_0x3eab:
assume false;

label_0x3eac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3eb4:
origDEST_147 := RAX;
origCOUNT_148 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), CF, LSHIFT_64(origDEST_147, (MINUS_64(64bv64, origCOUNT_148)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_148 == 1bv64)), origDEST_147[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), AF, unconstrained_47);

label_0x3eb8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3ebf:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3ec3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3ecb:
origDEST_153 := RCX;
origCOUNT_154 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_49);

label_0x3ecf:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_50;
SF := unconstrained_51;
AF := unconstrained_52;
PF := unconstrained_53;

label_0x3ed3:
if (bv2bool(CF)) {
  goto label_0x3ed6;
}

label_0x3ed5:
assume false;

label_0x3ed6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3ede:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x3ee4:
t_159 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_159)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_159, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))))[1:0]));
SF := t_159[64:63];
ZF := bool2bv(0bv64 == t_159);

label_0x3eea:
if (bv2bool(ZF)) {
  goto label_0x3f41;
}

label_0x3eec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3ef1:
t1_163 := RAX;
t2_164 := 5096bv64;
RAX := PLUS_64(RAX, t2_164);
CF := bool2bv(LT_64(RAX, t1_163));
OF := AND_1((bool2bv((t1_163[64:63]) == (t2_164[64:63]))), (XOR_1((t1_163[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_163)), t2_164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3ef7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x3efc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3f01:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3f07:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3f0c:
t_171 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))))[1:0]));
SF := t_171[64:63];
ZF := bool2bv(0bv64 == t_171);

label_0x3f0f:
if (bv2bool(ZF)) {
  goto label_0x3f12;
}

label_0x3f11:
assume false;

label_0x3f12:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3f17:
origDEST_175 := RAX;
origCOUNT_176 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), CF, LSHIFT_64(origDEST_175, (MINUS_64(64bv64, origCOUNT_176)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_176 == 1bv64)), origDEST_175[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_176 == 0bv64)), AF, unconstrained_57);

label_0x3f1b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3f22:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3f26:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3f2b:
origDEST_181 := RCX;
origCOUNT_182 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, LSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), origDEST_181[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_59);

label_0x3f2f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_60;
SF := unconstrained_61;
AF := unconstrained_62;
PF := unconstrained_63;

label_0x3f33:
if (bv2bool(CF)) {
  goto label_0x3f36;
}

label_0x3f35:
assume false;

label_0x3f36:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x3f3b:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x3f41:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_64;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3f43:
goto label_0x452f;

label_0x3f48:
RCX := (0bv32 ++ 5104bv32);

label_0x3f4d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 16210bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3f52"} true;
call arbitrary_func();

label_0x3f52:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x3f57:
t_187 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_187)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_187, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))))[1:0]));
SF := t_187[64:63];
ZF := bool2bv(0bv64 == t_187);

label_0x3f5d:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4023;
}

label_0x3f63:
t_191 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_191)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_191, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)), 2bv64)), (XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)), 2bv64)), (XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)))))[1:0]));
SF := t_191[64:63];
ZF := bool2bv(0bv64 == t_191);

label_0x3f6c:
if (bv2bool(ZF)) {
  goto label_0x3fbf;
}

label_0x3f6e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3f76:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3f7c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3f81:
t_197 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)), 2bv64)), (XOR_64((RSHIFT_64(t_197, 4bv64)), t_197)))))[1:0]));
SF := t_197[64:63];
ZF := bool2bv(0bv64 == t_197);

label_0x3f84:
if (bv2bool(ZF)) {
  goto label_0x3f87;
}

label_0x3f86:
assume false;

label_0x3f87:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3f8f:
origDEST_201 := RAX;
origCOUNT_202 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), CF, LSHIFT_64(origDEST_201, (MINUS_64(64bv64, origCOUNT_202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_202 == 1bv64)), origDEST_201[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), AF, unconstrained_68);

label_0x3f93:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3f9a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3f9e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3fa6:
origDEST_207 := RCX;
origCOUNT_208 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), CF, LSHIFT_64(origDEST_207, (MINUS_64(64bv64, origCOUNT_208)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_208 == 1bv64)), origDEST_207[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_208 == 0bv64)), AF, unconstrained_70);

label_0x3faa:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_71;
SF := unconstrained_72;
AF := unconstrained_73;
PF := unconstrained_74;

label_0x3fae:
if (bv2bool(CF)) {
  goto label_0x3fb1;
}

label_0x3fb0:
assume false;

label_0x3fb1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x3fb9:
mem := STORE_LE_32(mem, RAX, 4294967293bv32);

label_0x3fbf:
t_213 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_213)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_213, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))))[1:0]));
SF := t_213[64:63];
ZF := bool2bv(0bv64 == t_213);

label_0x3fc5:
if (bv2bool(ZF)) {
  goto label_0x401c;
}

label_0x3fc7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3fcc:
t1_217 := RAX;
t2_218 := 5096bv64;
RAX := PLUS_64(RAX, t2_218);
CF := bool2bv(LT_64(RAX, t1_217));
OF := AND_1((bool2bv((t1_217[64:63]) == (t2_218[64:63]))), (XOR_1((t1_217[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_217)), t2_218)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3fd2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x3fd7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3fdc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3fe2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3fe7:
t_225 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_76;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))))[1:0]));
SF := t_225[64:63];
ZF := bool2bv(0bv64 == t_225);

label_0x3fea:
if (bv2bool(ZF)) {
  goto label_0x3fed;
}

label_0x3fec:
assume false;

label_0x3fed:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3ff2:
origDEST_229 := RAX;
origCOUNT_230 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), CF, LSHIFT_64(origDEST_229, (MINUS_64(64bv64, origCOUNT_230)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_230 == 1bv64)), origDEST_229[64:63], unconstrained_77));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_230 == 0bv64)), AF, unconstrained_78);

label_0x3ff6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3ffd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4001:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x4006:
origDEST_235 := RCX;
origCOUNT_236 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), CF, LSHIFT_64(origDEST_235, (MINUS_64(64bv64, origCOUNT_236)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_236 == 1bv64)), origDEST_235[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_236 == 0bv64)), AF, unconstrained_80);

label_0x400a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_81;
SF := unconstrained_82;
AF := unconstrained_83;
PF := unconstrained_84;

label_0x400e:
if (bv2bool(CF)) {
  goto label_0x4011;
}

label_0x4010:
assume false;

label_0x4011:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x4016:
mem := STORE_LE_32(mem, RAX, 4294967293bv32);

label_0x401c:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_85;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x401e:
goto label_0x452f;

label_0x4023:
t_241 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_241)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_241, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)), 2bv64)), (XOR_64((RSHIFT_64(t_241, 4bv64)), t_241)))))[1:0]));
SF := t_241[64:63];
ZF := bool2bv(0bv64 == t_241);

label_0x402c:
if (bv2bool(ZF)) {
  goto label_0x407f;
}

label_0x402e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4036:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x403c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4041:
t_247 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)), 2bv64)), (XOR_64((RSHIFT_64(t_247, 4bv64)), t_247)))))[1:0]));
SF := t_247[64:63];
ZF := bool2bv(0bv64 == t_247);

label_0x4044:
if (bv2bool(ZF)) {
  goto label_0x4047;
}

label_0x4046:
assume false;

label_0x4047:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x404f:
origDEST_251 := RAX;
origCOUNT_252 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), CF, LSHIFT_64(origDEST_251, (MINUS_64(64bv64, origCOUNT_252)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv64)), origDEST_251[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv64)), AF, unconstrained_89);

label_0x4053:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x405a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x405e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4066:
origDEST_257 := RCX;
origCOUNT_258 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_91);

label_0x406a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_92;
SF := unconstrained_93;
AF := unconstrained_94;
PF := unconstrained_95;

label_0x406e:
if (bv2bool(CF)) {
  goto label_0x4071;
}

label_0x4070:
assume false;

label_0x4071:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x4079:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x407f:
t_263 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_263)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_263, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)), 2bv64)), (XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)), 2bv64)), (XOR_64((RSHIFT_64(t_263, 4bv64)), t_263)))))[1:0]));
SF := t_263[64:63];
ZF := bool2bv(0bv64 == t_263);

label_0x4085:
if (bv2bool(ZF)) {
  goto label_0x40dc;
}

label_0x4087:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x408c:
t1_267 := RAX;
t2_268 := 5096bv64;
RAX := PLUS_64(RAX, t2_268);
CF := bool2bv(LT_64(RAX, t1_267));
OF := AND_1((bool2bv((t1_267[64:63]) == (t2_268[64:63]))), (XOR_1((t1_267[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_267)), t2_268)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4092:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x4097:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x409c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x40a2:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x40a7:
t_275 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_97;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))))[1:0]));
SF := t_275[64:63];
ZF := bool2bv(0bv64 == t_275);

label_0x40aa:
if (bv2bool(ZF)) {
  goto label_0x40ad;
}

label_0x40ac:
assume false;

label_0x40ad:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x40b2:
origDEST_279 := RAX;
origCOUNT_280 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), CF, LSHIFT_64(origDEST_279, (MINUS_64(64bv64, origCOUNT_280)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_280 == 1bv64)), origDEST_279[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_280 == 0bv64)), AF, unconstrained_99);

label_0x40b6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x40bd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x40c1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x40c6:
origDEST_285 := RCX;
origCOUNT_286 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), CF, LSHIFT_64(origDEST_285, (MINUS_64(64bv64, origCOUNT_286)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_286 == 1bv64)), origDEST_285[64:63], unconstrained_100));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), AF, unconstrained_101);

label_0x40ca:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_102;
SF := unconstrained_103;
AF := unconstrained_104;
PF := unconstrained_105;

label_0x40ce:
if (bv2bool(CF)) {
  goto label_0x40d1;
}

label_0x40d0:
assume false;

label_0x40d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x40d6:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x40dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x40e1:
t1_291 := RAX;
t2_292 := 5100bv64;
RAX := PLUS_64(RAX, t2_292);
CF := bool2bv(LT_64(RAX, t1_291));
OF := AND_1((bool2bv((t1_291[64:63]) == (t2_292[64:63]))), (XOR_1((t1_291[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_291)), t2_292)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x40e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x40ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x40f1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x40f7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x40fc:
t_299 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)), 2bv64)), (XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)), 2bv64)), (XOR_64((RSHIFT_64(t_299, 4bv64)), t_299)))))[1:0]));
SF := t_299[64:63];
ZF := bool2bv(0bv64 == t_299);

label_0x40ff:
if (bv2bool(ZF)) {
  goto label_0x4102;
}

label_0x4101:
assume false;

label_0x4102:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x4107:
origDEST_303 := RAX;
origCOUNT_304 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), CF, LSHIFT_64(origDEST_303, (MINUS_64(64bv64, origCOUNT_304)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_304 == 1bv64)), origDEST_303[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_304 == 0bv64)), AF, unconstrained_109);

label_0x410b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4112:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4116:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x411b:
origDEST_309 := RCX;
origCOUNT_310 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), CF, LSHIFT_64(origDEST_309, (MINUS_64(64bv64, origCOUNT_310)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv64)), origDEST_309[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), AF, unconstrained_111);

label_0x411f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_112;
SF := unconstrained_113;
AF := unconstrained_114;
PF := unconstrained_115;

label_0x4123:
if (bv2bool(CF)) {
  goto label_0x4126;
}

label_0x4125:
assume false;

label_0x4126:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x412b:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x412e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4133:
t1_315 := RAX;
t2_316 := 5004bv64;
RAX := PLUS_64(RAX, t2_316);
CF := bool2bv(LT_64(RAX, t1_315));
OF := AND_1((bool2bv((t1_315[64:63]) == (t2_316[64:63]))), (XOR_1((t1_315[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_315)), t2_316)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4139:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x413e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x4143:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4149:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x414e:
t_323 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)), 2bv64)), (XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)), 2bv64)), (XOR_64((RSHIFT_64(t_323, 4bv64)), t_323)))))[1:0]));
SF := t_323[64:63];
ZF := bool2bv(0bv64 == t_323);

label_0x4151:
if (bv2bool(ZF)) {
  goto label_0x4154;
}

label_0x4153:
assume false;

label_0x4154:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x4159:
origDEST_327 := RAX;
origCOUNT_328 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), CF, LSHIFT_64(origDEST_327, (MINUS_64(64bv64, origCOUNT_328)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_328 == 1bv64)), origDEST_327[64:63], unconstrained_118));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_328 == 0bv64)), AF, unconstrained_119);

label_0x415d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4164:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4168:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x416d:
origDEST_333 := RCX;
origCOUNT_334 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), CF, LSHIFT_64(origDEST_333, (MINUS_64(64bv64, origCOUNT_334)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_334 == 1bv64)), origDEST_333[64:63], unconstrained_120));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), AF, unconstrained_121);

label_0x4171:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_122;
SF := unconstrained_123;
AF := unconstrained_124;
PF := unconstrained_125;

label_0x4175:
if (bv2bool(CF)) {
  goto label_0x4178;
}

label_0x4177:
assume false;

label_0x4178:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x417d:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x4183:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4188:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x418d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x4192:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4198:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x419d:
t_341 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)), 2bv64)), (XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)), 2bv64)), (XOR_64((RSHIFT_64(t_341, 4bv64)), t_341)))))[1:0]));
SF := t_341[64:63];
ZF := bool2bv(0bv64 == t_341);

label_0x41a0:
if (bv2bool(ZF)) {
  goto label_0x41a3;
}

label_0x41a2:
assume false;

label_0x41a3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x41a8:
origDEST_345 := RAX;
origCOUNT_346 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), CF, LSHIFT_64(origDEST_345, (MINUS_64(64bv64, origCOUNT_346)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_346 == 1bv64)), origDEST_345[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_346 == 0bv64)), AF, unconstrained_129);

label_0x41ac:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x41b3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x41b7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x41bc:
origDEST_351 := RCX;
origCOUNT_352 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), CF, LSHIFT_64(origDEST_351, (MINUS_64(64bv64, origCOUNT_352)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_352 == 1bv64)), origDEST_351[64:63], unconstrained_130));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_352 == 0bv64)), AF, unconstrained_131);

label_0x41c0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_132;
SF := unconstrained_133;
AF := unconstrained_134;
PF := unconstrained_135;

label_0x41c4:
if (bv2bool(CF)) {
  goto label_0x41c7;
}

label_0x41c6:
assume false;

label_0x41c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x41cc:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x41d3:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x41d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x41da:
t1_357 := RAX;
t2_358 := 5008bv64;
RAX := PLUS_64(RAX, t2_358);
CF := bool2bv(LT_64(RAX, t1_357));
OF := AND_1((bool2bv((t1_357[64:63]) == (t2_358[64:63]))), (XOR_1((t1_357[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_357)), t2_358)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41e0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x41e5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x41ea:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x41f0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x41f5:
t_365 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_137;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_365, 4bv64)), t_365)), 2bv64)), (XOR_64((RSHIFT_64(t_365, 4bv64)), t_365)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_365, 4bv64)), t_365)), 2bv64)), (XOR_64((RSHIFT_64(t_365, 4bv64)), t_365)))))[1:0]));
SF := t_365[64:63];
ZF := bool2bv(0bv64 == t_365);

label_0x41f8:
if (bv2bool(ZF)) {
  goto label_0x41fb;
}

label_0x41fa:
assume false;

label_0x41fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4200:
origDEST_369 := RAX;
origCOUNT_370 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), CF, LSHIFT_64(origDEST_369, (MINUS_64(64bv64, origCOUNT_370)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_370 == 1bv64)), origDEST_369[64:63], unconstrained_138));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_370 == 0bv64)), AF, unconstrained_139);

label_0x4204:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x420b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x420f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4214:
origDEST_375 := RCX;
origCOUNT_376 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), CF, LSHIFT_64(origDEST_375, (MINUS_64(64bv64, origCOUNT_376)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_376 == 1bv64)), origDEST_375[64:63], unconstrained_140));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_376 == 0bv64)), AF, unconstrained_141);

label_0x4218:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_142;
SF := unconstrained_143;
AF := unconstrained_144;
PF := unconstrained_145;

label_0x421c:
if (bv2bool(CF)) {
  goto label_0x421f;
}

label_0x421e:
assume false;

label_0x421f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4224:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x4227:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x422c:
t1_381 := RAX;
t2_382 := 5072bv64;
RAX := PLUS_64(RAX, t2_382);
CF := bool2bv(LT_64(RAX, t1_381));
OF := AND_1((bool2bv((t1_381[64:63]) == (t2_382[64:63]))), (XOR_1((t1_381[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_381)), t2_382)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4232:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x4237:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x423c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4242:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4247:
t_389 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)), 2bv64)), (XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)), 2bv64)), (XOR_64((RSHIFT_64(t_389, 4bv64)), t_389)))))[1:0]));
SF := t_389[64:63];
ZF := bool2bv(0bv64 == t_389);

label_0x424a:
if (bv2bool(ZF)) {
  goto label_0x424d;
}

label_0x424c:
assume false;

label_0x424d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4252:
origDEST_393 := RAX;
origCOUNT_394 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), CF, LSHIFT_64(origDEST_393, (MINUS_64(64bv64, origCOUNT_394)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_394 == 1bv64)), origDEST_393[64:63], unconstrained_148));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_394 == 0bv64)), AF, unconstrained_149);

label_0x4256:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x425d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4261:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4266:
origDEST_399 := RCX;
origCOUNT_400 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), CF, LSHIFT_64(origDEST_399, (MINUS_64(64bv64, origCOUNT_400)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_400 == 1bv64)), origDEST_399[64:63], unconstrained_150));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_400 == 0bv64)), AF, unconstrained_151);

label_0x426a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_152;
SF := unconstrained_153;
AF := unconstrained_154;
PF := unconstrained_155;

label_0x426e:
if (bv2bool(CF)) {
  goto label_0x4271;
}

label_0x4270:
assume false;

label_0x4271:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x4276:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x427d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4282:
t1_405 := RAX;
t2_406 := 5080bv64;
RAX := PLUS_64(RAX, t2_406);
CF := bool2bv(LT_64(RAX, t1_405));
OF := AND_1((bool2bv((t1_405[64:63]) == (t2_406[64:63]))), (XOR_1((t1_405[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_405)), t2_406)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4288:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x4290:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x4298:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x429e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x42a3:
t_413 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)), 2bv64)), (XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)), 2bv64)), (XOR_64((RSHIFT_64(t_413, 4bv64)), t_413)))))[1:0]));
SF := t_413[64:63];
ZF := bool2bv(0bv64 == t_413);

label_0x42a6:
if (bv2bool(ZF)) {
  goto label_0x42a9;
}

label_0x42a8:
assume false;

label_0x42a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x42b1:
origDEST_417 := RAX;
origCOUNT_418 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), CF, LSHIFT_64(origDEST_417, (MINUS_64(64bv64, origCOUNT_418)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_418 == 1bv64)), origDEST_417[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_418 == 0bv64)), AF, unconstrained_159);

label_0x42b5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x42bc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x42c0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x42c8:
origDEST_423 := RCX;
origCOUNT_424 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), CF, LSHIFT_64(origDEST_423, (MINUS_64(64bv64, origCOUNT_424)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_424 == 1bv64)), origDEST_423[64:63], unconstrained_160));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_424 == 0bv64)), AF, unconstrained_161);

label_0x42cc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_162;
SF := unconstrained_163;
AF := unconstrained_164;
PF := unconstrained_165;

label_0x42d0:
if (bv2bool(CF)) {
  goto label_0x42d3;
}

label_0x42d2:
assume false;

label_0x42d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x42db:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x42e2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x42e7:
t1_429 := RAX;
t2_430 := 5088bv64;
RAX := PLUS_64(RAX, t2_430);
CF := bool2bv(LT_64(RAX, t1_429));
OF := AND_1((bool2bv((t1_429[64:63]) == (t2_430[64:63]))), (XOR_1((t1_429[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_429)), t2_430)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x42ed:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x42f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x42fd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_166;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4303:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4308:
t_437 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))))[1:0]));
SF := t_437[64:63];
ZF := bool2bv(0bv64 == t_437);

label_0x430b:
if (bv2bool(ZF)) {
  goto label_0x430e;
}

label_0x430d:
assume false;

label_0x430e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4316:
origDEST_441 := RAX;
origCOUNT_442 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), CF, LSHIFT_64(origDEST_441, (MINUS_64(64bv64, origCOUNT_442)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_442 == 1bv64)), origDEST_441[64:63], unconstrained_168));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), AF, unconstrained_169);

label_0x431a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4321:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4325:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x432d:
origDEST_447 := RCX;
origCOUNT_448 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), CF, LSHIFT_64(origDEST_447, (MINUS_64(64bv64, origCOUNT_448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_448 == 1bv64)), origDEST_447[64:63], unconstrained_170));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), AF, unconstrained_171);

label_0x4331:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_172;
SF := unconstrained_173;
AF := unconstrained_174;
PF := unconstrained_175;

label_0x4335:
if (bv2bool(CF)) {
  goto label_0x4338;
}

label_0x4337:
assume false;

label_0x4338:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x4340:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x4347:
t_453 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_453)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_453, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_453, 4bv32)), t_453)), 2bv32)), (XOR_32((RSHIFT_32(t_453, 4bv32)), t_453)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_453, 4bv32)), t_453)), 2bv32)), (XOR_32((RSHIFT_32(t_453, 4bv32)), t_453)))))[1:0]));
SF := t_453[32:31];
ZF := bool2bv(0bv32 == t_453);

label_0x434c:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x4356;
}

label_0x434e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 30bv32);

label_0x4356:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x435b:
t1_457 := RAX;
t2_458 := 5016bv64;
RAX := PLUS_64(RAX, t2_458);
CF := bool2bv(LT_64(RAX, t1_457));
OF := AND_1((bool2bv((t1_457[64:63]) == (t2_458[64:63]))), (XOR_1((t1_457[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_457)), t2_458)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4361:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x4366:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 216bv64)));

label_0x436e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x4375:
RCX := RAX;

label_0x4378:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 17277bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x437d"} true;
call arbitrary_func();

label_0x437d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x4381:
t_463 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_463)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_463, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)), 2bv32)), (XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)), 2bv32)), (XOR_32((RSHIFT_32(t_463, 4bv32)), t_463)))))[1:0]));
SF := t_463[32:31];
ZF := bool2bv(0bv32 == t_463);

label_0x4386:
if (bv2bool(ZF)) {
  goto label_0x4465;
}

label_0x438c:
t_467 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))), t_467)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_467, (LOAD_LE_64(mem, PLUS_64(RSP, 192bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)), 2bv64)), (XOR_64((RSHIFT_64(t_467, 4bv64)), t_467)))))[1:0]));
SF := t_467[64:63];
ZF := bool2bv(0bv64 == t_467);

label_0x4395:
if (bv2bool(ZF)) {
  goto label_0x43e8;
}

label_0x4397:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x439f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x43a5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x43aa:
t_473 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)), 2bv64)), (XOR_64((RSHIFT_64(t_473, 4bv64)), t_473)))))[1:0]));
SF := t_473[64:63];
ZF := bool2bv(0bv64 == t_473);

label_0x43ad:
if (bv2bool(ZF)) {
  goto label_0x43b0;
}

label_0x43af:
assume false;

label_0x43b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x43b8:
origDEST_477 := RAX;
origCOUNT_478 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), CF, LSHIFT_64(origDEST_477, (MINUS_64(64bv64, origCOUNT_478)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_478 == 1bv64)), origDEST_477[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_478 == 0bv64)), AF, unconstrained_179);

label_0x43bc:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x43c3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x43c7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x43cf:
origDEST_483 := RCX;
origCOUNT_484 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), CF, LSHIFT_64(origDEST_483, (MINUS_64(64bv64, origCOUNT_484)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_484 == 1bv64)), origDEST_483[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_484 == 0bv64)), AF, unconstrained_181);

label_0x43d3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_182;
SF := unconstrained_183;
AF := unconstrained_184;
PF := unconstrained_185;

label_0x43d7:
if (bv2bool(CF)) {
  goto label_0x43da;
}

label_0x43d9:
assume false;

label_0x43da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x43e2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x43e6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x43e8:
t_489 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_489)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_489, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)), 2bv64)), (XOR_64((RSHIFT_64(t_489, 4bv64)), t_489)))))[1:0]));
SF := t_489[64:63];
ZF := bool2bv(0bv64 == t_489);

label_0x43ee:
if (bv2bool(ZF)) {
  goto label_0x4454;
}

label_0x43f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x43f5:
t1_493 := RAX;
t2_494 := 5096bv64;
RAX := PLUS_64(RAX, t2_494);
CF := bool2bv(LT_64(RAX, t1_493));
OF := AND_1((bool2bv((t1_493[64:63]) == (t2_494[64:63]))), (XOR_1((t1_493[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_493)), t2_494)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x43fb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x4403:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x440b:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4411:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4416:
t_501 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)), 2bv64)), (XOR_64((RSHIFT_64(t_501, 4bv64)), t_501)))))[1:0]));
SF := t_501[64:63];
ZF := bool2bv(0bv64 == t_501);

label_0x4419:
if (bv2bool(ZF)) {
  goto label_0x441c;
}

label_0x441b:
assume false;

label_0x441c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x4424:
origDEST_505 := RAX;
origCOUNT_506 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), CF, LSHIFT_64(origDEST_505, (MINUS_64(64bv64, origCOUNT_506)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_506 == 1bv64)), origDEST_505[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_506 == 0bv64)), AF, unconstrained_189);

label_0x4428:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x442f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4433:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x443b:
origDEST_511 := RCX;
origCOUNT_512 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), CF, LSHIFT_64(origDEST_511, (MINUS_64(64bv64, origCOUNT_512)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_512 == 1bv64)), origDEST_511[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_512 == 0bv64)), AF, unconstrained_191);

label_0x443f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_192;
SF := unconstrained_193;
AF := unconstrained_194;
PF := unconstrained_195;

label_0x4443:
if (bv2bool(CF)) {
  goto label_0x4446;
}

label_0x4445:
assume false;

label_0x4446:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x444e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x4452:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x4454:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x4459:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 17502bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x445e"} true;
call arbitrary_func();

label_0x445e:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_196;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x4460:
goto label_0x452f;

label_0x4465:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x446a:
t1_517 := RAX;
t2_518 := 5024bv64;
RAX := PLUS_64(RAX, t2_518);
CF := bool2bv(LT_64(RAX, t1_517));
OF := AND_1((bool2bv((t1_517[64:63]) == (t2_518[64:63]))), (XOR_1((t1_517[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_517)), t2_518)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4470:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x4478:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x4480:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_197;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4486:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x448b:
t_525 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_198;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_525, 4bv64)), t_525)), 2bv64)), (XOR_64((RSHIFT_64(t_525, 4bv64)), t_525)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_525, 4bv64)), t_525)), 2bv64)), (XOR_64((RSHIFT_64(t_525, 4bv64)), t_525)))))[1:0]));
SF := t_525[64:63];
ZF := bool2bv(0bv64 == t_525);

label_0x448e:
if (bv2bool(ZF)) {
  goto label_0x4491;
}

label_0x4490:
assume false;

label_0x4491:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x4499:
origDEST_529 := RAX;
origCOUNT_530 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), CF, LSHIFT_64(origDEST_529, (MINUS_64(64bv64, origCOUNT_530)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_530 == 1bv64)), origDEST_529[64:63], unconstrained_199));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_530 == 0bv64)), AF, unconstrained_200);

label_0x449d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x44a4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x44a8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x44b0:
origDEST_535 := RCX;
origCOUNT_536 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), CF, LSHIFT_64(origDEST_535, (MINUS_64(64bv64, origCOUNT_536)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_536 == 1bv64)), origDEST_535[64:63], unconstrained_201));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), AF, unconstrained_202);

label_0x44b4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_203;
SF := unconstrained_204;
AF := unconstrained_205;
PF := unconstrained_206;

label_0x44b8:
if (bv2bool(CF)) {
  goto label_0x44bb;
}

label_0x44ba:
assume false;

label_0x44bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x44c3:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x44c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x44ce:
t1_541 := RAX;
t2_542 := 5100bv64;
RAX := PLUS_64(RAX, t2_542);
CF := bool2bv(LT_64(RAX, t1_541));
OF := AND_1((bool2bv((t1_541[64:63]) == (t2_542[64:63]))), (XOR_1((t1_541[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_541)), t2_542)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x44d4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x44dc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x44e4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x44ea:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x44ef:
t_549 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_208;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)), 2bv64)), (XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)), 2bv64)), (XOR_64((RSHIFT_64(t_549, 4bv64)), t_549)))))[1:0]));
SF := t_549[64:63];
ZF := bool2bv(0bv64 == t_549);

label_0x44f2:
if (bv2bool(ZF)) {
  goto label_0x44f5;
}

label_0x44f4:
assume false;

label_0x44f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x44fd:
origDEST_553 := RAX;
origCOUNT_554 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), CF, LSHIFT_64(origDEST_553, (MINUS_64(64bv64, origCOUNT_554)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_554 == 1bv64)), origDEST_553[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_554 == 0bv64)), AF, unconstrained_210);

label_0x4501:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4508:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x450c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x4514:
origDEST_559 := RCX;
origCOUNT_560 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), CF, LSHIFT_64(origDEST_559, (MINUS_64(64bv64, origCOUNT_560)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_560 == 1bv64)), origDEST_559[64:63], unconstrained_211));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_560 == 0bv64)), AF, unconstrained_212);

label_0x4518:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_213;
SF := unconstrained_214;
AF := unconstrained_215;
PF := unconstrained_216;

label_0x451c:
if (bv2bool(CF)) {
  goto label_0x451f;
}

label_0x451e:
assume false;

label_0x451f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x4527:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x452a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x452f:
t1_565 := RSP;
t2_566 := 184bv64;
RSP := PLUS_64(RSP, t2_566);
CF := bool2bv(LT_64(RSP, t1_565));
OF := AND_1((bool2bv((t1_565[64:63]) == (t2_566[64:63]))), (XOR_1((t1_565[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_565)), t2_566)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x4536:

ra_571 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_100,origCOUNT_122,origCOUNT_128,origCOUNT_148,origCOUNT_154,origCOUNT_16,origCOUNT_176,origCOUNT_182,origCOUNT_202,origCOUNT_208,origCOUNT_22,origCOUNT_230,origCOUNT_236,origCOUNT_252,origCOUNT_258,origCOUNT_280,origCOUNT_286,origCOUNT_304,origCOUNT_310,origCOUNT_328,origCOUNT_334,origCOUNT_346,origCOUNT_352,origCOUNT_370,origCOUNT_376,origCOUNT_394,origCOUNT_400,origCOUNT_418,origCOUNT_424,origCOUNT_44,origCOUNT_442,origCOUNT_448,origCOUNT_478,origCOUNT_484,origCOUNT_50,origCOUNT_506,origCOUNT_512,origCOUNT_530,origCOUNT_536,origCOUNT_554,origCOUNT_560,origCOUNT_94,origDEST_121,origDEST_127,origDEST_147,origDEST_15,origDEST_153,origDEST_175,origDEST_181,origDEST_201,origDEST_207,origDEST_21,origDEST_229,origDEST_235,origDEST_251,origDEST_257,origDEST_279,origDEST_285,origDEST_303,origDEST_309,origDEST_327,origDEST_333,origDEST_345,origDEST_351,origDEST_369,origDEST_375,origDEST_393,origDEST_399,origDEST_417,origDEST_423,origDEST_43,origDEST_441,origDEST_447,origDEST_477,origDEST_483,origDEST_49,origDEST_505,origDEST_511,origDEST_529,origDEST_535,origDEST_553,origDEST_559,origDEST_93,origDEST_99,ra_571,t1_109,t1_163,t1_217,t1_267,t1_291,t1_31,t1_315,t1_357,t1_381,t1_405,t1_429,t1_457,t1_493,t1_517,t1_541,t1_565,t2_110,t2_164,t2_218,t2_268,t2_292,t2_316,t2_32,t2_358,t2_382,t2_406,t2_430,t2_458,t2_494,t2_518,t2_542,t2_566,t_1,t_105,t_11,t_117,t_133,t_137,t_143,t_159,t_171,t_187,t_191,t_197,t_213,t_225,t_241,t_247,t_263,t_27,t_275,t_299,t_323,t_341,t_365,t_389,t_39,t_413,t_437,t_453,t_463,t_467,t_473,t_489,t_5,t_501,t_525,t_549,t_55,t_59,t_63,t_67,t_71,t_75,t_79,t_83,t_89;

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
var origCOUNT_100: bv64;
var origCOUNT_122: bv64;
var origCOUNT_128: bv64;
var origCOUNT_148: bv64;
var origCOUNT_154: bv64;
var origCOUNT_16: bv64;
var origCOUNT_176: bv64;
var origCOUNT_182: bv64;
var origCOUNT_202: bv64;
var origCOUNT_208: bv64;
var origCOUNT_22: bv64;
var origCOUNT_230: bv64;
var origCOUNT_236: bv64;
var origCOUNT_252: bv64;
var origCOUNT_258: bv64;
var origCOUNT_280: bv64;
var origCOUNT_286: bv64;
var origCOUNT_304: bv64;
var origCOUNT_310: bv64;
var origCOUNT_328: bv64;
var origCOUNT_334: bv64;
var origCOUNT_346: bv64;
var origCOUNT_352: bv64;
var origCOUNT_370: bv64;
var origCOUNT_376: bv64;
var origCOUNT_394: bv64;
var origCOUNT_400: bv64;
var origCOUNT_418: bv64;
var origCOUNT_424: bv64;
var origCOUNT_44: bv64;
var origCOUNT_442: bv64;
var origCOUNT_448: bv64;
var origCOUNT_478: bv64;
var origCOUNT_484: bv64;
var origCOUNT_50: bv64;
var origCOUNT_506: bv64;
var origCOUNT_512: bv64;
var origCOUNT_530: bv64;
var origCOUNT_536: bv64;
var origCOUNT_554: bv64;
var origCOUNT_560: bv64;
var origCOUNT_94: bv64;
var origDEST_121: bv64;
var origDEST_127: bv64;
var origDEST_147: bv64;
var origDEST_15: bv64;
var origDEST_153: bv64;
var origDEST_175: bv64;
var origDEST_181: bv64;
var origDEST_201: bv64;
var origDEST_207: bv64;
var origDEST_21: bv64;
var origDEST_229: bv64;
var origDEST_235: bv64;
var origDEST_251: bv64;
var origDEST_257: bv64;
var origDEST_279: bv64;
var origDEST_285: bv64;
var origDEST_303: bv64;
var origDEST_309: bv64;
var origDEST_327: bv64;
var origDEST_333: bv64;
var origDEST_345: bv64;
var origDEST_351: bv64;
var origDEST_369: bv64;
var origDEST_375: bv64;
var origDEST_393: bv64;
var origDEST_399: bv64;
var origDEST_417: bv64;
var origDEST_423: bv64;
var origDEST_43: bv64;
var origDEST_441: bv64;
var origDEST_447: bv64;
var origDEST_477: bv64;
var origDEST_483: bv64;
var origDEST_49: bv64;
var origDEST_505: bv64;
var origDEST_511: bv64;
var origDEST_529: bv64;
var origDEST_535: bv64;
var origDEST_553: bv64;
var origDEST_559: bv64;
var origDEST_93: bv64;
var origDEST_99: bv64;
var ra_571: bv64;
var t1_109: bv64;
var t1_163: bv64;
var t1_217: bv64;
var t1_267: bv64;
var t1_291: bv64;
var t1_31: bv64;
var t1_315: bv64;
var t1_357: bv64;
var t1_381: bv64;
var t1_405: bv64;
var t1_429: bv64;
var t1_457: bv64;
var t1_493: bv64;
var t1_517: bv64;
var t1_541: bv64;
var t1_565: bv64;
var t2_110: bv64;
var t2_164: bv64;
var t2_218: bv64;
var t2_268: bv64;
var t2_292: bv64;
var t2_316: bv64;
var t2_32: bv64;
var t2_358: bv64;
var t2_382: bv64;
var t2_406: bv64;
var t2_430: bv64;
var t2_458: bv64;
var t2_494: bv64;
var t2_518: bv64;
var t2_542: bv64;
var t2_566: bv64;
var t_1: bv64;
var t_105: bv64;
var t_11: bv64;
var t_117: bv64;
var t_133: bv32;
var t_137: bv64;
var t_143: bv64;
var t_159: bv64;
var t_171: bv64;
var t_187: bv64;
var t_191: bv64;
var t_197: bv64;
var t_213: bv64;
var t_225: bv64;
var t_241: bv64;
var t_247: bv64;
var t_263: bv64;
var t_27: bv64;
var t_275: bv64;
var t_299: bv64;
var t_323: bv64;
var t_341: bv64;
var t_365: bv64;
var t_389: bv64;
var t_39: bv64;
var t_413: bv64;
var t_437: bv64;
var t_453: bv32;
var t_463: bv32;
var t_467: bv64;
var t_473: bv64;
var t_489: bv64;
var t_5: bv64;
var t_501: bv64;
var t_525: bv64;
var t_549: bv64;
var t_55: bv32;
var t_59: bv32;
var t_63: bv32;
var t_67: bv32;
var t_71: bv32;
var t_75: bv32;
var t_79: bv32;
var t_83: bv64;
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
