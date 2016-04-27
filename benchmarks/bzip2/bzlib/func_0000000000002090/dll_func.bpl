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
axiom _function_addr_low == 8336bv64;
axiom _function_addr_high == 11024bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2090:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x2095:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x209a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x209e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x20a3:
t_1 := RSP;
RSP := MINUS_64(RSP, 232bv64);
CF := bool2bv(LT_64(t_1, 232bv64));
OF := AND_64((XOR_64(t_1, 232bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 232bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x20aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x20b2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x20b7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 280bv64)));

label_0x20be:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x20c2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), 0bv64);

label_0x20cb:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x20d4:
if (bv2bool(ZF)) {
  goto label_0x2127;
}

label_0x20d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x20de:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x20e4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x20e9:
t_11 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x20ec:
if (bv2bool(ZF)) {
  goto label_0x20ef;
}

label_0x20ee:
assume false;

label_0x20ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x20f7:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_4);

label_0x20fb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2102:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2106:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x210e:
origDEST_21 := RCX;
origCOUNT_22 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, LSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), origDEST_21[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_6);

label_0x2112:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x2116:
if (bv2bool(CF)) {
  goto label_0x2119;
}

label_0x2118:
assume false;

label_0x2119:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2121:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x2127:
t_27 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_27)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_27, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x212d:
if (bv2bool(ZF)) {
  goto label_0x2184;
}

label_0x212f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2134:
t1_31 := RAX;
t2_32 := 5096bv64;
RAX := PLUS_64(RAX, t2_32);
CF := bool2bv(LT_64(RAX, t1_31));
OF := AND_1((bool2bv((t1_31[64:63]) == (t2_32[64:63]))), (XOR_1((t1_31[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_31)), t2_32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x213a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x213f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x2144:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x214a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x214f:
t_39 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)), 2bv64)), (XOR_64((RSHIFT_64(t_39, 4bv64)), t_39)))))[1:0]));
SF := t_39[64:63];
ZF := bool2bv(0bv64 == t_39);

label_0x2152:
if (bv2bool(ZF)) {
  goto label_0x2155;
}

label_0x2154:
assume false;

label_0x2155:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x215a:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0x215e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2165:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2169:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x216e:
origDEST_49 := RCX;
origCOUNT_50 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, LSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), origDEST_49[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_16);

label_0x2172:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x2176:
if (bv2bool(CF)) {
  goto label_0x2179;
}

label_0x2178:
assume false;

label_0x2179:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x217e:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x2184:
t_55 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 248bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 248bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 248bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 248bv64))), t_55)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_55, (LOAD_LE_32(mem, PLUS_64(RSP, 248bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)), 2bv32)), (XOR_32((RSHIFT_32(t_55, 4bv32)), t_55)))))[1:0]));
SF := t_55[32:31];
ZF := bool2bv(0bv32 == t_55);

label_0x218c:
if (bv2bool(ZF)) {
  goto label_0x21e6;
}

label_0x218e:
t_59 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), t_59)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_59, (LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)), 2bv32)), (XOR_32((RSHIFT_32(t_59, 4bv32)), t_59)))))[1:0]));
SF := t_59[32:31];
ZF := bool2bv(0bv32 == t_59);

label_0x2196:
if (bv2bool(ZF)) {
  goto label_0x21a2;
}

label_0x2198:
t_63 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))), t_63)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_63, (LOAD_LE_32(mem, PLUS_64(RSP, 264bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)), 2bv32)), (XOR_32((RSHIFT_32(t_63, 4bv32)), t_63)))))[1:0]));
SF := t_63[32:31];
ZF := bool2bv(0bv32 == t_63);

label_0x21a0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x21e6;
}

label_0x21a2:
t_67 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), t_67)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_67, (LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))))[1:0]));
SF := t_67[32:31];
ZF := bool2bv(0bv32 == t_67);

label_0x21aa:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x21e6;
}

label_0x21ac:
t_71 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))), t_71)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_71, (LOAD_LE_32(mem, PLUS_64(RSP, 256bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)), 2bv32)), (XOR_32((RSHIFT_32(t_71, 4bv32)), t_71)))))[1:0]));
SF := t_71[32:31];
ZF := bool2bv(0bv32 == t_71);

label_0x21b4:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x21e6;
}

label_0x21b6:
t_75 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_75)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_75, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))))[1:0]));
SF := t_75[64:63];
ZF := bool2bv(0bv64 == t_75);

label_0x21bc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x21c5;
}

label_0x21be:
t_79 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_79)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_79, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)), 2bv32)), (XOR_32((RSHIFT_32(t_79, 4bv32)), t_79)))))[1:0]));
SF := t_79[32:31];
ZF := bool2bv(0bv32 == t_79);

label_0x21c3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x21e6;
}

label_0x21c5:
t_83 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_83)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_83, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)), 2bv64)), (XOR_64((RSHIFT_64(t_83, 4bv64)), t_83)))))[1:0]));
SF := t_83[64:63];
ZF := bool2bv(0bv64 == t_83);

label_0x21cb:
if (bv2bool(ZF)) {
  goto label_0x22a6;
}

label_0x21d1:
t_87 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_87)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_87, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))))[1:0]));
SF := t_87[32:31];
ZF := bool2bv(0bv32 == t_87);

label_0x21d6:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x21e6;
}

label_0x21d8:
t_91 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 5000bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 5000bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 5000bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_91)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_91, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 5000bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))))[1:0]));
SF := t_91[32:31];
ZF := bool2bv(0bv32 == t_91);

label_0x21e0:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x22a6;
}

label_0x21e6:
t_95 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_95)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_95, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_95, 4bv64)), t_95)), 2bv64)), (XOR_64((RSHIFT_64(t_95, 4bv64)), t_95)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_95, 4bv64)), t_95)), 2bv64)), (XOR_64((RSHIFT_64(t_95, 4bv64)), t_95)))))[1:0]));
SF := t_95[64:63];
ZF := bool2bv(0bv64 == t_95);

label_0x21ef:
if (bv2bool(ZF)) {
  goto label_0x2242;
}

label_0x21f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x21f9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21ff:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2204:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x2207:
if (bv2bool(ZF)) {
  goto label_0x220a;
}

label_0x2209:
assume false;

label_0x220a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2212:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_24);

label_0x2216:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x221d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2221:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2229:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_26);

label_0x222d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x2231:
if (bv2bool(CF)) {
  goto label_0x2234;
}

label_0x2233:
assume false;

label_0x2234:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x223c:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x2242:
t_117 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_117)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_117, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x2248:
if (bv2bool(ZF)) {
  goto label_0x229f;
}

label_0x224a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x224f:
t1_121 := RAX;
t2_122 := 5096bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2255:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x225a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x225f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2265:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x226a:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x226d:
if (bv2bool(ZF)) {
  goto label_0x2270;
}

label_0x226f:
assume false;

label_0x2270:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2275:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_34);

label_0x2279:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2280:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2284:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2289:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_36);

label_0x228d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x2291:
if (bv2bool(CF)) {
  goto label_0x2294;
}

label_0x2293:
assume false;

label_0x2294:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2299:
mem := STORE_LE_32(mem, RAX, 4294967294bv32);

label_0x229f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_41;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x22a1:
goto label_0x2afc;

label_0x22a6:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x22a8:
t_145 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0x22aa:
if (bv2bool(ZF)) {
  goto label_0x2370;
}

label_0x22b0:
t_149 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_149)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_149, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))))[1:0]));
SF := t_149[64:63];
ZF := bool2bv(0bv64 == t_149);

label_0x22b9:
if (bv2bool(ZF)) {
  goto label_0x230c;
}

label_0x22bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x22c3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x22c9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x22ce:
t_155 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)), 2bv64)), (XOR_64((RSHIFT_64(t_155, 4bv64)), t_155)))))[1:0]));
SF := t_155[64:63];
ZF := bool2bv(0bv64 == t_155);

label_0x22d1:
if (bv2bool(ZF)) {
  goto label_0x22d4;
}

label_0x22d3:
assume false;

label_0x22d4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x22dc:
origDEST_159 := RAX;
origCOUNT_160 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_47);

label_0x22e0:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x22e7:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x22eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x22f3:
origDEST_165 := RCX;
origCOUNT_166 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), CF, LSHIFT_64(origDEST_165, (MINUS_64(64bv64, origCOUNT_166)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_166 == 1bv64)), origDEST_165[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_166 == 0bv64)), AF, unconstrained_49);

label_0x22f7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_50;
SF := unconstrained_51;
AF := unconstrained_52;
PF := unconstrained_53;

label_0x22fb:
if (bv2bool(CF)) {
  goto label_0x22fe;
}

label_0x22fd:
assume false;

label_0x22fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2306:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x230c:
t_171 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_171)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_171, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)), 2bv64)), (XOR_64((RSHIFT_64(t_171, 4bv64)), t_171)))))[1:0]));
SF := t_171[64:63];
ZF := bool2bv(0bv64 == t_171);

label_0x2312:
if (bv2bool(ZF)) {
  goto label_0x2369;
}

label_0x2314:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2319:
t1_175 := RAX;
t2_176 := 5096bv64;
RAX := PLUS_64(RAX, t2_176);
CF := bool2bv(LT_64(RAX, t1_175));
OF := AND_1((bool2bv((t1_175[64:63]) == (t2_176[64:63]))), (XOR_1((t1_175[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_175)), t2_176)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x231f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x2324:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2329:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x232f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2334:
t_183 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))))[1:0]));
SF := t_183[64:63];
ZF := bool2bv(0bv64 == t_183);

label_0x2337:
if (bv2bool(ZF)) {
  goto label_0x233a;
}

label_0x2339:
assume false;

label_0x233a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x233f:
origDEST_187 := RAX;
origCOUNT_188 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_57);

label_0x2343:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x234a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x234e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2353:
origDEST_193 := RCX;
origCOUNT_194 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), CF, LSHIFT_64(origDEST_193, (MINUS_64(64bv64, origCOUNT_194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_194 == 1bv64)), origDEST_193[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), AF, unconstrained_59);

label_0x2357:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_60;
SF := unconstrained_61;
AF := unconstrained_62;
PF := unconstrained_63;

label_0x235b:
if (bv2bool(CF)) {
  goto label_0x235e;
}

label_0x235d:
assume false;

label_0x235e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2363:
mem := STORE_LE_32(mem, RAX, 4294967290bv32);

label_0x2369:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_64;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x236b:
goto label_0x2afc;

label_0x2370:
RCX := (0bv32 ++ 5104bv32);

label_0x2375:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 9082bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x237a"} true;
call arbitrary_func();

label_0x237a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x237f:
t_199 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_199)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_199, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)), 2bv64)), (XOR_64((RSHIFT_64(t_199, 4bv64)), t_199)))))[1:0]));
SF := t_199[64:63];
ZF := bool2bv(0bv64 == t_199);

label_0x2385:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x244b;
}

label_0x238b:
t_203 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_203)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_203, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)), 2bv64)), (XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)), 2bv64)), (XOR_64((RSHIFT_64(t_203, 4bv64)), t_203)))))[1:0]));
SF := t_203[64:63];
ZF := bool2bv(0bv64 == t_203);

label_0x2394:
if (bv2bool(ZF)) {
  goto label_0x23e7;
}

label_0x2396:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x239e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_65;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x23a4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x23a9:
t_209 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_66;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)), 2bv64)), (XOR_64((RSHIFT_64(t_209, 4bv64)), t_209)))))[1:0]));
SF := t_209[64:63];
ZF := bool2bv(0bv64 == t_209);

label_0x23ac:
if (bv2bool(ZF)) {
  goto label_0x23af;
}

label_0x23ae:
assume false;

label_0x23af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x23b7:
origDEST_213 := RAX;
origCOUNT_214 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), CF, LSHIFT_64(origDEST_213, (MINUS_64(64bv64, origCOUNT_214)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_214 == 1bv64)), origDEST_213[64:63], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_214 == 0bv64)), AF, unconstrained_68);

label_0x23bb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x23c2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x23c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x23ce:
origDEST_219 := RCX;
origCOUNT_220 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), CF, LSHIFT_64(origDEST_219, (MINUS_64(64bv64, origCOUNT_220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv64)), origDEST_219[64:63], unconstrained_69));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv64)), AF, unconstrained_70);

label_0x23d2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_71;
SF := unconstrained_72;
AF := unconstrained_73;
PF := unconstrained_74;

label_0x23d6:
if (bv2bool(CF)) {
  goto label_0x23d9;
}

label_0x23d8:
assume false;

label_0x23d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x23e1:
mem := STORE_LE_32(mem, RAX, 4294967293bv32);

label_0x23e7:
t_225 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_225)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_225, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)), 2bv64)), (XOR_64((RSHIFT_64(t_225, 4bv64)), t_225)))))[1:0]));
SF := t_225[64:63];
ZF := bool2bv(0bv64 == t_225);

label_0x23ed:
if (bv2bool(ZF)) {
  goto label_0x2444;
}

label_0x23ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x23f4:
t1_229 := RAX;
t2_230 := 5096bv64;
RAX := PLUS_64(RAX, t2_230);
CF := bool2bv(LT_64(RAX, t1_229));
OF := AND_1((bool2bv((t1_229[64:63]) == (t2_230[64:63]))), (XOR_1((t1_229[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_229)), t2_230)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x23fa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x23ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2404:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x240a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x240f:
t_237 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_76;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)), 2bv64)), (XOR_64((RSHIFT_64(t_237, 4bv64)), t_237)))))[1:0]));
SF := t_237[64:63];
ZF := bool2bv(0bv64 == t_237);

label_0x2412:
if (bv2bool(ZF)) {
  goto label_0x2415;
}

label_0x2414:
assume false;

label_0x2415:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x241a:
origDEST_241 := RAX;
origCOUNT_242 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), CF, LSHIFT_64(origDEST_241, (MINUS_64(64bv64, origCOUNT_242)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_242 == 1bv64)), origDEST_241[64:63], unconstrained_77));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_242 == 0bv64)), AF, unconstrained_78);

label_0x241e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2425:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2429:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x242e:
origDEST_247 := RCX;
origCOUNT_248 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), CF, LSHIFT_64(origDEST_247, (MINUS_64(64bv64, origCOUNT_248)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_248 == 1bv64)), origDEST_247[64:63], unconstrained_79));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_248 == 0bv64)), AF, unconstrained_80);

label_0x2432:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_81;
SF := unconstrained_82;
AF := unconstrained_83;
PF := unconstrained_84;

label_0x2436:
if (bv2bool(CF)) {
  goto label_0x2439;
}

label_0x2438:
assume false;

label_0x2439:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x243e:
mem := STORE_LE_32(mem, RAX, 4294967293bv32);

label_0x2444:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_85;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2446:
goto label_0x2afc;

label_0x244b:
t_253 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_253)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_253, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))))[1:0]));
SF := t_253[64:63];
ZF := bool2bv(0bv64 == t_253);

label_0x2454:
if (bv2bool(ZF)) {
  goto label_0x24a7;
}

label_0x2456:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x245e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2464:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2469:
t_259 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_87;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)), 2bv64)), (XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)), 2bv64)), (XOR_64((RSHIFT_64(t_259, 4bv64)), t_259)))))[1:0]));
SF := t_259[64:63];
ZF := bool2bv(0bv64 == t_259);

label_0x246c:
if (bv2bool(ZF)) {
  goto label_0x246f;
}

label_0x246e:
assume false;

label_0x246f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2477:
origDEST_263 := RAX;
origCOUNT_264 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_88));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_89);

label_0x247b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2482:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2486:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x248e:
origDEST_269 := RCX;
origCOUNT_270 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), CF, LSHIFT_64(origDEST_269, (MINUS_64(64bv64, origCOUNT_270)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_270 == 1bv64)), origDEST_269[64:63], unconstrained_90));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_270 == 0bv64)), AF, unconstrained_91);

label_0x2492:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_92;
SF := unconstrained_93;
AF := unconstrained_94;
PF := unconstrained_95;

label_0x2496:
if (bv2bool(CF)) {
  goto label_0x2499;
}

label_0x2498:
assume false;

label_0x2499:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x24a1:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x24a7:
t_275 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_275)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_275, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)), 2bv64)), (XOR_64((RSHIFT_64(t_275, 4bv64)), t_275)))))[1:0]));
SF := t_275[64:63];
ZF := bool2bv(0bv64 == t_275);

label_0x24ad:
if (bv2bool(ZF)) {
  goto label_0x2504;
}

label_0x24af:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x24b4:
t1_279 := RAX;
t2_280 := 5096bv64;
RAX := PLUS_64(RAX, t2_280);
CF := bool2bv(LT_64(RAX, t1_279));
OF := AND_1((bool2bv((t1_279[64:63]) == (t2_280[64:63]))), (XOR_1((t1_279[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_279)), t2_280)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x24ba:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x24bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24c4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_96;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x24ca:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x24cf:
t_287 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_97;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)), 2bv64)), (XOR_64((RSHIFT_64(t_287, 4bv64)), t_287)))))[1:0]));
SF := t_287[64:63];
ZF := bool2bv(0bv64 == t_287);

label_0x24d2:
if (bv2bool(ZF)) {
  goto label_0x24d5;
}

label_0x24d4:
assume false;

label_0x24d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24da:
origDEST_291 := RAX;
origCOUNT_292 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_98));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_99);

label_0x24de:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x24e5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x24e9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24ee:
origDEST_297 := RCX;
origCOUNT_298 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), CF, LSHIFT_64(origDEST_297, (MINUS_64(64bv64, origCOUNT_298)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_298 == 1bv64)), origDEST_297[64:63], unconstrained_100));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_298 == 0bv64)), AF, unconstrained_101);

label_0x24f2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_102;
SF := unconstrained_103;
AF := unconstrained_104;
PF := unconstrained_105;

label_0x24f6:
if (bv2bool(CF)) {
  goto label_0x24f9;
}

label_0x24f8:
assume false;

label_0x24f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x24fe:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x2504:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2509:
t1_303 := RAX;
t2_304 := 5100bv64;
RAX := PLUS_64(RAX, t2_304);
CF := bool2bv(LT_64(RAX, t1_303));
OF := AND_1((bool2bv((t1_303[64:63]) == (t2_304[64:63]))), (XOR_1((t1_303[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_303)), t2_304)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x250f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x2514:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2519:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_106;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x251f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2524:
t_311 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_107;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)), 2bv64)), (XOR_64((RSHIFT_64(t_311, 4bv64)), t_311)))))[1:0]));
SF := t_311[64:63];
ZF := bool2bv(0bv64 == t_311);

label_0x2527:
if (bv2bool(ZF)) {
  goto label_0x252a;
}

label_0x2529:
assume false;

label_0x252a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x252f:
origDEST_315 := RAX;
origCOUNT_316 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_108));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_109);

label_0x2533:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x253a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x253e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2543:
origDEST_321 := RCX;
origCOUNT_322 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), CF, LSHIFT_64(origDEST_321, (MINUS_64(64bv64, origCOUNT_322)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_322 == 1bv64)), origDEST_321[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_322 == 0bv64)), AF, unconstrained_111);

label_0x2547:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_112;
SF := unconstrained_113;
AF := unconstrained_114;
PF := unconstrained_115;

label_0x254b:
if (bv2bool(CF)) {
  goto label_0x254e;
}

label_0x254d:
assume false;

label_0x254e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2553:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x2556:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x255b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x2560:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x2565:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_116;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x256b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2570:
t_329 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_117;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)), 2bv64)), (XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)), 2bv64)), (XOR_64((RSHIFT_64(t_329, 4bv64)), t_329)))))[1:0]));
SF := t_329[64:63];
ZF := bool2bv(0bv64 == t_329);

label_0x2573:
if (bv2bool(ZF)) {
  goto label_0x2576;
}

label_0x2575:
assume false;

label_0x2576:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x257b:
origDEST_333 := RAX;
origCOUNT_334 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), CF, LSHIFT_64(origDEST_333, (MINUS_64(64bv64, origCOUNT_334)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_334 == 1bv64)), origDEST_333[64:63], unconstrained_118));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_334 == 0bv64)), AF, unconstrained_119);

label_0x257f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2586:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x258a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x258f:
origDEST_339 := RCX;
origCOUNT_340 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), CF, LSHIFT_64(origDEST_339, (MINUS_64(64bv64, origCOUNT_340)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_340 == 1bv64)), origDEST_339[64:63], unconstrained_120));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_340 == 0bv64)), AF, unconstrained_121);

label_0x2593:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_122;
SF := unconstrained_123;
AF := unconstrained_124;
PF := unconstrained_125;

label_0x2597:
if (bv2bool(CF)) {
  goto label_0x259a;
}

label_0x2599:
assume false;

label_0x259a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x259f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 248bv64)));

label_0x25a6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x25a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x25ad:
t1_345 := RAX;
t2_346 := 5004bv64;
RAX := PLUS_64(RAX, t2_346);
CF := bool2bv(LT_64(RAX, t1_345));
OF := AND_1((bool2bv((t1_345[64:63]) == (t2_346[64:63]))), (XOR_1((t1_345[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_345)), t2_346)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25b3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x25b8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x25bd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_126;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25c3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x25c8:
t_353 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_127;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_353, 4bv64)), t_353)), 2bv64)), (XOR_64((RSHIFT_64(t_353, 4bv64)), t_353)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_353, 4bv64)), t_353)), 2bv64)), (XOR_64((RSHIFT_64(t_353, 4bv64)), t_353)))))[1:0]));
SF := t_353[64:63];
ZF := bool2bv(0bv64 == t_353);

label_0x25cb:
if (bv2bool(ZF)) {
  goto label_0x25ce;
}

label_0x25cd:
assume false;

label_0x25ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x25d3:
origDEST_357 := RAX;
origCOUNT_358 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), CF, LSHIFT_64(origDEST_357, (MINUS_64(64bv64, origCOUNT_358)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_358 == 1bv64)), origDEST_357[64:63], unconstrained_128));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_358 == 0bv64)), AF, unconstrained_129);

label_0x25d7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x25de:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x25e2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x25e7:
origDEST_363 := RCX;
origCOUNT_364 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), CF, LSHIFT_64(origDEST_363, (MINUS_64(64bv64, origCOUNT_364)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_364 == 1bv64)), origDEST_363[64:63], unconstrained_130));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_364 == 0bv64)), AF, unconstrained_131);

label_0x25eb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_132;
SF := unconstrained_133;
AF := unconstrained_134;
PF := unconstrained_135;

label_0x25ef:
if (bv2bool(CF)) {
  goto label_0x25f2;
}

label_0x25f1:
assume false;

label_0x25f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x25f7:
mem := STORE_LE_32(mem, RAX, 0bv32);

label_0x25fd:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2602:
t1_369 := RAX;
t2_370 := 5008bv64;
RAX := PLUS_64(RAX, t2_370);
CF := bool2bv(LT_64(RAX, t1_369));
OF := AND_1((bool2bv((t1_369[64:63]) == (t2_370[64:63]))), (XOR_1((t1_369[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_369)), t2_370)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2608:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x260d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x2612:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_136;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2618:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x261d:
t_377 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_137;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_377, 4bv64)), t_377)), 2bv64)), (XOR_64((RSHIFT_64(t_377, 4bv64)), t_377)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_377, 4bv64)), t_377)), 2bv64)), (XOR_64((RSHIFT_64(t_377, 4bv64)), t_377)))))[1:0]));
SF := t_377[64:63];
ZF := bool2bv(0bv64 == t_377);

label_0x2620:
if (bv2bool(ZF)) {
  goto label_0x2623;
}

label_0x2622:
assume false;

label_0x2623:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x2628:
origDEST_381 := RAX;
origCOUNT_382 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), CF, LSHIFT_64(origDEST_381, (MINUS_64(64bv64, origCOUNT_382)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_382 == 1bv64)), origDEST_381[64:63], unconstrained_138));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_382 == 0bv64)), AF, unconstrained_139);

label_0x262c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2633:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2637:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x263c:
origDEST_387 := RCX;
origCOUNT_388 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), CF, LSHIFT_64(origDEST_387, (MINUS_64(64bv64, origCOUNT_388)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_388 == 1bv64)), origDEST_387[64:63], unconstrained_140));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_388 == 0bv64)), AF, unconstrained_141);

label_0x2640:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_142;
SF := unconstrained_143;
AF := unconstrained_144;
PF := unconstrained_145;

label_0x2644:
if (bv2bool(CF)) {
  goto label_0x2647;
}

label_0x2646:
assume false;

label_0x2647:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x264c:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x264f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2654:
t1_393 := RAX;
t2_394 := 5072bv64;
RAX := PLUS_64(RAX, t2_394);
CF := bool2bv(LT_64(RAX, t1_393));
OF := AND_1((bool2bv((t1_393[64:63]) == (t2_394[64:63]))), (XOR_1((t1_393[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_393)), t2_394)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x265a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x2662:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x266a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_146;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2670:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2675:
t_401 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_147;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)), 2bv64)), (XOR_64((RSHIFT_64(t_401, 4bv64)), t_401)))))[1:0]));
SF := t_401[64:63];
ZF := bool2bv(0bv64 == t_401);

label_0x2678:
if (bv2bool(ZF)) {
  goto label_0x267b;
}

label_0x267a:
assume false;

label_0x267b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2683:
origDEST_405 := RAX;
origCOUNT_406 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), CF, LSHIFT_64(origDEST_405, (MINUS_64(64bv64, origCOUNT_406)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_406 == 1bv64)), origDEST_405[64:63], unconstrained_148));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_406 == 0bv64)), AF, unconstrained_149);

label_0x2687:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x268e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2692:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x269a:
origDEST_411 := RCX;
origCOUNT_412 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), CF, LSHIFT_64(origDEST_411, (MINUS_64(64bv64, origCOUNT_412)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_412 == 1bv64)), origDEST_411[64:63], unconstrained_150));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_412 == 0bv64)), AF, unconstrained_151);

label_0x269e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_152;
SF := unconstrained_153;
AF := unconstrained_154;
PF := unconstrained_155;

label_0x26a2:
if (bv2bool(CF)) {
  goto label_0x26a5;
}

label_0x26a4:
assume false;

label_0x26a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x26ad:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x26b4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x26b9:
t1_417 := RAX;
t2_418 := 5080bv64;
RAX := PLUS_64(RAX, t2_418);
CF := bool2bv(LT_64(RAX, t1_417));
OF := AND_1((bool2bv((t1_417[64:63]) == (t2_418[64:63]))), (XOR_1((t1_417[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_417)), t2_418)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26bf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x26c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x26cf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_156;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26d5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x26da:
t_425 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_157;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)), 2bv64)), (XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)), 2bv64)), (XOR_64((RSHIFT_64(t_425, 4bv64)), t_425)))))[1:0]));
SF := t_425[64:63];
ZF := bool2bv(0bv64 == t_425);

label_0x26dd:
if (bv2bool(ZF)) {
  goto label_0x26e0;
}

label_0x26df:
assume false;

label_0x26e0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x26e8:
origDEST_429 := RAX;
origCOUNT_430 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), CF, LSHIFT_64(origDEST_429, (MINUS_64(64bv64, origCOUNT_430)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_430 == 1bv64)), origDEST_429[64:63], unconstrained_158));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_430 == 0bv64)), AF, unconstrained_159);

label_0x26ec:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x26f3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x26f7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x26ff:
origDEST_435 := RCX;
origCOUNT_436 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), CF, LSHIFT_64(origDEST_435, (MINUS_64(64bv64, origCOUNT_436)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_436 == 1bv64)), origDEST_435[64:63], unconstrained_160));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_436 == 0bv64)), AF, unconstrained_161);

label_0x2703:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_162;
SF := unconstrained_163;
AF := unconstrained_164;
PF := unconstrained_165;

label_0x2707:
if (bv2bool(CF)) {
  goto label_0x270a;
}

label_0x2709:
assume false;

label_0x270a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x2712:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x2719:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x271e:
t1_441 := RAX;
t2_442 := 5088bv64;
RAX := PLUS_64(RAX, t2_442);
CF := bool2bv(LT_64(RAX, t1_441));
OF := AND_1((bool2bv((t1_441[64:63]) == (t2_442[64:63]))), (XOR_1((t1_441[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_441)), t2_442)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2724:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x272c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2734:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_166;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x273a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x273f:
t_449 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)), 2bv64)), (XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)), 2bv64)), (XOR_64((RSHIFT_64(t_449, 4bv64)), t_449)))))[1:0]));
SF := t_449[64:63];
ZF := bool2bv(0bv64 == t_449);

label_0x2742:
if (bv2bool(ZF)) {
  goto label_0x2745;
}

label_0x2744:
assume false;

label_0x2745:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x274d:
origDEST_453 := RAX;
origCOUNT_454 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), CF, LSHIFT_64(origDEST_453, (MINUS_64(64bv64, origCOUNT_454)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_454 == 1bv64)), origDEST_453[64:63], unconstrained_168));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_454 == 0bv64)), AF, unconstrained_169);

label_0x2751:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2758:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x275c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2764:
origDEST_459 := RCX;
origCOUNT_460 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), CF, LSHIFT_64(origDEST_459, (MINUS_64(64bv64, origCOUNT_460)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_460 == 1bv64)), origDEST_459[64:63], unconstrained_170));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_460 == 0bv64)), AF, unconstrained_171);

label_0x2768:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_172;
SF := unconstrained_173;
AF := unconstrained_174;
PF := unconstrained_175;

label_0x276c:
if (bv2bool(CF)) {
  goto label_0x276f;
}

label_0x276e:
assume false;

label_0x276f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2777:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x277e:
t_465 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_465)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_465, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)), 2bv32)), (XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)), 2bv32)), (XOR_32((RSHIFT_32(t_465, 4bv32)), t_465)))))[1:0]));
SF := t_465[32:31];
ZF := bool2bv(0bv32 == t_465);

label_0x2783:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2895;
}

label_0x2789:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x278e:
t1_469 := RAX;
t2_470 := 4bv64;
RAX := PLUS_64(RAX, t2_470);
CF := bool2bv(LT_64(RAX, t1_469));
OF := AND_1((bool2bv((t1_469[64:63]) == (t2_470[64:63]))), (XOR_1((t1_469[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_469)), t2_470)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2792:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2797:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RCX, 5004bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 5004bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 5004bv64)))));

label_0x279e:
t1_475 := RAX;
t2_476 := RCX;
RAX := PLUS_64(RAX, t2_476);
CF := bool2bv(LT_64(RAX, t1_475));
OF := AND_1((bool2bv((t1_475[64:63]) == (t2_476[64:63]))), (XOR_1((t1_475[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_475)), t2_476)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x27a1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x27a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x27b1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x27b7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x27bc:
t_483 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_483, 4bv64)), t_483)), 2bv64)), (XOR_64((RSHIFT_64(t_483, 4bv64)), t_483)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_483, 4bv64)), t_483)), 2bv64)), (XOR_64((RSHIFT_64(t_483, 4bv64)), t_483)))))[1:0]));
SF := t_483[64:63];
ZF := bool2bv(0bv64 == t_483);

label_0x27bf:
if (bv2bool(ZF)) {
  goto label_0x27c2;
}

label_0x27c1:
assume false;

label_0x27c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x27ca:
origDEST_487 := RAX;
origCOUNT_488 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), CF, LSHIFT_64(origDEST_487, (MINUS_64(64bv64, origCOUNT_488)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_488 == 1bv64)), origDEST_487[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_488 == 0bv64)), AF, unconstrained_179);

label_0x27ce:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x27d5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x27d9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x27e1:
origDEST_493 := RCX;
origCOUNT_494 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), CF, LSHIFT_64(origDEST_493, (MINUS_64(64bv64, origCOUNT_494)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_494 == 1bv64)), origDEST_493[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_494 == 0bv64)), AF, unconstrained_181);

label_0x27e5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_182;
SF := unconstrained_183;
AF := unconstrained_184;
PF := unconstrained_185;

label_0x27e9:
if (bv2bool(CF)) {
  goto label_0x27ec;
}

label_0x27eb:
assume false;

label_0x27ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x27f4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x27f9:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RCX)));

label_0x27fc:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x27fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2803:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 5004bv64)));

label_0x2809:
t_499 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_499[32:31]) == (1bv32[32:31]))), (XOR_1((t_499[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_499)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x280b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 200bv64), RAX[32:0]);

label_0x2812:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2817:
t1_503 := RAX;
t2_504 := 5004bv64;
RAX := PLUS_64(RAX, t2_504);
CF := bool2bv(LT_64(RAX, t1_503));
OF := AND_1((bool2bv((t1_503[64:63]) == (t2_504[64:63]))), (XOR_1((t1_503[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_503)), t2_504)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x281d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x2825:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x282d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2833:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2838:
t_511 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_511, 4bv64)), t_511)), 2bv64)), (XOR_64((RSHIFT_64(t_511, 4bv64)), t_511)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_511, 4bv64)), t_511)), 2bv64)), (XOR_64((RSHIFT_64(t_511, 4bv64)), t_511)))))[1:0]));
SF := t_511[64:63];
ZF := bool2bv(0bv64 == t_511);

label_0x283b:
if (bv2bool(ZF)) {
  goto label_0x283e;
}

label_0x283d:
assume false;

label_0x283e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2846:
origDEST_515 := RAX;
origCOUNT_516 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), CF, LSHIFT_64(origDEST_515, (MINUS_64(64bv64, origCOUNT_516)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_516 == 1bv64)), origDEST_515[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_516 == 0bv64)), AF, unconstrained_189);

label_0x284a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2851:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2855:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x285d:
origDEST_521 := RCX;
origCOUNT_522 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), CF, LSHIFT_64(origDEST_521, (MINUS_64(64bv64, origCOUNT_522)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_522 == 1bv64)), origDEST_521[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_522 == 0bv64)), AF, unconstrained_191);

label_0x2861:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_192;
SF := unconstrained_193;
AF := unconstrained_194;
PF := unconstrained_195;

label_0x2865:
if (bv2bool(CF)) {
  goto label_0x2868;
}

label_0x2867:
assume false;

label_0x2868:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2870:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x2877:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2879:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x287e:
t_527 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_527[64:63]) == (1bv64[64:63]))), (XOR_1((t_527[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_527)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2881:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x2886:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x288a:
t_531 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_531, 1bv32)), (XOR_32(t_531, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_531)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x288c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x2890:
goto label_0x277e;

label_0x2895:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x289a:
t1_535 := RAX;
t2_536 := 5016bv64;
RAX := PLUS_64(RAX, t2_536);
CF := bool2bv(LT_64(RAX, t1_535));
OF := AND_1((bool2bv((t1_535[64:63]) == (t2_536[64:63]))), (XOR_1((t1_535[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_535)), t2_536)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x28a0:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 264bv64)));

label_0x28a8:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 256bv64)));

label_0x28af:
RCX := RAX;

label_0x28b2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10423bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x28b7"} true;
call arbitrary_func();

label_0x28b7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x28bb:
t_541 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_541)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_541, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)), 2bv32)), (XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)), 2bv32)), (XOR_32((RSHIFT_32(t_541, 4bv32)), t_541)))))[1:0]));
SF := t_541[32:31];
ZF := bool2bv(0bv32 == t_541);

label_0x28c0:
if (bv2bool(ZF)) {
  goto label_0x299f;
}

label_0x28c6:
t_545 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))), t_545)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_545, (LOAD_LE_64(mem, PLUS_64(RSP, 240bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_545, 4bv64)), t_545)), 2bv64)), (XOR_64((RSHIFT_64(t_545, 4bv64)), t_545)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_545, 4bv64)), t_545)), 2bv64)), (XOR_64((RSHIFT_64(t_545, 4bv64)), t_545)))))[1:0]));
SF := t_545[64:63];
ZF := bool2bv(0bv64 == t_545);

label_0x28cf:
if (bv2bool(ZF)) {
  goto label_0x2922;
}

label_0x28d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x28d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_196;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x28df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x28e4:
t_551 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_197;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)), 2bv64)), (XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)), 2bv64)), (XOR_64((RSHIFT_64(t_551, 4bv64)), t_551)))))[1:0]));
SF := t_551[64:63];
ZF := bool2bv(0bv64 == t_551);

label_0x28e7:
if (bv2bool(ZF)) {
  goto label_0x28ea;
}

label_0x28e9:
assume false;

label_0x28ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x28f2:
origDEST_555 := RAX;
origCOUNT_556 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), CF, LSHIFT_64(origDEST_555, (MINUS_64(64bv64, origCOUNT_556)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_556 == 1bv64)), origDEST_555[64:63], unconstrained_198));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_556 == 0bv64)), AF, unconstrained_199);

label_0x28f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x28fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2901:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2909:
origDEST_561 := RCX;
origCOUNT_562 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), CF, LSHIFT_64(origDEST_561, (MINUS_64(64bv64, origCOUNT_562)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_562 == 1bv64)), origDEST_561[64:63], unconstrained_200));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_562 == 0bv64)), AF, unconstrained_201);

label_0x290d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_202;
SF := unconstrained_203;
AF := unconstrained_204;
PF := unconstrained_205;

label_0x2911:
if (bv2bool(CF)) {
  goto label_0x2914;
}

label_0x2913:
assume false;

label_0x2914:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x291c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x2920:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2922:
t_567 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_567)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_567, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)), 2bv64)), (XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)), 2bv64)), (XOR_64((RSHIFT_64(t_567, 4bv64)), t_567)))))[1:0]));
SF := t_567[64:63];
ZF := bool2bv(0bv64 == t_567);

label_0x2928:
if (bv2bool(ZF)) {
  goto label_0x298e;
}

label_0x292a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x292f:
t1_571 := RAX;
t2_572 := 5096bv64;
RAX := PLUS_64(RAX, t2_572);
CF := bool2bv(LT_64(RAX, t1_571));
OF := AND_1((bool2bv((t1_571[64:63]) == (t2_572[64:63]))), (XOR_1((t1_571[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_571)), t2_572)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2935:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x293d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2945:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_206;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x294b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2950:
t_579 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)), 2bv64)), (XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)), 2bv64)), (XOR_64((RSHIFT_64(t_579, 4bv64)), t_579)))))[1:0]));
SF := t_579[64:63];
ZF := bool2bv(0bv64 == t_579);

label_0x2953:
if (bv2bool(ZF)) {
  goto label_0x2956;
}

label_0x2955:
assume false;

label_0x2956:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x295e:
origDEST_583 := RAX;
origCOUNT_584 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), CF, LSHIFT_64(origDEST_583, (MINUS_64(64bv64, origCOUNT_584)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_584 == 1bv64)), origDEST_583[64:63], unconstrained_208));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_584 == 0bv64)), AF, unconstrained_209);

label_0x2962:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2969:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x296d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2975:
origDEST_589 := RCX;
origCOUNT_590 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), CF, LSHIFT_64(origDEST_589, (MINUS_64(64bv64, origCOUNT_590)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_590 == 1bv64)), origDEST_589[64:63], unconstrained_210));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_590 == 0bv64)), AF, unconstrained_211);

label_0x2979:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_212;
SF := unconstrained_213;
AF := unconstrained_214;
PF := unconstrained_215;

label_0x297d:
if (bv2bool(CF)) {
  goto label_0x2980;
}

label_0x297f:
assume false;

label_0x2980:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2988:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x298c:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x298e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2993:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10648bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2998"} true;
call arbitrary_func();

label_0x2998:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_216;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x299a:
goto label_0x2afc;

label_0x299f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x29a4:
t1_595 := RAX;
t2_596 := 5004bv64;
RAX := PLUS_64(RAX, t2_596);
CF := bool2bv(LT_64(RAX, t1_595));
OF := AND_1((bool2bv((t1_595[64:63]) == (t2_596[64:63]))), (XOR_1((t1_595[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_595)), t2_596)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x29b2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x29b7:
t1_601 := RAX;
t2_602 := 5024bv64;
RAX := PLUS_64(RAX, t2_602);
CF := bool2bv(LT_64(RAX, t1_601));
OF := AND_1((bool2bv((t1_601[64:63]) == (t2_602[64:63]))), (XOR_1((t1_601[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_601)), t2_602)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29bd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x29c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x29cd:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_217;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x29d3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x29d8:
t_609 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_218;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)), 2bv64)), (XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)), 2bv64)), (XOR_64((RSHIFT_64(t_609, 4bv64)), t_609)))))[1:0]));
SF := t_609[64:63];
ZF := bool2bv(0bv64 == t_609);

label_0x29db:
if (bv2bool(ZF)) {
  goto label_0x29de;
}

label_0x29dd:
assume false;

label_0x29de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x29e6:
origDEST_613 := RAX;
origCOUNT_614 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), CF, LSHIFT_64(origDEST_613, (MINUS_64(64bv64, origCOUNT_614)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_614 == 1bv64)), origDEST_613[64:63], unconstrained_219));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_614 == 0bv64)), AF, unconstrained_220);

label_0x29ea:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x29f1:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x29f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x29fd:
origDEST_619 := RCX;
origCOUNT_620 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), CF, LSHIFT_64(origDEST_619, (MINUS_64(64bv64, origCOUNT_620)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_620 == 1bv64)), origDEST_619[64:63], unconstrained_221));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_620 == 0bv64)), AF, unconstrained_222);

label_0x2a01:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_223;
SF := unconstrained_224;
AF := unconstrained_225;
PF := unconstrained_226;

label_0x2a05:
if (bv2bool(CF)) {
  goto label_0x2a08;
}

label_0x2a07:
assume false;

label_0x2a08:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2a10:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x2a18:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x2a1a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2a1c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2a21:
t1_625 := RAX;
t2_626 := 4bv64;
RAX := PLUS_64(RAX, t2_626);
CF := bool2bv(LT_64(RAX, t1_625));
OF := AND_1((bool2bv((t1_625[64:63]) == (t2_626[64:63]))), (XOR_1((t1_625[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_625)), t2_626)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a25:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x2a2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2a32:
t1_631 := RAX;
t2_632 := 5016bv64;
RAX := PLUS_64(RAX, t2_632);
CF := bool2bv(LT_64(RAX, t1_631));
OF := AND_1((bool2bv((t1_631[64:63]) == (t2_632[64:63]))), (XOR_1((t1_631[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_631)), t2_632)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a38:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x2a40:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x2a48:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_227;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a4e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2a53:
t_639 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_228;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)), 2bv64)), (XOR_64((RSHIFT_64(t_639, 4bv64)), t_639)))))[1:0]));
SF := t_639[64:63];
ZF := bool2bv(0bv64 == t_639);

label_0x2a56:
if (bv2bool(ZF)) {
  goto label_0x2a59;
}

label_0x2a58:
assume false;

label_0x2a59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x2a61:
origDEST_643 := RAX;
origCOUNT_644 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), CF, LSHIFT_64(origDEST_643, (MINUS_64(64bv64, origCOUNT_644)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_644 == 1bv64)), origDEST_643[64:63], unconstrained_229));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_644 == 0bv64)), AF, unconstrained_230);

label_0x2a65:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2a6c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2a70:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x2a78:
origDEST_649 := RCX;
origCOUNT_650 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), CF, LSHIFT_64(origDEST_649, (MINUS_64(64bv64, origCOUNT_650)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_650 == 1bv64)), origDEST_649[64:63], unconstrained_231));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_650 == 0bv64)), AF, unconstrained_232);

label_0x2a7c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_233;
SF := unconstrained_234;
AF := unconstrained_235;
PF := unconstrained_236;

label_0x2a80:
if (bv2bool(CF)) {
  goto label_0x2a83;
}

label_0x2a82:
assume false;

label_0x2a83:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x2a8b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x2a93:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2a96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2a9b:
t1_655 := RAX;
t2_656 := 5100bv64;
RAX := PLUS_64(RAX, t2_656);
CF := bool2bv(LT_64(RAX, t1_655));
OF := AND_1((bool2bv((t1_655[64:63]) == (t2_656[64:63]))), (XOR_1((t1_655[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_655)), t2_656)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2aa1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RAX);

label_0x2aa9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2ab1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_237;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ab7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2abc:
t_663 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_238;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)), 2bv64)), (XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)), 2bv64)), (XOR_64((RSHIFT_64(t_663, 4bv64)), t_663)))))[1:0]));
SF := t_663[64:63];
ZF := bool2bv(0bv64 == t_663);

label_0x2abf:
if (bv2bool(ZF)) {
  goto label_0x2ac2;
}

label_0x2ac1:
assume false;

label_0x2ac2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2aca:
origDEST_667 := RAX;
origCOUNT_668 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), CF, LSHIFT_64(origDEST_667, (MINUS_64(64bv64, origCOUNT_668)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_668 == 1bv64)), origDEST_667[64:63], unconstrained_239));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_668 == 0bv64)), AF, unconstrained_240);

label_0x2ace:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2ad5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2ad9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2ae1:
origDEST_673 := RCX;
origCOUNT_674 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), CF, LSHIFT_64(origDEST_673, (MINUS_64(64bv64, origCOUNT_674)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_674 == 1bv64)), origDEST_673[64:63], unconstrained_241));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_674 == 0bv64)), AF, unconstrained_242);

label_0x2ae5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_243;
SF := unconstrained_244;
AF := unconstrained_245;
PF := unconstrained_246;

label_0x2ae9:
if (bv2bool(CF)) {
  goto label_0x2aec;
}

label_0x2aeb:
assume false;

label_0x2aec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x2af4:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x2af7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2afc:
t1_679 := RSP;
t2_680 := 232bv64;
RSP := PLUS_64(RSP, t2_680);
CF := bool2bv(LT_64(RSP, t1_679));
OF := AND_1((bool2bv((t1_679[64:63]) == (t2_680[64:63]))), (XOR_1((t1_679[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_679)), t2_680)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2b03:

ra_685 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_134,origCOUNT_140,origCOUNT_16,origCOUNT_160,origCOUNT_166,origCOUNT_188,origCOUNT_194,origCOUNT_214,origCOUNT_22,origCOUNT_220,origCOUNT_242,origCOUNT_248,origCOUNT_264,origCOUNT_270,origCOUNT_292,origCOUNT_298,origCOUNT_316,origCOUNT_322,origCOUNT_334,origCOUNT_340,origCOUNT_358,origCOUNT_364,origCOUNT_382,origCOUNT_388,origCOUNT_406,origCOUNT_412,origCOUNT_430,origCOUNT_436,origCOUNT_44,origCOUNT_454,origCOUNT_460,origCOUNT_488,origCOUNT_494,origCOUNT_50,origCOUNT_516,origCOUNT_522,origCOUNT_556,origCOUNT_562,origCOUNT_584,origCOUNT_590,origCOUNT_614,origCOUNT_620,origCOUNT_644,origCOUNT_650,origCOUNT_668,origCOUNT_674,origDEST_105,origDEST_111,origDEST_133,origDEST_139,origDEST_15,origDEST_159,origDEST_165,origDEST_187,origDEST_193,origDEST_21,origDEST_213,origDEST_219,origDEST_241,origDEST_247,origDEST_263,origDEST_269,origDEST_291,origDEST_297,origDEST_315,origDEST_321,origDEST_333,origDEST_339,origDEST_357,origDEST_363,origDEST_381,origDEST_387,origDEST_405,origDEST_411,origDEST_429,origDEST_43,origDEST_435,origDEST_453,origDEST_459,origDEST_487,origDEST_49,origDEST_493,origDEST_515,origDEST_521,origDEST_555,origDEST_561,origDEST_583,origDEST_589,origDEST_613,origDEST_619,origDEST_643,origDEST_649,origDEST_667,origDEST_673,ra_685,t1_121,t1_175,t1_229,t1_279,t1_303,t1_31,t1_345,t1_369,t1_393,t1_417,t1_441,t1_469,t1_475,t1_503,t1_535,t1_571,t1_595,t1_601,t1_625,t1_631,t1_655,t1_679,t2_122,t2_176,t2_230,t2_280,t2_304,t2_32,t2_346,t2_370,t2_394,t2_418,t2_442,t2_470,t2_476,t2_504,t2_536,t2_572,t2_596,t2_602,t2_626,t2_632,t2_656,t2_680,t_1,t_101,t_11,t_117,t_129,t_145,t_149,t_155,t_171,t_183,t_199,t_203,t_209,t_225,t_237,t_253,t_259,t_27,t_275,t_287,t_311,t_329,t_353,t_377,t_39,t_401,t_425,t_449,t_465,t_483,t_499,t_5,t_511,t_527,t_531,t_541,t_545,t_55,t_551,t_567,t_579,t_59,t_609,t_63,t_639,t_663,t_67,t_71,t_75,t_79,t_83,t_87,t_91,t_95;

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
var origCOUNT_134: bv64;
var origCOUNT_140: bv64;
var origCOUNT_16: bv64;
var origCOUNT_160: bv64;
var origCOUNT_166: bv64;
var origCOUNT_188: bv64;
var origCOUNT_194: bv64;
var origCOUNT_214: bv64;
var origCOUNT_22: bv64;
var origCOUNT_220: bv64;
var origCOUNT_242: bv64;
var origCOUNT_248: bv64;
var origCOUNT_264: bv64;
var origCOUNT_270: bv64;
var origCOUNT_292: bv64;
var origCOUNT_298: bv64;
var origCOUNT_316: bv64;
var origCOUNT_322: bv64;
var origCOUNT_334: bv64;
var origCOUNT_340: bv64;
var origCOUNT_358: bv64;
var origCOUNT_364: bv64;
var origCOUNT_382: bv64;
var origCOUNT_388: bv64;
var origCOUNT_406: bv64;
var origCOUNT_412: bv64;
var origCOUNT_430: bv64;
var origCOUNT_436: bv64;
var origCOUNT_44: bv64;
var origCOUNT_454: bv64;
var origCOUNT_460: bv64;
var origCOUNT_488: bv64;
var origCOUNT_494: bv64;
var origCOUNT_50: bv64;
var origCOUNT_516: bv64;
var origCOUNT_522: bv64;
var origCOUNT_556: bv64;
var origCOUNT_562: bv64;
var origCOUNT_584: bv64;
var origCOUNT_590: bv64;
var origCOUNT_614: bv64;
var origCOUNT_620: bv64;
var origCOUNT_644: bv64;
var origCOUNT_650: bv64;
var origCOUNT_668: bv64;
var origCOUNT_674: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_15: bv64;
var origDEST_159: bv64;
var origDEST_165: bv64;
var origDEST_187: bv64;
var origDEST_193: bv64;
var origDEST_21: bv64;
var origDEST_213: bv64;
var origDEST_219: bv64;
var origDEST_241: bv64;
var origDEST_247: bv64;
var origDEST_263: bv64;
var origDEST_269: bv64;
var origDEST_291: bv64;
var origDEST_297: bv64;
var origDEST_315: bv64;
var origDEST_321: bv64;
var origDEST_333: bv64;
var origDEST_339: bv64;
var origDEST_357: bv64;
var origDEST_363: bv64;
var origDEST_381: bv64;
var origDEST_387: bv64;
var origDEST_405: bv64;
var origDEST_411: bv64;
var origDEST_429: bv64;
var origDEST_43: bv64;
var origDEST_435: bv64;
var origDEST_453: bv64;
var origDEST_459: bv64;
var origDEST_487: bv64;
var origDEST_49: bv64;
var origDEST_493: bv64;
var origDEST_515: bv64;
var origDEST_521: bv64;
var origDEST_555: bv64;
var origDEST_561: bv64;
var origDEST_583: bv64;
var origDEST_589: bv64;
var origDEST_613: bv64;
var origDEST_619: bv64;
var origDEST_643: bv64;
var origDEST_649: bv64;
var origDEST_667: bv64;
var origDEST_673: bv64;
var ra_685: bv64;
var t1_121: bv64;
var t1_175: bv64;
var t1_229: bv64;
var t1_279: bv64;
var t1_303: bv64;
var t1_31: bv64;
var t1_345: bv64;
var t1_369: bv64;
var t1_393: bv64;
var t1_417: bv64;
var t1_441: bv64;
var t1_469: bv64;
var t1_475: bv64;
var t1_503: bv64;
var t1_535: bv64;
var t1_571: bv64;
var t1_595: bv64;
var t1_601: bv64;
var t1_625: bv64;
var t1_631: bv64;
var t1_655: bv64;
var t1_679: bv64;
var t2_122: bv64;
var t2_176: bv64;
var t2_230: bv64;
var t2_280: bv64;
var t2_304: bv64;
var t2_32: bv64;
var t2_346: bv64;
var t2_370: bv64;
var t2_394: bv64;
var t2_418: bv64;
var t2_442: bv64;
var t2_470: bv64;
var t2_476: bv64;
var t2_504: bv64;
var t2_536: bv64;
var t2_572: bv64;
var t2_596: bv64;
var t2_602: bv64;
var t2_626: bv64;
var t2_632: bv64;
var t2_656: bv64;
var t2_680: bv64;
var t_1: bv64;
var t_101: bv64;
var t_11: bv64;
var t_117: bv64;
var t_129: bv64;
var t_145: bv32;
var t_149: bv64;
var t_155: bv64;
var t_171: bv64;
var t_183: bv64;
var t_199: bv64;
var t_203: bv64;
var t_209: bv64;
var t_225: bv64;
var t_237: bv64;
var t_253: bv64;
var t_259: bv64;
var t_27: bv64;
var t_275: bv64;
var t_287: bv64;
var t_311: bv64;
var t_329: bv64;
var t_353: bv64;
var t_377: bv64;
var t_39: bv64;
var t_401: bv64;
var t_425: bv64;
var t_449: bv64;
var t_465: bv32;
var t_483: bv64;
var t_499: bv32;
var t_5: bv64;
var t_511: bv64;
var t_527: bv64;
var t_531: bv32;
var t_541: bv32;
var t_545: bv64;
var t_55: bv32;
var t_551: bv64;
var t_567: bv64;
var t_579: bv64;
var t_59: bv32;
var t_609: bv64;
var t_63: bv32;
var t_639: bv64;
var t_663: bv64;
var t_67: bv32;
var t_71: bv32;
var t_75: bv64;
var t_79: bv32;
var t_83: bv64;
var t_87: bv32;
var t_91: bv32;
var t_95: bv64;


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
