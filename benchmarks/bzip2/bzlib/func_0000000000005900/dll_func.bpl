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
axiom _function_addr_low == 22784bv64;
axiom _function_addr_high == 23723bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x5900:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x5905:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x590a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x590f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x5914:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x5915:
t_3 := RSP;
RSP := MINUS_64(RSP, 304bv64);
CF := bool2bv(LT_64(t_3, 304bv64));
OF := AND_64((XOR_64(t_3, 304bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 304bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x591c:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5923:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RAX);

label_0x592b:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5930:
origDEST_7 := RAX;
origCOUNT_8 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), CF, LSHIFT_64(origDEST_7, (MINUS_64(64bv64, origCOUNT_8)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_8 == 1bv64)), origDEST_7[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_8 == 0bv64)), AF, unconstrained_2);

label_0x5934:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x593c:
RAX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5941:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_4);

label_0x5945:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5949:
RCX := (0bv32 ++ 1023bv32);

label_0x594e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RCX);

label_0x5956:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5959:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x5961:
origDEST_21 := RAX;
origCOUNT_22 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), CF, RSHIFT_64(origDEST_21, (MINUS_64(64bv64, origCOUNT_22)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_22 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_22 == 0bv64)), AF, unconstrained_7);

label_0x5964:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x596c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x5974:
mem := STORE_LE_64(mem, PLUS_64(RCX, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(RCX, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(RCX, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(RCX, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(RCX, RDX))));

label_0x5978:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 368bv64)));

label_0x597f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), RAX[32:0]);

label_0x5986:
t_29 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 320bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 320bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 320bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 320bv64))), t_29)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_29, (LOAD_LE_64(mem, PLUS_64(RSP, 320bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0x598f:
if (bv2bool(ZF)) {
  goto label_0x59ea;
}

label_0x5991:
t_33 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 328bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 328bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 328bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 328bv64))), t_33)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_33, (LOAD_LE_64(mem, PLUS_64(RSP, 328bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x599a:
if (bv2bool(ZF)) {
  goto label_0x59ea;
}

label_0x599c:
t_37 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))), t_37)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_37, (LOAD_LE_64(mem, PLUS_64(RSP, 336bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x59a5:
if (bv2bool(ZF)) {
  goto label_0x59ea;
}

label_0x59a7:
t_41 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 1bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 1bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 1bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0x59af:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x59ea;
}

label_0x59b1:
t_45 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 9bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 9bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), 9bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))), t_45)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_45, (LOAD_LE_32(mem, PLUS_64(RSP, 352bv64))))), 9bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)), 2bv32)), (XOR_32((RSHIFT_32(t_45, 4bv32)), t_45)))))[1:0]));
SF := t_45[32:31];
ZF := bool2bv(0bv32 == t_45);

label_0x59b9:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x59ea;
}

label_0x59bb:
t_49 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), t_49)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_49, (LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))))[1:0]));
SF := t_49[32:31];
ZF := bool2bv(0bv32 == t_49);

label_0x59c3:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x59ea;
}

label_0x59c5:
t_53 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))), t_53)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_53, (LOAD_LE_32(mem, PLUS_64(RSP, 360bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))))[1:0]));
SF := t_53[32:31];
ZF := bool2bv(0bv32 == t_53);

label_0x59cd:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x59ea;
}

label_0x59cf:
t_57 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), t_57)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_57, (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))))[1:0]));
SF := t_57[32:31];
ZF := bool2bv(0bv32 == t_57);

label_0x59d7:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x59ea;
}

label_0x59d9:
t_61 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 250bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 250bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 250bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), t_61)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_61, (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))), 250bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)), 2bv32)), (XOR_32((RSHIFT_32(t_61, 4bv32)), t_61)))))[1:0]));
SF := t_61[32:31];
ZF := bool2bv(0bv32 == t_61);

label_0x59e4:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x5a6a;
}

label_0x59ea:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x59f1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x59f9:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5a01:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_10);

label_0x5a05:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x5a0d:
t1_71 := RCX;
t2_72 := RAX;
RCX := PLUS_64(RCX, t2_72);
CF := bool2bv(LT_64(RCX, t1_71));
OF := AND_1((bool2bv((t1_71[64:63]) == (t2_72[64:63]))), (XOR_1((t1_71[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_71)), t2_72)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5a10:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RCX);

label_0x5a18:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5a20:
origDEST_77 := RAX;
origCOUNT_78 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), CF, LSHIFT_64(origDEST_77, (MINUS_64(64bv64, origCOUNT_78)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_78 == 1bv64)), origDEST_77[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_78 == 0bv64)), AF, unconstrained_12);

label_0x5a24:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5a28:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5a2a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 192bv64), RCX[32:0][8:0]);

label_0x5a31:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5a34:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 192bv64))));

label_0x5a3c:
origDEST_85 := RAX[32:0][8:0];
origCOUNT_86 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), CF, RSHIFT_8(origDEST_85, (MINUS_8(8bv8, origCOUNT_86)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_14));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv8)), AF, unconstrained_15);

label_0x5a3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x5a46:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5a48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x5a50:
t_93 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_93, 2bv64));
OF := AND_64((XOR_64(t_93, 2bv64)), (XOR_64(t_93, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_93)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5a54:
RDI := RAX;

label_0x5a57:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_17;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5a59:
RCX := (0bv32 ++ 2bv32);

label_0x5a5e:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5a60:
RAX := (0bv32 ++ 4294967294bv32);

label_0x5a65:
goto label_0x5dbc;

label_0x5a6a:
t_97 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))), t_97)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_97, (LOAD_LE_32(mem, PLUS_64(RSP, 148bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))))[1:0]));
SF := t_97[32:31];
ZF := bool2bv(0bv32 == t_97);

label_0x5a72:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5a7f;
}

label_0x5a74:
mem := STORE_LE_32(mem, PLUS_64(RSP, 148bv64), 30bv32);

label_0x5a7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), 0bv64);

label_0x5a88:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), 0bv64);

label_0x5a91:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), 0bv64);

label_0x5a9a:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 148bv64)));

label_0x5aa2:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 360bv64)));

label_0x5aaa:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 352bv64)));

label_0x5ab1:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5ab6:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 23227bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5abb"} true;
call arbitrary_func();

label_0x5abb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x5ac2:
t_101 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x5aca:
if (bv2bool(ZF)) {
  goto label_0x5b52;
}

label_0x5ad0:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5ad7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x5adf:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5ae7:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_19);

label_0x5aeb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x5af3:
t1_111 := RCX;
t2_112 := RAX;
RCX := PLUS_64(RCX, t2_112);
CF := bool2bv(LT_64(RCX, t1_111));
OF := AND_1((bool2bv((t1_111[64:63]) == (t2_112[64:63]))), (XOR_1((t1_111[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_111)), t2_112)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5af6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RCX);

label_0x5afe:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5b06:
origDEST_117 := RAX;
origCOUNT_118 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), CF, LSHIFT_64(origDEST_117, (MINUS_64(64bv64, origCOUNT_118)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_118 == 1bv64)), origDEST_117[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_118 == 0bv64)), AF, unconstrained_21);

label_0x5b0a:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5b0e:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5b10:
mem := STORE_LE_8(mem, PLUS_64(RSP, 216bv64), RCX[32:0][8:0]);

label_0x5b17:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5b1a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 216bv64))));

label_0x5b22:
origDEST_125 := RAX[32:0][8:0];
origCOUNT_126 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), CF, RSHIFT_8(origDEST_125, (MINUS_8(8bv8, origCOUNT_126)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv8)), AF, unconstrained_24);

label_0x5b24:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x5b2c:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5b2e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x5b36:
t_133 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_133, 2bv64));
OF := AND_64((XOR_64(t_133, 2bv64)), (XOR_64(t_133, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_133)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5b3a:
RDI := RAX;

label_0x5b3d:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_26;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5b3f:
RCX := (0bv32 ++ 2bv32);

label_0x5b44:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5b46:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x5b4d:
goto label_0x5dbc;

label_0x5b52:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x5b5a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x5b5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x5b67:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x5b6c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 344bv64)));

label_0x5b73:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x5b77:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5b7f:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5b81:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x5b85:
RDX := (0bv32 ++ 2bv32);

label_0x5b8a:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5b8f:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 23444bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5b94"} true;
call arbitrary_func();

label_0x5b94:
mem := STORE_LE_32(mem, PLUS_64(RSP, 144bv64), RAX[32:0]);

label_0x5b9b:
t_137 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_137)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_137, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))))[1:0]));
SF := t_137[32:31];
ZF := bool2bv(0bv32 == t_137);

label_0x5ba3:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x5baa;
}

label_0x5ba5:
goto label_0x5cab;

label_0x5baa:
t_141 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))), t_141)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_141, (LOAD_LE_32(mem, PLUS_64(RSP, 144bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)), 2bv32)), (XOR_32((RSHIFT_32(t_141, 4bv32)), t_141)))))[1:0]));
SF := t_141[32:31];
ZF := bool2bv(0bv32 == t_141);

label_0x5bb2:
if (bv2bool(ZF)) {
  goto label_0x5bb9;
}

label_0x5bb4:
goto label_0x5d35;

label_0x5bb9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5bc1:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0x5bc5:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x5bc7:
t_145 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_145, (RCX[32:0])));
OF := AND_32((XOR_32(t_145, (RCX[32:0]))), (XOR_32(t_145, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x5bc9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 220bv64), RAX[32:0]);

label_0x5bd0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5bd8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5bde:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5be3:
t_151 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)), 2bv64)), (XOR_64((RSHIFT_64(t_151, 4bv64)), t_151)))))[1:0]));
SF := t_151[64:63];
ZF := bool2bv(0bv64 == t_151);

label_0x5be6:
if (bv2bool(ZF)) {
  goto label_0x5be9;
}

label_0x5be8:
assume false;

label_0x5be9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5bf1:
origDEST_155 := RAX;
origCOUNT_156 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), CF, LSHIFT_64(origDEST_155, (MINUS_64(64bv64, origCOUNT_156)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv64)), origDEST_155[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv64)), AF, unconstrained_30);

label_0x5bf5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5bfc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5c00:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5c08:
origDEST_161 := RCX;
origCOUNT_162 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), CF, LSHIFT_64(origDEST_161, (MINUS_64(64bv64, origCOUNT_162)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_162 == 1bv64)), origDEST_161[64:63], unconstrained_31));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_162 == 0bv64)), AF, unconstrained_32);

label_0x5c0c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_33;
SF := unconstrained_34;
AF := unconstrained_35;
PF := unconstrained_36;

label_0x5c10:
if (bv2bool(CF)) {
  goto label_0x5c13;
}

label_0x5c12:
assume false;

label_0x5c13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x5c1b:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 220bv64)));

label_0x5c22:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x5c24:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5c29:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 23598bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5c2e"} true;
call arbitrary_func();

label_0x5c2e:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5c35:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x5c3d:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5c45:
origDEST_167 := RAX;
origCOUNT_168 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), CF, LSHIFT_64(origDEST_167, (MINUS_64(64bv64, origCOUNT_168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_168 == 1bv64)), origDEST_167[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_168 == 0bv64)), AF, unconstrained_38);

label_0x5c49:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x5c51:
t1_173 := RCX;
t2_174 := RAX;
RCX := PLUS_64(RCX, t2_174);
CF := bool2bv(LT_64(RCX, t1_173));
OF := AND_1((bool2bv((t1_173[64:63]) == (t2_174[64:63]))), (XOR_1((t1_173[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_173)), t2_174)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5c54:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RCX);

label_0x5c5c:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5c64:
origDEST_179 := RAX;
origCOUNT_180 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), CF, LSHIFT_64(origDEST_179, (MINUS_64(64bv64, origCOUNT_180)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_180 == 1bv64)), origDEST_179[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_180 == 0bv64)), AF, unconstrained_40);

label_0x5c68:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_41;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5c6c:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5c6e:
mem := STORE_LE_8(mem, PLUS_64(RSP, 240bv64), RCX[32:0][8:0]);

label_0x5c75:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5c78:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 240bv64))));

label_0x5c80:
origDEST_187 := RAX[32:0][8:0];
origCOUNT_188 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), CF, RSHIFT_8(origDEST_187, (MINUS_8(8bv8, origCOUNT_188)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_42));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv8)), AF, unconstrained_43);

label_0x5c82:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x5c8a:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5c8c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x5c94:
t_195 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_195, 2bv64));
OF := AND_64((XOR_64(t_195, 2bv64)), (XOR_64(t_195, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_195)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5c98:
RDI := RAX;

label_0x5c9b:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_45;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5c9d:
RCX := (0bv32 ++ 2bv32);

label_0x5ca2:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5ca4:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_46;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5ca6:
goto label_0x5dbc;

label_0x5cab:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5cb0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 23733bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5cb5"} true;
call arbitrary_func();

label_0x5cb5:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5cbc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x5cc4:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5ccc:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_48);

label_0x5cd0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x5cd8:
t1_205 := RCX;
t2_206 := RAX;
RCX := PLUS_64(RCX, t2_206);
CF := bool2bv(LT_64(RCX, t1_205));
OF := AND_1((bool2bv((t1_205[64:63]) == (t2_206[64:63]))), (XOR_1((t1_205[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_205)), t2_206)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5cdb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RCX);

label_0x5ce3:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5ceb:
origDEST_211 := RAX;
origCOUNT_212 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), CF, LSHIFT_64(origDEST_211, (MINUS_64(64bv64, origCOUNT_212)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_212 == 1bv64)), origDEST_211[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_212 == 0bv64)), AF, unconstrained_50);

label_0x5cef:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_51;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5cf3:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5cf5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 264bv64), RCX[32:0][8:0]);

label_0x5cfc:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5cff:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 264bv64))));

label_0x5d07:
origDEST_219 := RAX[32:0][8:0];
origCOUNT_220 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), CF, RSHIFT_8(origDEST_219, (MINUS_8(8bv8, origCOUNT_220)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_220 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_220 == 0bv8)), AF, unconstrained_53);

label_0x5d09:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x5d11:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_54;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5d13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x5d1b:
t_227 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_227, 2bv64));
OF := AND_64((XOR_64(t_227, 2bv64)), (XOR_64(t_227, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_227)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5d1f:
RDI := RAX;

label_0x5d22:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_55;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5d24:
RCX := (0bv32 ++ 2bv32);

label_0x5d29:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5d2b:
RAX := (0bv32 ++ 4294967288bv32);

label_0x5d30:
goto label_0x5dbc;

label_0x5d35:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x5d3a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 23871bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x5d3f"} true;
call arbitrary_func();

label_0x5d3f:
RAX := LOAD_LE_64(mem, 29888bv64);

label_0x5d46:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RAX);

label_0x5d4e:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5d56:
origDEST_231 := RAX;
origCOUNT_232 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), CF, LSHIFT_64(origDEST_231, (MINUS_64(64bv64, origCOUNT_232)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_232 == 1bv64)), origDEST_231[64:63], unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), AF, unconstrained_57);

label_0x5d5a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x5d62:
t1_237 := RCX;
t2_238 := RAX;
RCX := PLUS_64(RCX, t2_238);
CF := bool2bv(LT_64(RCX, t1_237));
OF := AND_1((bool2bv((t1_237[64:63]) == (t2_238[64:63]))), (XOR_1((t1_237[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_237)), t2_238)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x5d65:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RCX);

label_0x5d6d:
RAX := PLUS_64(RSP, 128bv64)[64:0];

label_0x5d75:
origDEST_243 := RAX;
origCOUNT_244 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), CF, LSHIFT_64(origDEST_243, (MINUS_64(64bv64, origCOUNT_244)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_244 == 1bv64)), origDEST_243[64:63], unconstrained_58));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_244 == 0bv64)), AF, unconstrained_59);

label_0x5d79:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_60;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5d7d:
RCX := (RCX[64:8]) ++ 254bv8;

label_0x5d7f:
mem := STORE_LE_8(mem, PLUS_64(RSP, 288bv64), RCX[32:0][8:0]);

label_0x5d86:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x5d89:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 288bv64))));

label_0x5d91:
origDEST_251 := RAX[32:0][8:0];
origCOUNT_252 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), CF, RSHIFT_8(origDEST_251, (MINUS_8(8bv8, origCOUNT_252)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_252 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_252 == 0bv8)), AF, unconstrained_62);

label_0x5d93:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x5d9b:
mem := STORE_LE_8(mem, RCX, AND_8((LOAD_LE_8(mem, RCX)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_63;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RCX)), 4bv8)), (LOAD_LE_8(mem, RCX)))))))[1:0]));
SF := LOAD_LE_8(mem, RCX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RCX)));

label_0x5d9d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x5da5:
t_259 := RAX;
RAX := MINUS_64(RAX, 2bv64);
CF := bool2bv(LT_64(t_259, 2bv64));
OF := AND_64((XOR_64(t_259, 2bv64)), (XOR_64(t_259, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_259)), 2bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5da9:
RDI := RAX;

label_0x5dac:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_64;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x5dae:
RCX := (0bv32 ++ 2bv32);

label_0x5db3:
assert {:SlashVerifyCommandType "rep_stosb"} true;

label_0x5db5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 144bv64)));

label_0x5dbc:
t1_263 := RSP;
t2_264 := 304bv64;
RSP := PLUS_64(RSP, t2_264);
CF := bool2bv(LT_64(RSP, t1_263));
OF := AND_1((bool2bv((t1_263[64:63]) == (t2_264[64:63]))), (XOR_1((t1_263[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_263)), t2_264)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x5dc3:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x5dc4:

ra_269 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDI,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_118,origCOUNT_126,origCOUNT_14,origCOUNT_156,origCOUNT_162,origCOUNT_168,origCOUNT_180,origCOUNT_188,origCOUNT_200,origCOUNT_212,origCOUNT_22,origCOUNT_220,origCOUNT_232,origCOUNT_244,origCOUNT_252,origCOUNT_66,origCOUNT_78,origCOUNT_8,origCOUNT_86,origDEST_105,origDEST_117,origDEST_125,origDEST_13,origDEST_155,origDEST_161,origDEST_167,origDEST_179,origDEST_187,origDEST_199,origDEST_21,origDEST_211,origDEST_219,origDEST_231,origDEST_243,origDEST_251,origDEST_65,origDEST_7,origDEST_77,origDEST_85,ra_269,t1_111,t1_173,t1_205,t1_237,t1_263,t1_71,t2_112,t2_174,t2_206,t2_238,t2_264,t2_72,t_1,t_101,t_133,t_137,t_141,t_145,t_151,t_195,t_227,t_259,t_29,t_3,t_33,t_37,t_41,t_45,t_49,t_53,t_57,t_61,t_93,t_97;

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
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_106: bv64;
var origCOUNT_118: bv64;
var origCOUNT_126: bv8;
var origCOUNT_14: bv64;
var origCOUNT_156: bv64;
var origCOUNT_162: bv64;
var origCOUNT_168: bv64;
var origCOUNT_180: bv64;
var origCOUNT_188: bv8;
var origCOUNT_200: bv64;
var origCOUNT_212: bv64;
var origCOUNT_22: bv64;
var origCOUNT_220: bv8;
var origCOUNT_232: bv64;
var origCOUNT_244: bv64;
var origCOUNT_252: bv8;
var origCOUNT_66: bv64;
var origCOUNT_78: bv64;
var origCOUNT_8: bv64;
var origCOUNT_86: bv8;
var origDEST_105: bv64;
var origDEST_117: bv64;
var origDEST_125: bv8;
var origDEST_13: bv64;
var origDEST_155: bv64;
var origDEST_161: bv64;
var origDEST_167: bv64;
var origDEST_179: bv64;
var origDEST_187: bv8;
var origDEST_199: bv64;
var origDEST_21: bv64;
var origDEST_211: bv64;
var origDEST_219: bv8;
var origDEST_231: bv64;
var origDEST_243: bv64;
var origDEST_251: bv8;
var origDEST_65: bv64;
var origDEST_7: bv64;
var origDEST_77: bv64;
var origDEST_85: bv8;
var ra_269: bv64;
var t1_111: bv64;
var t1_173: bv64;
var t1_205: bv64;
var t1_237: bv64;
var t1_263: bv64;
var t1_71: bv64;
var t2_112: bv64;
var t2_174: bv64;
var t2_206: bv64;
var t2_238: bv64;
var t2_264: bv64;
var t2_72: bv64;
var t_1: bv64;
var t_101: bv32;
var t_133: bv64;
var t_137: bv32;
var t_141: bv32;
var t_145: bv32;
var t_151: bv64;
var t_195: bv64;
var t_227: bv64;
var t_259: bv64;
var t_29: bv64;
var t_3: bv64;
var t_33: bv64;
var t_37: bv64;
var t_41: bv32;
var t_45: bv32;
var t_49: bv32;
var t_53: bv32;
var t_57: bv32;
var t_61: bv32;
var t_93: bv64;
var t_97: bv32;


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
