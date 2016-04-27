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
axiom _function_addr_low == 448bv64;
axiom _function_addr_high == 1680bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1c0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x1c5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x1c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1ce:
t_1 := RSP;
RSP := MINUS_64(RSP, 136bv64);
CF := bool2bv(LT_64(t_1, 136bv64));
OF := AND_64((XOR_64(t_1, 136bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 136bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1d5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x1dd:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x1e4:
t_5 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_5[32:0]);
OF := bool2bv(t_5 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_5 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_1;
SF := unconstrained_2;
ZF := unconstrained_3;
AF := unconstrained_4;

label_0x1eb:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1ed:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x1f4:
t1_7 := RCX[32:0];
t2_8 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_8));
CF := bool2bv(LT_32((RCX[32:0]), t1_7));
OF := AND_1((bool2bv((t1_7[32:31]) == (t2_8[32:31]))), (XOR_1((t1_7[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_7)), t2_8)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1f6:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1f8:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x1fa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x202:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x206:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x20a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x212:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 16bv64))));

label_0x216:
t_13 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x218:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x21f;
}

label_0x21a:
goto label_0x676;

label_0x21f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x227:
t1_17 := RAX;
t2_18 := 16bv64;
RAX := PLUS_64(RAX, t2_18);
CF := bool2bv(LT_64(RAX, t1_17));
OF := AND_1((bool2bv((t1_17[64:63]) == (t2_18[64:63]))), (XOR_1((t1_17[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_17)), t2_18)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x22b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x230:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x238:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x23f:
t_23 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_23[32:0]);
OF := bool2bv(t_23 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_23 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_5;
SF := unconstrained_6;
ZF := unconstrained_7;
AF := unconstrained_8;

label_0x246:
RAX := (0bv32 ++ RCX[32:0]);

label_0x248:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x24f:
t1_25 := RCX[32:0];
t2_26 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_26));
CF := bool2bv(LT_32((RCX[32:0]), t1_25));
OF := AND_1((bool2bv((t1_25[32:31]) == (t2_26[32:31]))), (XOR_1((t1_25[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_25)), t2_26)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x251:
RAX := (0bv32 ++ RCX[32:0]);

label_0x253:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x255:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x25d:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x261:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x265:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x26a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x26f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x275:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x27a:
t_33 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)), 2bv64)), (XOR_64((RSHIFT_64(t_33, 4bv64)), t_33)))))[1:0]));
SF := t_33[64:63];
ZF := bool2bv(0bv64 == t_33);

label_0x27d:
if (bv2bool(ZF)) {
  goto label_0x280;
}

label_0x27f:
assume false;

label_0x280:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x285:
origDEST_37 := RAX;
origCOUNT_38 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_12);

label_0x289:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x290:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x294:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x299:
origDEST_43 := RCX;
origCOUNT_44 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, LSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), origDEST_43[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0x29d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_15;
SF := unconstrained_16;
AF := unconstrained_17;
PF := unconstrained_18;

label_0x2a1:
if (bv2bool(CF)) {
  goto label_0x2a4;
}

label_0x2a3:
assume false;

label_0x2a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2ae:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2b1:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2b4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x2bb:
t_49 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_49, 1bv32)), (XOR_32(t_49, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_49)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2bd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x2c1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x2c8:
t_53 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_53, 1bv32)), (XOR_32(t_53, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_53)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2ca:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x2ce:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x2d5:
t_57 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_57[32:31]) == (1bv32[32:31]))), (XOR_1((t_57[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_57)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2d7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x2db:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x2e2:
t_61 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_61[32:31]) == (1bv32[32:31]))), (XOR_1((t_61[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_61)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2e4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x2e8:
t_65 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))), t_65)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_65, (LOAD_LE_32(mem, PLUS_64(RSP, 56bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)), 2bv32)), (XOR_32((RSHIFT_32(t_65, 4bv32)), t_65)))))[1:0]));
SF := t_65[32:31];
ZF := bool2bv(0bv32 == t_65);

label_0x2ed:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x2f7;
}

label_0x2ef:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 0bv32);

label_0x2f7:
t_69 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_69)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_69, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)), 2bv32)), (XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)), 2bv32)), (XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)))))[1:0]));
SF := t_69[32:31];
ZF := bool2bv(0bv32 == t_69);

label_0x2fc:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x306;
}

label_0x2fe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 0bv32);

label_0x306:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x30e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4408bv64)));

label_0x314:
t_73 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), t_73)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_73, (LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x318:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x32c;
}

label_0x31a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x322:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4408bv64)));

label_0x328:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x32c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x334:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4412bv64)));

label_0x33a:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x33e:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x352;
}

label_0x340:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x348:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4412bv64)));

label_0x34e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x352:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), 10000000bv32);

label_0x35a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 1bv8);

label_0x35f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x363:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x367:
goto label_0x373;

label_0x369:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x36d:
t_81 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_81[32:31]) == (1bv32[32:31]))), (XOR_1((t_81[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_81)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x36f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x373:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x377:
t_85 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_85)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_85, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))))[1:0]));
SF := t_85[32:31];
ZF := bool2bv(0bv32 == t_85);

label_0x37b:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x48a;
}

label_0x381:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x385:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x389:
goto label_0x395;

label_0x38b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x38f:
t_89 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_89[32:31]) == (1bv32[32:31]))), (XOR_1((t_89[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_89)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x391:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x395:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)));

label_0x399:
t_93 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_93)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_93, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)), 2bv32)), (XOR_32((RSHIFT_32(t_93, 4bv32)), t_93)))))[1:0]));
SF := t_93[32:31];
ZF := bool2bv(0bv32 == t_93);

label_0x39d:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x485;
}

label_0x3a3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x3aa:
t_97 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_97)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_97, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)), 2bv32)), (XOR_32((RSHIFT_32(t_97, 4bv32)), t_97)))))[1:0]));
SF := t_97[32:31];
ZF := bool2bv(0bv32 == t_97);

label_0x3ae:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3c1;
}

label_0x3b0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x3b7:
t_101 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x3bb:
if (bv2bool(ZF)) {
  goto label_0x480;
}

label_0x3c1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3c9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x3cd:
t_105 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_105[32:0]);
OF := bool2bv(t_105 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_105 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_19;
SF := unconstrained_20;
ZF := unconstrained_21;
AF := unconstrained_22;

label_0x3d4:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3d6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x3da:
t1_107 := RCX[32:0];
t2_108 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_108));
CF := bool2bv(LT_32((RCX[32:0]), t1_107));
OF := AND_1((bool2bv((t1_107[32:31]) == (t2_108[32:31]))), (XOR_1((t1_107[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_107)), t2_108)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3dc:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3de:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3e8:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x3ec:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x3f0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x3f8:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 16bv64))));

label_0x3fc:
t_113 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_113)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_113, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)), 2bv32)), (XOR_32((RSHIFT_32(t_113, 4bv32)), t_113)))))[1:0]));
SF := t_113[32:31];
ZF := bool2bv(0bv32 == t_113);

label_0x3fe:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x44d;
}

label_0x400:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x408:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x40c:
t_117 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_117[32:0]);
OF := bool2bv(t_117 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_117 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_23;
SF := unconstrained_24;
ZF := unconstrained_25;
AF := unconstrained_26;

label_0x413:
RAX := (0bv32 ++ RCX[32:0]);

label_0x415:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x419:
t1_119 := RCX[32:0];
t2_120 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_120));
CF := bool2bv(LT_32((RCX[32:0]), t1_119));
OF := AND_1((bool2bv((t1_119[32:31]) == (t2_120[32:31]))), (XOR_1((t1_119[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_119)), t2_120)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x41b:
RAX := (0bv32 ++ RCX[32:0]);

label_0x41d:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x41f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x427:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x42b:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64((PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))), 2bv64))));

label_0x430:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), RAX[32:0]);

label_0x434:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x438:
t_125 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), t_125)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_125, (LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)), 2bv32)), (XOR_32((RSHIFT_32(t_125, 4bv32)), t_125)))))[1:0]));
SF := t_125[32:31];
ZF := bool2bv(0bv32 == t_125);

label_0x43c:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x44b;
}

label_0x43e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 68bv64)));

label_0x442:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RAX[32:0]);

label_0x446:
mem := STORE_LE_8(mem, PLUS_64(RSP, 32bv64), 0bv8);

label_0x44b:
goto label_0x480;

label_0x44d:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x452:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x456:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x45e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1123bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x463"} true;
call arbitrary_func();

label_0x463:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x466:
t_129 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)), 2bv32)), (XOR_32((RSHIFT_32(t_129, 4bv32)), t_129)))))[1:0]));
SF := t_129[32:31];
ZF := bool2bv(0bv32 == t_129);

label_0x468:
if (bv2bool(ZF)) {
  goto label_0x480;
}

label_0x46a:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x46f:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x473:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x47b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1152bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x480"} true;
call arbitrary_func();

label_0x480:
goto label_0x38b;

label_0x485:
goto label_0x369;

label_0x48a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x48f:
t_133 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0x491:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x54a;
}

label_0x497:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x49f:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x4a6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x4ae:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1203bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4b3"} true;
call arbitrary_func();

label_0x4b3:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x4b6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x4ba:
t1_137 := RCX[32:0];
t2_138 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_138));
CF := bool2bv(LT_32((RCX[32:0]), t1_137));
OF := AND_1((bool2bv((t1_137[32:31]) == (t2_138[32:31]))), (XOR_1((t1_137[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_137)), t2_138)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4bc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 104bv64), RCX[32:0]);

label_0x4c0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x4c8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x4cf:
t_143 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_143[32:0]);
OF := bool2bv(t_143 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_143 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_29;
SF := unconstrained_30;
ZF := unconstrained_31;
AF := unconstrained_32;

label_0x4d6:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4d8:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x4df:
t1_145 := RCX[32:0];
t2_146 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_146));
CF := bool2bv(LT_32((RCX[32:0]), t1_145));
OF := AND_1((bool2bv((t1_145[32:31]) == (t2_146[32:31]))), (XOR_1((t1_145[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_145)), t2_146)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x4e1:
RAX := (0bv32 ++ RCX[32:0]);

label_0x4e3:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x4e5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x4ed:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x4f1:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x4f5:
t1_151 := RAX;
t2_152 := 2bv64;
RAX := PLUS_64(RAX, t2_152);
CF := bool2bv(LT_64(RAX, t1_151));
OF := AND_1((bool2bv((t1_151[64:63]) == (t2_152[64:63]))), (XOR_1((t1_151[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_151)), t2_152)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4f9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x4fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x503:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x509:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x50e:
t_159 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)), 2bv64)), (XOR_64((RSHIFT_64(t_159, 4bv64)), t_159)))))[1:0]));
SF := t_159[64:63];
ZF := bool2bv(0bv64 == t_159);

label_0x511:
if (bv2bool(ZF)) {
  goto label_0x514;
}

label_0x513:
assume false;

label_0x514:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x519:
origDEST_163 := RAX;
origCOUNT_164 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_36);

label_0x51d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x524:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x528:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x52d:
origDEST_169 := RCX;
origCOUNT_170 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), CF, LSHIFT_64(origDEST_169, (MINUS_64(64bv64, origCOUNT_170)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv64)), origDEST_169[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv64)), AF, unconstrained_38);

label_0x531:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x535:
if (bv2bool(CF)) {
  goto label_0x538;
}

label_0x537:
assume false;

label_0x538:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x53d:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 104bv64))));

label_0x542:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x545:
goto label_0x5f3;

label_0x54a:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x552:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x559:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x561:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 1382bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x566"} true;
call arbitrary_func();

label_0x566:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x569:
mem := STORE_LE_16(mem, PLUS_64(RSP, 44bv64), RAX[32:0][16:0]);

label_0x56e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x576:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x57d:
t_175 := TIMES_64(((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))), ((ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4424bv64)))))));
RCX := (0bv32 ++ t_175[32:0]);
OF := bool2bv(t_175 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
CF := bool2bv(t_175 != ((ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])))));
PF := unconstrained_43;
SF := unconstrained_44;
ZF := unconstrained_45;
AF := unconstrained_46;

label_0x584:
RAX := (0bv32 ++ RCX[32:0]);

label_0x586:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 152bv64)));

label_0x58d:
t1_177 := RCX[32:0];
t2_178 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_178));
CF := bool2bv(LT_32((RCX[32:0]), t1_177));
OF := AND_1((bool2bv((t1_177[32:31]) == (t2_178[32:31]))), (XOR_1((t1_177[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_177)), t2_178)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x58f:
RAX := (0bv32 ++ RCX[32:0]);

label_0x591:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x593:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x59b:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 8bv64));

label_0x59f:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x5a3:
t1_183 := RAX;
t2_184 := 2bv64;
RAX := PLUS_64(RAX, t2_184);
CF := bool2bv(LT_64(RAX, t1_183));
OF := AND_1((bool2bv((t1_183[64:63]) == (t2_184[64:63]))), (XOR_1((t1_183[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_183)), t2_184)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5a7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x5ac:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x5b1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x5b7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x5bc:
t_191 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)), 2bv64)), (XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)), 2bv64)), (XOR_64((RSHIFT_64(t_191, 4bv64)), t_191)))))[1:0]));
SF := t_191[64:63];
ZF := bool2bv(0bv64 == t_191);

label_0x5bf:
if (bv2bool(ZF)) {
  goto label_0x5c2;
}

label_0x5c1:
assume false;

label_0x5c2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x5c7:
origDEST_195 := RAX;
origCOUNT_196 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), CF, LSHIFT_64(origDEST_195, (MINUS_64(64bv64, origCOUNT_196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_196 == 1bv64)), origDEST_195[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_196 == 0bv64)), AF, unconstrained_50);

label_0x5cb:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x5d2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x5d6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x5db:
origDEST_201 := RCX;
origCOUNT_202 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), CF, LSHIFT_64(origDEST_201, (MINUS_64(64bv64, origCOUNT_202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_202 == 1bv64)), origDEST_201[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_202 == 0bv64)), AF, unconstrained_52);

label_0x5df:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x5e3:
if (bv2bool(CF)) {
  goto label_0x5e6;
}

label_0x5e5:
assume false;

label_0x5e6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x5eb:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 44bv64))));

label_0x5f0:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x5f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x5fb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4388bv64)));

label_0x601:
t_207 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))), t_207)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_207, (LOAD_LE_32(mem, PLUS_64(RSP, 152bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)), 2bv32)), (XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)), 2bv32)), (XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)))))[1:0]));
SF := t_207[32:31];
ZF := bool2bv(0bv32 == t_207);

label_0x608:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x676;
}

label_0x60a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x612:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 4392bv64)));

label_0x618:
t_211 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), t_211)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_211, (LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))))[1:0]));
SF := t_211[32:31];
ZF := bool2bv(0bv32 == t_211);

label_0x61f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x676;
}

label_0x621:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x629:
t1_215 := RAX;
t2_216 := 4404bv64;
RAX := PLUS_64(RAX, t2_216);
CF := bool2bv(LT_64(RAX, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x62f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x634:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x639:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x63f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x644:
t_223 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))))[1:0]));
SF := t_223[64:63];
ZF := bool2bv(0bv64 == t_223);

label_0x647:
if (bv2bool(ZF)) {
  goto label_0x64a;
}

label_0x649:
assume false;

label_0x64a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x64f:
origDEST_227 := RAX;
origCOUNT_228 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_60);

label_0x653:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x65a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x65e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x663:
origDEST_233 := RCX;
origCOUNT_234 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_62);

label_0x667:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_63;
SF := unconstrained_64;
AF := unconstrained_65;
PF := unconstrained_66;

label_0x66b:
if (bv2bool(CF)) {
  goto label_0x66e;
}

label_0x66d:
assume false;

label_0x66e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x673:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x676:
t1_239 := RSP;
t2_240 := 136bv64;
RSP := PLUS_64(RSP, t2_240);
CF := bool2bv(LT_64(RSP, t1_239));
OF := AND_1((bool2bv((t1_239[64:63]) == (t2_240[64:63]))), (XOR_1((t1_239[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_239)), t2_240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x67d:

ra_245 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_164,origCOUNT_170,origCOUNT_196,origCOUNT_202,origCOUNT_228,origCOUNT_234,origCOUNT_38,origCOUNT_44,origDEST_163,origDEST_169,origDEST_195,origDEST_201,origDEST_227,origDEST_233,origDEST_37,origDEST_43,ra_245,t1_107,t1_119,t1_137,t1_145,t1_151,t1_17,t1_177,t1_183,t1_215,t1_239,t1_25,t1_7,t2_108,t2_120,t2_138,t2_146,t2_152,t2_178,t2_18,t2_184,t2_216,t2_240,t2_26,t2_8,t_1,t_101,t_105,t_113,t_117,t_125,t_129,t_13,t_133,t_143,t_159,t_175,t_191,t_207,t_211,t_223,t_23,t_33,t_49,t_5,t_53,t_57,t_61,t_65,t_69,t_73,t_77,t_81,t_85,t_89,t_93,t_97;

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
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
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
var origCOUNT_164: bv64;
var origCOUNT_170: bv64;
var origCOUNT_196: bv64;
var origCOUNT_202: bv64;
var origCOUNT_228: bv64;
var origCOUNT_234: bv64;
var origCOUNT_38: bv64;
var origCOUNT_44: bv64;
var origDEST_163: bv64;
var origDEST_169: bv64;
var origDEST_195: bv64;
var origDEST_201: bv64;
var origDEST_227: bv64;
var origDEST_233: bv64;
var origDEST_37: bv64;
var origDEST_43: bv64;
var ra_245: bv64;
var t1_107: bv32;
var t1_119: bv32;
var t1_137: bv32;
var t1_145: bv32;
var t1_151: bv64;
var t1_17: bv64;
var t1_177: bv32;
var t1_183: bv64;
var t1_215: bv64;
var t1_239: bv64;
var t1_25: bv32;
var t1_7: bv32;
var t2_108: bv32;
var t2_120: bv32;
var t2_138: bv32;
var t2_146: bv32;
var t2_152: bv64;
var t2_178: bv32;
var t2_18: bv64;
var t2_184: bv64;
var t2_216: bv64;
var t2_240: bv64;
var t2_26: bv32;
var t2_8: bv32;
var t_1: bv64;
var t_101: bv32;
var t_105: bv64;
var t_113: bv32;
var t_117: bv64;
var t_125: bv32;
var t_129: bv32;
var t_13: bv32;
var t_133: bv32;
var t_143: bv64;
var t_159: bv64;
var t_175: bv64;
var t_191: bv64;
var t_207: bv32;
var t_211: bv32;
var t_223: bv64;
var t_23: bv64;
var t_33: bv64;
var t_49: bv32;
var t_5: bv64;
var t_53: bv32;
var t_57: bv32;
var t_61: bv32;
var t_65: bv32;
var t_69: bv32;
var t_73: bv32;
var t_77: bv32;
var t_81: bv32;
var t_85: bv32;
var t_89: bv32;
var t_93: bv32;
var t_97: bv32;


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
