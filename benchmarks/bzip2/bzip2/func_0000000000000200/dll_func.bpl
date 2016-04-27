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
axiom _function_addr_low == 512bv64;
axiom _function_addr_high == 1408bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x200:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x205:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x209:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x20e:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x212:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x219:
origDEST_5 := RAX[32:0];
origCOUNT_6 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), CF, LSHIFT_32(origDEST_5, (MINUS_32(32bv32, origCOUNT_6)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_6 == 1bv32)), origDEST_5[32:31], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), AF, unconstrained_2);

label_0x21c:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x221:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RAX[32:0]);

label_0x225:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x22a:
RCX := (0bv32 ++ 1bv32);

label_0x22f:
t_13 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(7bv64[64:63]) ,(1bv64 ++ 7bv64) ,(0bv64 ++ 7bv64)))));
RCX := t_13[64:0];
OF := bool2bv(t_13 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_13 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_4;
SF := unconstrained_5;
ZF := unconstrained_6;
AF := unconstrained_7;

label_0x233:
t1_15 := RAX;
t2_16 := RCX;
RAX := PLUS_64(RAX, t2_16);
CF := bool2bv(LT_64(RAX, t1_15));
OF := AND_1((bool2bv((t1_15[64:63]) == (t2_16[64:63]))), (XOR_1((t1_15[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_15)), t2_16)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x236:
mem := STORE_LE_64(mem, RSP, RAX);

label_0x23a:
RAX := LOAD_LE_64(mem, RSP);

label_0x23e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x244:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x249:
t_23 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))))[1:0]));
SF := t_23[64:63];
ZF := bool2bv(0bv64 == t_23);

label_0x24c:
if (bv2bool(ZF)) {
  goto label_0x24f;
}

label_0x24e:
assume false;

label_0x24f:
RAX := LOAD_LE_64(mem, RSP);

label_0x253:
origDEST_27 := RAX;
origCOUNT_28 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), CF, LSHIFT_64(origDEST_27, (MINUS_64(64bv64, origCOUNT_28)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_28 == 1bv64)), origDEST_27[64:63], unconstrained_10));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), AF, unconstrained_11);

label_0x257:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x25e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x262:
RCX := LOAD_LE_64(mem, RSP);

label_0x266:
origDEST_33 := RCX;
origCOUNT_34 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, LSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), origDEST_33[64:63], unconstrained_12));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_13);

label_0x26a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_14;
SF := unconstrained_15;
AF := unconstrained_16;
PF := unconstrained_17;

label_0x26e:
if (bv2bool(CF)) {
  goto label_0x271;
}

label_0x270:
assume false;

label_0x271:
RAX := LOAD_LE_64(mem, RSP);

label_0x275:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 64bv64))));

label_0x27a:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x27c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x283:
origDEST_39 := RAX[32:0];
origCOUNT_40 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), CF, LSHIFT_32(origDEST_39, (MINUS_32(32bv32, origCOUNT_40)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv32)), origDEST_39[32:31], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv32)), AF, unconstrained_19);

label_0x286:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x28b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), RAX[32:0]);

label_0x28f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x294:
RCX := (0bv32 ++ 1bv32);

label_0x299:
t_47 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(6bv64[64:63]) ,(1bv64 ++ 6bv64) ,(0bv64 ++ 6bv64)))));
RCX := t_47[64:0];
OF := bool2bv(t_47 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_47 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_21;
SF := unconstrained_22;
ZF := unconstrained_23;
AF := unconstrained_24;

label_0x29d:
t1_49 := RAX;
t2_50 := RCX;
RAX := PLUS_64(RAX, t2_50);
CF := bool2bv(LT_64(RAX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RAX);

label_0x2a5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2aa:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2b5:
t_57 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0x2b8:
if (bv2bool(ZF)) {
  goto label_0x2bb;
}

label_0x2ba:
assume false;

label_0x2bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2c0:
origDEST_61 := RAX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_28);

label_0x2c4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2cb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2d4:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_30);

label_0x2d8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x2dc:
if (bv2bool(CF)) {
  goto label_0x2df;
}

label_0x2de:
assume false;

label_0x2df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e4:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 68bv64))));

label_0x2e9:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x2eb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x2f2:
origDEST_73 := RAX[32:0];
origCOUNT_74 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), CF, LSHIFT_32(origDEST_73, (MINUS_32(32bv32, origCOUNT_74)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_74 == 1bv32)), origDEST_73[32:31], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_74 == 0bv32)), AF, unconstrained_36);

label_0x2f5:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2fa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), RAX[32:0]);

label_0x2fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x303:
RCX := (0bv32 ++ 1bv32);

label_0x308:
t_81 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(5bv64[64:63]) ,(1bv64 ++ 5bv64) ,(0bv64 ++ 5bv64)))));
RCX := t_81[64:0];
OF := bool2bv(t_81 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_81 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_38;
SF := unconstrained_39;
ZF := unconstrained_40;
AF := unconstrained_41;

label_0x30c:
t1_83 := RAX;
t2_84 := RCX;
RAX := PLUS_64(RAX, t2_84);
CF := bool2bv(LT_64(RAX, t1_83));
OF := AND_1((bool2bv((t1_83[64:63]) == (t2_84[64:63]))), (XOR_1((t1_83[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_83)), t2_84)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x30f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RAX);

label_0x314:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x319:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_42;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x31f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x324:
t_91 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))))[1:0]));
SF := t_91[64:63];
ZF := bool2bv(0bv64 == t_91);

label_0x327:
if (bv2bool(ZF)) {
  goto label_0x32a;
}

label_0x329:
assume false;

label_0x32a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x32f:
origDEST_95 := RAX;
origCOUNT_96 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), CF, LSHIFT_64(origDEST_95, (MINUS_64(64bv64, origCOUNT_96)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_96 == 1bv64)), origDEST_95[64:63], unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_96 == 0bv64)), AF, unconstrained_45);

label_0x333:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x33a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x33e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x343:
origDEST_101 := RCX;
origCOUNT_102 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), CF, LSHIFT_64(origDEST_101, (MINUS_64(64bv64, origCOUNT_102)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_102 == 1bv64)), origDEST_101[64:63], unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_102 == 0bv64)), AF, unconstrained_47);

label_0x347:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_48;
SF := unconstrained_49;
AF := unconstrained_50;
PF := unconstrained_51;

label_0x34b:
if (bv2bool(CF)) {
  goto label_0x34e;
}

label_0x34d:
assume false;

label_0x34e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x353:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 72bv64))));

label_0x358:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x35a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 128bv64)));

label_0x361:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_52;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x366:
mem := STORE_LE_32(mem, PLUS_64(RSP, 76bv64), RAX[32:0]);

label_0x36a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x36f:
RCX := (0bv32 ++ 1bv32);

label_0x374:
t_109 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(4bv64[64:63]) ,(1bv64 ++ 4bv64) ,(0bv64 ++ 4bv64)))));
RCX := t_109[64:0];
OF := bool2bv(t_109 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_109 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_53;
SF := unconstrained_54;
ZF := unconstrained_55;
AF := unconstrained_56;

label_0x378:
t1_111 := RAX;
t2_112 := RCX;
RAX := PLUS_64(RAX, t2_112);
CF := bool2bv(LT_64(RAX, t1_111));
OF := AND_1((bool2bv((t1_111[64:63]) == (t2_112[64:63]))), (XOR_1((t1_111[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_111)), t2_112)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x37b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RAX);

label_0x380:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x385:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_57;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x38b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x390:
t_119 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)), 2bv64)), (XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)), 2bv64)), (XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)))))[1:0]));
SF := t_119[64:63];
ZF := bool2bv(0bv64 == t_119);

label_0x393:
if (bv2bool(ZF)) {
  goto label_0x396;
}

label_0x395:
assume false;

label_0x396:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x39b:
origDEST_123 := RAX;
origCOUNT_124 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), CF, LSHIFT_64(origDEST_123, (MINUS_64(64bv64, origCOUNT_124)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_124 == 1bv64)), origDEST_123[64:63], unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_124 == 0bv64)), AF, unconstrained_60);

label_0x39f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3a6:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3aa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x3af:
origDEST_129 := RCX;
origCOUNT_130 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), CF, LSHIFT_64(origDEST_129, (MINUS_64(64bv64, origCOUNT_130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_130 == 1bv64)), origDEST_129[64:63], unconstrained_61));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), AF, unconstrained_62);

label_0x3b3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_63;
SF := unconstrained_64;
AF := unconstrained_65;
PF := unconstrained_66;

label_0x3b7:
if (bv2bool(CF)) {
  goto label_0x3ba;
}

label_0x3b9:
assume false;

label_0x3ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x3bf:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 76bv64))));

label_0x3c4:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x3c6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x3ca:
origDEST_135 := RAX[32:0];
origCOUNT_136 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), CF, LSHIFT_32(origDEST_135, (MINUS_32(32bv32, origCOUNT_136)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv32)), origDEST_135[32:31], unconstrained_67));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv32)), AF, unconstrained_68);

label_0x3cd:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3d2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RAX[32:0]);

label_0x3d6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3db:
RCX := (0bv32 ++ 1bv32);

label_0x3e0:
t_143 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(3bv64[64:63]) ,(1bv64 ++ 3bv64) ,(0bv64 ++ 3bv64)))));
RCX := t_143[64:0];
OF := bool2bv(t_143 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_143 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_70;
SF := unconstrained_71;
ZF := unconstrained_72;
AF := unconstrained_73;

label_0x3e4:
t1_145 := RAX;
t2_146 := RCX;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x3ec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x3f1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_74;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3f7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3fc:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_75;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0x3ff:
if (bv2bool(ZF)) {
  goto label_0x402;
}

label_0x401:
assume false;

label_0x402:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x407:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_76));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_77);

label_0x40b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x412:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x416:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x41b:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_78));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_79);

label_0x41f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_80;
SF := unconstrained_81;
AF := unconstrained_82;
PF := unconstrained_83;

label_0x423:
if (bv2bool(CF)) {
  goto label_0x426;
}

label_0x425:
assume false;

label_0x426:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x42b:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 80bv64))));

label_0x430:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x432:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x436:
origDEST_169 := RAX[32:0];
origCOUNT_170 := AND_32(16bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(16bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), CF, LSHIFT_32(origDEST_169, (MINUS_32(32bv32, origCOUNT_170)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_170 == 1bv32)), origDEST_169[32:31], unconstrained_84));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_170 == 0bv32)), AF, unconstrained_85);

label_0x439:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_86;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x43e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), RAX[32:0]);

label_0x442:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x447:
RCX := (0bv32 ++ 1bv32);

label_0x44c:
t_177 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(2bv64[64:63]) ,(1bv64 ++ 2bv64) ,(0bv64 ++ 2bv64)))));
RCX := t_177[64:0];
OF := bool2bv(t_177 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_177 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_87;
SF := unconstrained_88;
ZF := unconstrained_89;
AF := unconstrained_90;

label_0x450:
t1_179 := RAX;
t2_180 := RCX;
RAX := PLUS_64(RAX, t2_180);
CF := bool2bv(LT_64(RAX, t1_179));
OF := AND_1((bool2bv((t1_179[64:63]) == (t2_180[64:63]))), (XOR_1((t1_179[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_179)), t2_180)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x453:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x458:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x45d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_91;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x463:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x468:
t_187 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_92;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)), 2bv64)), (XOR_64((RSHIFT_64(t_187, 4bv64)), t_187)))))[1:0]));
SF := t_187[64:63];
ZF := bool2bv(0bv64 == t_187);

label_0x46b:
if (bv2bool(ZF)) {
  goto label_0x46e;
}

label_0x46d:
assume false;

label_0x46e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x473:
origDEST_191 := RAX;
origCOUNT_192 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), CF, LSHIFT_64(origDEST_191, (MINUS_64(64bv64, origCOUNT_192)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_192 == 1bv64)), origDEST_191[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_192 == 0bv64)), AF, unconstrained_94);

label_0x477:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x47e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x482:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x487:
origDEST_197 := RCX;
origCOUNT_198 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), CF, LSHIFT_64(origDEST_197, (MINUS_64(64bv64, origCOUNT_198)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_198 == 1bv64)), origDEST_197[64:63], unconstrained_95));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_198 == 0bv64)), AF, unconstrained_96);

label_0x48b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_97;
SF := unconstrained_98;
AF := unconstrained_99;
PF := unconstrained_100;

label_0x48f:
if (bv2bool(CF)) {
  goto label_0x492;
}

label_0x491:
assume false;

label_0x492:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x497:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 84bv64))));

label_0x49c:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x49e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x4a2:
origDEST_203 := RAX[32:0];
origCOUNT_204 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), CF, LSHIFT_32(origDEST_203, (MINUS_32(32bv32, origCOUNT_204)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_204 == 1bv32)), origDEST_203[32:31], unconstrained_101));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_204 == 0bv32)), AF, unconstrained_102);

label_0x4a5:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_103;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x4aa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 88bv64), RAX[32:0]);

label_0x4ae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x4b3:
RCX := (0bv32 ++ 1bv32);

label_0x4b8:
t_211 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RCX := t_211[64:0];
OF := bool2bv(t_211 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_211 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_104;
SF := unconstrained_105;
ZF := unconstrained_106;
AF := unconstrained_107;

label_0x4bc:
t1_213 := RAX;
t2_214 := RCX;
RAX := PLUS_64(RAX, t2_214);
CF := bool2bv(LT_64(RAX, t1_213));
OF := AND_1((bool2bv((t1_213[64:63]) == (t2_214[64:63]))), (XOR_1((t1_213[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_213)), t2_214)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4bf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x4c4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4c9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_108;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x4cf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x4d4:
t_221 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_109;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)), 2bv64)), (XOR_64((RSHIFT_64(t_221, 4bv64)), t_221)))))[1:0]));
SF := t_221[64:63];
ZF := bool2bv(0bv64 == t_221);

label_0x4d7:
if (bv2bool(ZF)) {
  goto label_0x4da;
}

label_0x4d9:
assume false;

label_0x4da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4df:
origDEST_225 := RAX;
origCOUNT_226 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), CF, LSHIFT_64(origDEST_225, (MINUS_64(64bv64, origCOUNT_226)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_226 == 1bv64)), origDEST_225[64:63], unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_226 == 0bv64)), AF, unconstrained_111);

label_0x4e3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x4ea:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x4ee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x4f3:
origDEST_231 := RCX;
origCOUNT_232 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), CF, LSHIFT_64(origDEST_231, (MINUS_64(64bv64, origCOUNT_232)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_232 == 1bv64)), origDEST_231[64:63], unconstrained_112));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_232 == 0bv64)), AF, unconstrained_113);

label_0x4f7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_114;
SF := unconstrained_115;
AF := unconstrained_116;
PF := unconstrained_117;

label_0x4fb:
if (bv2bool(CF)) {
  goto label_0x4fe;
}

label_0x4fd:
assume false;

label_0x4fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x503:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 88bv64))));

label_0x508:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x50a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x50e:
RAX := (0bv32 ++ AND_32((RAX[32:0]), 255bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_118;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x513:
mem := STORE_LE_32(mem, PLUS_64(RSP, 92bv64), RAX[32:0]);

label_0x517:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x51c:
RCX := (0bv32 ++ 1bv32);

label_0x521:
t_239 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RCX := t_239[64:0];
OF := bool2bv(t_239 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_239 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_119;
SF := unconstrained_120;
ZF := unconstrained_121;
AF := unconstrained_122;

label_0x525:
t1_241 := RAX;
t2_242 := RCX;
RAX := PLUS_64(RAX, t2_242);
CF := bool2bv(LT_64(RAX, t1_241));
OF := AND_1((bool2bv((t1_241[64:63]) == (t2_242[64:63]))), (XOR_1((t1_241[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_241)), t2_242)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x528:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x52d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x532:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_123;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x538:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x53d:
t_249 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_124;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)), 2bv64)), (XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)), 2bv64)), (XOR_64((RSHIFT_64(t_249, 4bv64)), t_249)))))[1:0]));
SF := t_249[64:63];
ZF := bool2bv(0bv64 == t_249);

label_0x540:
if (bv2bool(ZF)) {
  goto label_0x543;
}

label_0x542:
assume false;

label_0x543:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x548:
origDEST_253 := RAX;
origCOUNT_254 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), CF, LSHIFT_64(origDEST_253, (MINUS_64(64bv64, origCOUNT_254)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_254 == 1bv64)), origDEST_253[64:63], unconstrained_125));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_254 == 0bv64)), AF, unconstrained_126);

label_0x54c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x553:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x557:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x55c:
origDEST_259 := RCX;
origCOUNT_260 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), CF, LSHIFT_64(origDEST_259, (MINUS_64(64bv64, origCOUNT_260)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_260 == 1bv64)), origDEST_259[64:63], unconstrained_127));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_260 == 0bv64)), AF, unconstrained_128);

label_0x560:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_129;
SF := unconstrained_130;
AF := unconstrained_131;
PF := unconstrained_132;

label_0x564:
if (bv2bool(CF)) {
  goto label_0x567;
}

label_0x566:
assume false;

label_0x567:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x56c:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 92bv64))));

label_0x571:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x573:
t1_265 := RSP;
t2_266 := 104bv64;
RSP := PLUS_64(RSP, t2_266);
CF := bool2bv(LT_64(RSP, t1_265));
OF := AND_1((bool2bv((t1_265[64:63]) == (t2_266[64:63]))), (XOR_1((t1_265[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_265)), t2_266)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x577:

ra_271 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_102,origCOUNT_124,origCOUNT_130,origCOUNT_136,origCOUNT_158,origCOUNT_164,origCOUNT_170,origCOUNT_192,origCOUNT_198,origCOUNT_204,origCOUNT_226,origCOUNT_232,origCOUNT_254,origCOUNT_260,origCOUNT_28,origCOUNT_34,origCOUNT_40,origCOUNT_6,origCOUNT_62,origCOUNT_68,origCOUNT_74,origCOUNT_96,origDEST_101,origDEST_123,origDEST_129,origDEST_135,origDEST_157,origDEST_163,origDEST_169,origDEST_191,origDEST_197,origDEST_203,origDEST_225,origDEST_231,origDEST_253,origDEST_259,origDEST_27,origDEST_33,origDEST_39,origDEST_5,origDEST_61,origDEST_67,origDEST_73,origDEST_95,ra_271,t1_111,t1_145,t1_15,t1_179,t1_213,t1_241,t1_265,t1_49,t1_83,t2_112,t2_146,t2_16,t2_180,t2_214,t2_242,t2_266,t2_50,t2_84,t_1,t_109,t_119,t_13,t_143,t_153,t_177,t_187,t_211,t_221,t_23,t_239,t_249,t_47,t_57,t_81,t_91;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_102: bv64;
var origCOUNT_124: bv64;
var origCOUNT_130: bv64;
var origCOUNT_136: bv32;
var origCOUNT_158: bv64;
var origCOUNT_164: bv64;
var origCOUNT_170: bv32;
var origCOUNT_192: bv64;
var origCOUNT_198: bv64;
var origCOUNT_204: bv32;
var origCOUNT_226: bv64;
var origCOUNT_232: bv64;
var origCOUNT_254: bv64;
var origCOUNT_260: bv64;
var origCOUNT_28: bv64;
var origCOUNT_34: bv64;
var origCOUNT_40: bv32;
var origCOUNT_6: bv32;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origCOUNT_74: bv32;
var origCOUNT_96: bv64;
var origDEST_101: bv64;
var origDEST_123: bv64;
var origDEST_129: bv64;
var origDEST_135: bv32;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_169: bv32;
var origDEST_191: bv64;
var origDEST_197: bv64;
var origDEST_203: bv32;
var origDEST_225: bv64;
var origDEST_231: bv64;
var origDEST_253: bv64;
var origDEST_259: bv64;
var origDEST_27: bv64;
var origDEST_33: bv64;
var origDEST_39: bv32;
var origDEST_5: bv32;
var origDEST_61: bv64;
var origDEST_67: bv64;
var origDEST_73: bv32;
var origDEST_95: bv64;
var ra_271: bv64;
var t1_111: bv64;
var t1_145: bv64;
var t1_15: bv64;
var t1_179: bv64;
var t1_213: bv64;
var t1_241: bv64;
var t1_265: bv64;
var t1_49: bv64;
var t1_83: bv64;
var t2_112: bv64;
var t2_146: bv64;
var t2_16: bv64;
var t2_180: bv64;
var t2_214: bv64;
var t2_242: bv64;
var t2_266: bv64;
var t2_50: bv64;
var t2_84: bv64;
var t_1: bv64;
var t_109: bv128;
var t_119: bv64;
var t_13: bv128;
var t_143: bv128;
var t_153: bv64;
var t_177: bv128;
var t_187: bv64;
var t_211: bv128;
var t_221: bv64;
var t_23: bv64;
var t_239: bv128;
var t_249: bv64;
var t_47: bv128;
var t_57: bv64;
var t_81: bv128;
var t_91: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(80bv64);
axiom policy(160bv64);
axiom policy(224bv64);
axiom policy(288bv64);
axiom policy(368bv64);
axiom policy(416bv64);
axiom policy(512bv64);
axiom policy(1408bv64);
axiom policy(1552bv64);
axiom policy(1632bv64);
axiom policy(1856bv64);
axiom policy(2640bv64);
axiom policy(2704bv64);
axiom policy(4064bv64);
axiom policy(5968bv64);
axiom policy(6000bv64);
axiom policy(6064bv64);
