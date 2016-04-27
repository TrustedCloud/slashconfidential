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
axiom _guard_writeTable_ptr == 12352bv64;
axiom _guard_callTable_ptr == 12336bv64;
axiom _function_addr_low == 10240bv64;
axiom _function_addr_high == 10521bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2800:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x2805:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2809:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x280e:
RAX := LOAD_LE_64(mem, RAX);

label_0x2811:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x2816:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x281b:
t_5 := MINUS_32((LOAD_LE_32(mem, RAX)), 3221225477bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 3221225477bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 3221225477bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, RAX)))), 3221225477bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x2821:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2912;
}

label_0x2827:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x282c:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RAX, 24bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x2830:
if (bv2bool(CF)) {
  goto label_0x2912;
}

label_0x2836:
RAX := (0bv32 ++ 8bv32);

label_0x283b:
t_13 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(0bv64[64:63]) ,(1bv64 ++ 0bv64) ,(0bv64 ++ 0bv64)))));
RAX := t_13[64:0];
OF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_13 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_1;
SF := unconstrained_2;
ZF := unconstrained_3;
AF := unconstrained_4;

label_0x283f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2844:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 32bv64));

label_0x2849:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x284e:
RAX := (0bv32 ++ 8bv32);

label_0x2853:
t_15 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(1bv64[64:63]) ,(1bv64 ++ 1bv64) ,(0bv64 ++ 1bv64)))));
RAX := t_15[64:0];
OF := bool2bv(t_15 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_15 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_5;
SF := unconstrained_6;
ZF := unconstrained_7;
AF := unconstrained_8;

label_0x2857:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x285c:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 32bv64));

label_0x2861:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x2866:
t_17 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_17)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_17, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)), 2bv64)), (XOR_64((RSHIFT_64(t_17, 4bv64)), t_17)))))[1:0]));
SF := t_17[64:63];
ZF := bool2bv(0bv64 == t_17);

label_0x286c:
if (bv2bool(ZF)) {
  goto label_0x287a;
}

label_0x286e:
t_21 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 1bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 1bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 1bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_21)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_21, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))))[1:0]));
SF := t_21[64:63];
ZF := bool2bv(0bv64 == t_21);

label_0x2874:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2912;
}

label_0x287a:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1983bv64, 10369bv64)), 0bv64));

label_0x2881:
t_25 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_25)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_25, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))))[1:0]));
SF := t_25[64:63];
ZF := bool2bv(0bv64 == t_25);

label_0x2886:
if (bv2bool(CF)) {
  goto label_0x28a3;
}

label_0x2888:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1961bv64, 10383bv64)), 0bv64));

label_0x288f:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1962bv64, 10390bv64)), 0bv64));

label_0x2896:
t1_29 := RCX;
t2_30 := RAX;
RCX := PLUS_64(RCX, t2_30);
CF := bool2bv(LT_64(RCX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x2899:
RAX := RCX;

label_0x289c:
t_35 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_35)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_35, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))))[1:0]));
SF := t_35[64:63];
ZF := bool2bv(0bv64 == t_35);

label_0x28a1:
if (bv2bool(CF)) {
  goto label_0x28d5;
}

label_0x28a3:
t_39 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(6038bv64, 10409bv64)), 1bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(6038bv64, 10409bv64)), 1bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(6038bv64, 10409bv64)), 1bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(6038bv64, 10409bv64)), 1bv64))), t_39)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_39, (LOAD_LE_32(mem, PLUS_64((PLUS_64(6038bv64, 10409bv64)), 1bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_39, 4bv32)), t_39)), 2bv32)), (XOR_32((RSHIFT_32(t_39, 4bv32)), t_39)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_39, 4bv32)), t_39)), 2bv32)), (XOR_32((RSHIFT_32(t_39, 4bv32)), t_39)))))[1:0]));
SF := t_39[32:31];
ZF := bool2bv(0bv32 == t_39);

label_0x28aa:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2912;
}

label_0x28ac:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1917bv64, 10419bv64)), 0bv64));

label_0x28b3:
t_43 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_43)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_43, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x28b8:
if (bv2bool(CF)) {
  goto label_0x2912;
}

label_0x28ba:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1895bv64, 10433bv64)), 0bv64));

label_0x28c1:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(1896bv64, 10440bv64)), 0bv64));

label_0x28c8:
t1_47 := RCX;
t2_48 := RAX;
RCX := PLUS_64(RCX, t2_48);
CF := bool2bv(LT_64(RCX, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x28cb:
RAX := RCX;

label_0x28ce:
t_53 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_53)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_53, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))))[1:0]));
SF := t_53[64:63];
ZF := bool2bv(0bv64 == t_53);

label_0x28d3:
if (bv2bool(NOT_1(CF))) {
  goto label_0x2912;
}

label_0x28d5:
R9 := (0bv32 ++ 4bv32);

label_0x28db:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(5918bv64, 10466bv64)), 0bv64)));

label_0x28e2:
RDX := (0bv32 ++ 1bv32);

label_0x28e7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x28ec:

target_57 := LOAD_LE_64(mem, PLUS_64((PLUS_64(1822bv64, 10482bv64)), 0bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10482bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_57"} true;
call arbitrary_func();

label_0x28f2:
t_59 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)), 2bv64)), (XOR_64((RSHIFT_64(t_59, 4bv64)), t_59)))))[1:0]));
SF := t_59[64:63];
ZF := bool2bv(0bv64 == t_59);

label_0x28f5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x290b;
}

label_0x28f7:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x28fc:
RDX := (0bv32 ++ 1bv32);

label_0x2901:
RCX := (0bv32 ++ 3221225495bv32);

label_0x2906:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10507bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1260"} true;
call arbitrary_func();

label_0x290b:
RAX := (0bv32 ++ 4294967295bv32);

label_0x2910:
goto label_0x2914;

label_0x2912:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2914:
t1_63 := RSP;
t2_64 := 72bv64;
RSP := PLUS_64(RSP, t2_64);
CF := bool2bv(LT_64(RSP, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2918:

ra_69 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,ra_69,t1_29,t1_47,t1_63,t2_30,t2_48,t2_64,t_1,t_13,t_15,t_17,t_21,t_25,t_35,t_39,t_43,t_5,t_53,t_59,t_9,target_57;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
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
var ra_69: bv64;
var t1_29: bv64;
var t1_47: bv64;
var t1_63: bv64;
var t2_30: bv64;
var t2_48: bv64;
var t2_64: bv64;
var t_1: bv64;
var t_13: bv128;
var t_15: bv128;
var t_17: bv64;
var t_21: bv64;
var t_25: bv64;
var t_35: bv64;
var t_39: bv32;
var t_43: bv64;
var t_5: bv32;
var t_53: bv64;
var t_59: bv64;
var t_9: bv32;
var target_57: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4160bv64);
axiom policy(4240bv64);
axiom policy(4288bv64);
axiom policy(4304bv64);
axiom policy(4704bv64);
axiom policy(4736bv64);
axiom policy(4800bv64);
axiom policy(5200bv64);
axiom policy(5664bv64);
axiom policy(5728bv64);
axiom policy(5776bv64);
axiom policy(5840bv64);
axiom policy(5904bv64);
axiom policy(5968bv64);
axiom policy(6288bv64);
axiom policy(6992bv64);
axiom policy(7088bv64);
axiom policy(7168bv64);
axiom policy(7312bv64);
axiom policy(7520bv64);
axiom policy(7664bv64);
axiom policy(7824bv64);
axiom policy(7840bv64);
axiom policy(7952bv64);
axiom policy(8096bv64);
axiom policy(8240bv64);
axiom policy(8800bv64);
axiom policy(8880bv64);
axiom policy(9040bv64);
axiom policy(9088bv64);
axiom policy(9136bv64);
axiom policy(9216bv64);
axiom policy(9264bv64);
axiom policy(9312bv64);
axiom policy(9360bv64);
axiom policy(9392bv64);
axiom policy(9424bv64);
axiom policy(9472bv64);
axiom policy(9520bv64);
axiom policy(9568bv64);
axiom policy(9600bv64);
axiom policy(9616bv64);
axiom policy(9632bv64);
axiom policy(9648bv64);
axiom policy(9664bv64);
axiom policy(9680bv64);
axiom policy(9696bv64);
axiom policy(9984bv64);
axiom policy(10240bv64);
axiom policy(10528bv64);
axiom policy(10672bv64);
axiom policy(10800bv64);
axiom policy(10944bv64);
