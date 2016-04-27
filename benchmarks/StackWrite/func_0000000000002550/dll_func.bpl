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
axiom _function_addr_low == 9552bv64;
axiom _function_addr_high == 10103bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2550:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x2555:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x255a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x255f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x2564:
t_1 := RSP;
RSP := MINUS_64(RSP, 136bv64);
CF := bool2bv(LT_64(t_1, 136bv64));
OF := AND_64((XOR_64(t_1, 136bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 136bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x256b:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 152bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 152bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 152bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 152bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 152bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x2574:
if (bv2bool(ZF)) {
  goto label_0x2581;
}

label_0x2576:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 144bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x257f:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2586;
}

label_0x2581:
goto label_0x276f;

label_0x2586:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x258e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x2593:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x259b:
RAX := AND_64(RAX, 7bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x259f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x25a7:
RAX := PLUS_64((PLUS_64(RCX, RAX)), 7bv64)[64:0];

label_0x25ac:
origDEST_15 := RAX;
origCOUNT_16 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), CF, LSHIFT_64(origDEST_15, (MINUS_64(64bv64, origCOUNT_16)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_16 == 1bv64)), origDEST_15[64:63], unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_16 == 0bv64)), AF, unconstrained_3);

label_0x25b0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x25b5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x25ba:
RAX := AND_64(RAX, 4294967295bv32 ++ 4294967288bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25be:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x25c3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x25c8:
origDEST_23 := RAX;
origCOUNT_24 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, LSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), origDEST_23[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_6);

label_0x25cc:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x25d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x25d6:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, LSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), origDEST_29[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_8);

label_0x25da:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(2655bv64, 9697bv64)), 0bv64));

label_0x25e1:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64)))[64:0];

label_0x25e5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x25ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x25ef:
RAX := AND_64(RAX, 511bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25f5:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x25f8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2606;
}

label_0x25fa:
t_41 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_41)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_41, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 64bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x2600:
if (bv2bool(NOT_1(CF))) {
  goto label_0x26d3;
}

label_0x2606:
t_45 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_45)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_45, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 64bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)), 2bv64)), (XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)), 2bv64)), (XOR_64((RSHIFT_64(t_45, 4bv64)), t_45)))))[1:0]));
SF := t_45[64:63];
ZF := bool2bv(0bv64 == t_45);

label_0x260c:
if (bv2bool(CF)) {
  goto label_0x2619;
}

label_0x260e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), 4294967295bv32 ++ 4294967295bv32);

label_0x2617:
goto label_0x263d;

label_0x2619:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x261e:
RCX := 4294967295bv32 ++ 4294967295bv32;

label_0x2625:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RCX);

label_0x262a:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x262d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x2632:
origDEST_49 := RAX;
origCOUNT_50 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), CF, RSHIFT_64(origDEST_49, (MINUS_64(64bv64, origCOUNT_50)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_50 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_50 == 0bv64)), AF, unconstrained_12);

label_0x2635:
RAX := NOT_64(RAX);

label_0x2638:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x263d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x2642:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x2647:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x264c:
origDEST_55 := RAX;
origCOUNT_56 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_14);

label_0x2650:
RAX := AND_64(RAX, 63bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2654:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x2658:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x265c:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x265f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2664:
origDEST_63 := RAX;
origCOUNT_64 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), CF, RSHIFT_64(origDEST_63, (MINUS_64(64bv64, origCOUNT_64)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_64 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_64 == 0bv64)), AF, unconstrained_17);

label_0x2667:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x266c:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x2674:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x267c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2681:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2686:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 9867bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x24c0"} true;
call arbitrary_func();

label_0x268b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x2690:
t1_69 := RAX;
t2_70 := 8bv64;
RAX := PLUS_64(RAX, t2_70);
CF := bool2bv(LT_64(RAX, t1_69));
OF := AND_1((bool2bv((t1_69[64:63]) == (t2_70[64:63]))), (XOR_1((t1_69[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_69)), t2_70)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2694:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x2699:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x269d:
RCX := (0bv32 ++ 64bv32);

label_0x26a2:
t_75 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_75, RAX));
OF := AND_64((XOR_64(t_75, RAX)), (XOR_64(t_75, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_75)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x26a5:
RAX := RCX;

label_0x26a8:
t_79 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_79)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_79, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)), 2bv64)), (XOR_64((RSHIFT_64(t_79, 4bv64)), t_79)))))[1:0]));
SF := t_79[64:63];
ZF := bool2bv(0bv64 == t_79);

label_0x26ad:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x26b4;
}

label_0x26af:
goto label_0x276f;

label_0x26b4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x26b8:
RCX := (0bv32 ++ 64bv32);

label_0x26bd:
t_83 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_83, RAX));
OF := AND_64((XOR_64(t_83, RAX)), (XOR_64(t_83, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_83)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x26c0:
RAX := RCX;

label_0x26c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x26c8:
t_87 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_87, RAX));
OF := AND_64((XOR_64(t_87, RAX)), (XOR_64(t_87, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_87)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x26cb:
RAX := RCX;

label_0x26ce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x26d3:
t_91 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 64bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_91)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_91, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 64bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)), 2bv64)), (XOR_64((RSHIFT_64(t_91, 4bv64)), t_91)))))[1:0]));
SF := t_91[64:63];
ZF := bool2bv(0bv64 == t_91);

label_0x26d9:
if (bv2bool(CF)) {
  goto label_0x2724;
}

label_0x26db:
t_95 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))), t_95)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_95, (LOAD_LE_32(mem, PLUS_64(RSP, 160bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)), 2bv32)), (XOR_32((RSHIFT_32(t_95, 4bv32)), t_95)))))[1:0]));
SF := t_95[32:31];
ZF := bool2bv(0bv32 == t_95);

label_0x26e3:
if (bv2bool(ZF)) {
  goto label_0x26f0;
}

label_0x26e5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), 4294967295bv32 ++ 4294967295bv32);

label_0x26ee:
goto label_0x26f9;

label_0x26f0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), 0bv64);

label_0x26f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x26fe:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x2703:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x2706:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x270b:
t1_99 := RAX;
t2_100 := 8bv64;
RAX := PLUS_64(RAX, t2_100);
CF := bool2bv(LT_64(RAX, t1_99));
OF := AND_1((bool2bv((t1_99[64:63]) == (t2_100[64:63]))), (XOR_1((t1_99[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_99)), t2_100)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x270f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x2714:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2719:
t_105 := RAX;
RAX := MINUS_64(RAX, 64bv64);
CF := bool2bv(LT_64(t_105, 64bv64));
OF := AND_64((XOR_64(t_105, 64bv64)), (XOR_64(t_105, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_105)), 64bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x271d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x2722:
goto label_0x26d3;

label_0x2724:
t_109 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))), t_109)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_109, (LOAD_LE_64(mem, PLUS_64(RSP, 32bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))))[1:0]));
SF := t_109[64:63];
ZF := bool2bv(0bv64 == t_109);

label_0x272a:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x276f;
}

label_0x272c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x2731:
RCX := 4294967295bv32 ++ 4294967295bv32;

label_0x2738:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RCX);

label_0x273d:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x2740:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x2745:
origDEST_113 := RAX;
origCOUNT_114 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, RSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_19);

label_0x2748:
RAX := NOT_64(RAX);

label_0x274b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RAX);

label_0x2750:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x2758:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x2760:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2765:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x276a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 10095bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x24c0"} true;
call arbitrary_func();

label_0x276f:
t1_119 := RSP;
t2_120 := 136bv64;
RSP := PLUS_64(RSP, t2_120);
CF := bool2bv(LT_64(RSP, t1_119));
OF := AND_1((bool2bv((t1_119[64:63]) == (t2_120[64:63]))), (XOR_1((t1_119[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_119)), t2_120)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2776:

ra_125 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_114,origCOUNT_16,origCOUNT_24,origCOUNT_30,origCOUNT_50,origCOUNT_56,origCOUNT_64,origDEST_113,origDEST_15,origDEST_23,origDEST_29,origDEST_49,origDEST_55,origDEST_63,ra_125,t1_119,t1_69,t1_99,t2_100,t2_120,t2_70,t_1,t_105,t_109,t_37,t_41,t_45,t_5,t_75,t_79,t_83,t_87,t_9,t_91,t_95;

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
var origCOUNT_114: bv64;
var origCOUNT_16: bv64;
var origCOUNT_24: bv64;
var origCOUNT_30: bv64;
var origCOUNT_50: bv64;
var origCOUNT_56: bv64;
var origCOUNT_64: bv64;
var origDEST_113: bv64;
var origDEST_15: bv64;
var origDEST_23: bv64;
var origDEST_29: bv64;
var origDEST_49: bv64;
var origDEST_55: bv64;
var origDEST_63: bv64;
var ra_125: bv64;
var t1_119: bv64;
var t1_69: bv64;
var t1_99: bv64;
var t2_100: bv64;
var t2_120: bv64;
var t2_70: bv64;
var t_1: bv64;
var t_105: bv64;
var t_109: bv64;
var t_37: bv64;
var t_41: bv64;
var t_45: bv64;
var t_5: bv64;
var t_75: bv64;
var t_79: bv64;
var t_83: bv64;
var t_87: bv64;
var t_9: bv64;
var t_91: bv64;
var t_95: bv32;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4672bv64);
axiom policy(4720bv64);
axiom policy(4768bv64);
axiom policy(4784bv64);
axiom policy(5072bv64);
axiom policy(5328bv64);
axiom policy(5616bv64);
axiom policy(6016bv64);
axiom policy(6048bv64);
axiom policy(6112bv64);
axiom policy(6512bv64);
axiom policy(6976bv64);
axiom policy(7040bv64);
axiom policy(7088bv64);
axiom policy(7152bv64);
axiom policy(7216bv64);
axiom policy(7280bv64);
axiom policy(7600bv64);
axiom policy(8304bv64);
axiom policy(8400bv64);
axiom policy(8480bv64);
axiom policy(8624bv64);
axiom policy(8832bv64);
axiom policy(8976bv64);
axiom policy(9136bv64);
axiom policy(9152bv64);
axiom policy(9264bv64);
axiom policy(9408bv64);
axiom policy(9552bv64);
axiom policy(10112bv64);
axiom policy(10192bv64);
axiom policy(10352bv64);
axiom policy(10400bv64);
axiom policy(10448bv64);
axiom policy(10528bv64);
axiom policy(10576bv64);
axiom policy(10624bv64);
axiom policy(10672bv64);
axiom policy(10704bv64);
axiom policy(10736bv64);
axiom policy(10784bv64);
axiom policy(10832bv64);
axiom policy(10880bv64);
axiom policy(10912bv64);
axiom policy(10928bv64);
axiom policy(10944bv64);
axiom policy(10960bv64);
axiom policy(10976bv64);
axiom policy(10992bv64);
axiom policy(11008bv64);
axiom policy(11152bv64);
axiom policy(11280bv64);
axiom policy(11424bv64);
