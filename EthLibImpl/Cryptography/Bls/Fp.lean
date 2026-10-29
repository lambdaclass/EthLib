import EthLibImpl.Cryptography.Bls.Limbs
import EthLib.Cryptography.Bls.Errors

/-!
# `Fp`

The BLS12-381 base field, as six 64-bit little-endian words in Montgomery
form: the words of `a` hold `a · R mod p` with `R = 2^384`.

The spec (`EthLib.Cryptography.Bls.Fp`) is `Fin p` over `Nat`, so every
operation there is a GMP call plus a heap allocation per intermediate. Here
a field element is one Lean object with six unboxed `UInt64` fields, and
multiplication is word-level Montgomery (CIOS), so an operation costs one
allocation and straight-line native code.

Invariant: every `Fp` produced by this module is *canonical*, i.e. its word
vector, read as an integer, is below `p`. Operations assume canonical inputs.
Intermediate values inside `mul` are below `2p`, which fits in six words
since `2p < 2^383`.

Equivalence with the spec is stated through `Fp.val` (the decoded residue)
in `EthLibImpl.Cryptography.Proofs.Bls.Fp`.
-/

namespace EthLibImpl.Cryptography.Bls

open EthLib.Cryptography.Bls (BlsError)
open Limbs

/-- A base-field element in Montgomery form, six little-endian words. -/
structure Fp where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
deriving Inhabited, Repr

namespace Fp

/-- BLS12-381 base field modulus (same value as the spec's `Fp.modulus`). -/
def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-! ## Constants -/

def P0 : UInt64 := 0xb9feffffffffaaab
def P1 : UInt64 := 0x1eabfffeb153ffff
def P2 : UInt64 := 0x6730d2a0f6b0f624
def P3 : UInt64 := 0x64774b84f38512bf
def P4 : UInt64 := 0x4b1ba7b6434bacd7
def P5 : UInt64 := 0x1a0111ea397fe69a

/-- `-p⁻¹ mod 2^64`, the Montgomery reduction constant. -/
def N0 : UInt64 := 0x89f3fffcfffcfffd

/-- The integer a word vector stands for (no Montgomery decoding). -/
def raw (a : Fp) : Nat :=
  a.l0.toNat + 2^64 * (a.l1.toNat + 2^64 * (a.l2.toNat + 2^64 * (a.l3.toNat +
    2^64 * (a.l4.toNat + 2^64 * a.l5.toNat))))

/-- The words of `n mod 2^384` (no Montgomery encoding). -/
def ofRaw (n : Nat) : Fp :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64,
   (n >>> 256).toUInt64, (n >>> 320).toUInt64⟩

/-- All-zero words: the field's zero, also the starting accumulator. -/
def zero : Fp := ⟨0, 0, 0, 0, 0, 0⟩

/-- `R mod p`, i.e. the field's one in Montgomery form. -/
def one : Fp := ofRaw
  0x15f65ec3fa80e4935c071a97a256ec6d77ce5853705257455f48985753c758baebf4000bc40c0002760900000002fffd

/-- `R² mod p`; multiplying by it converts into Montgomery form. -/
def R2 : Fp := ofRaw
  0x11988fe592cae3aa9a793e85b519952d67eb88a9939d83c08de5476c4c95b6d50a76e6a609d104f1f4df1f341c341746

/-- The plain integer one; multiplying by it converts out of Montgomery form. -/
def rawOne : Fp := ⟨1, 0, 0, 0, 0, 0⟩

/-! ## Word-vector helpers -/

/-- The modulus as an object. Additions and the Montgomery rows read its
words from memory: on x86-64 a 64-bit constant must otherwise be rebuilt
with a `movabs` into a register before every use, which roughly doubled
the instruction count of inlined additions. -/
def modulusWords : Fp := ⟨P0, P1, P2, P3, P4, P5⟩

/-- `t - p` and the final borrow (`1` iff `t < p`). -/
@[inline] def subP (t : Fp) : Fp × UInt64 :=
  let q := modulusWords
  let (d0, b) := sbb t.l0 q.l0 0
  let (d1, b) := sbb t.l1 q.l1 b
  let (d2, b) := sbb t.l2 q.l2 b
  let (d3, b) := sbb t.l3 q.l3 b
  let (d4, b) := sbb t.l4 q.l4 b
  let (d5, b) := sbb t.l5 q.l5 b
  (⟨d0, d1, d2, d3, d4, d5⟩, b)

/-- `t + p` modulo `2^384`. -/
@[inline] def addP (t : Fp) : Fp :=
  let q := modulusWords
  let (s0, c) := adc t.l0 q.l0 0
  let (s1, c) := adc t.l1 q.l1 c
  let (s2, c) := adc t.l2 q.l2 c
  let (s3, c) := adc t.l3 q.l3 c
  let (s4, c) := adc t.l4 q.l4 c
  let (s5, _) := adc t.l5 q.l5 c
  ⟨s0, s1, s2, s3, s4, s5⟩

/-- `if m = 0 then a else b`, word by word, for a mask `m` that is `0` or
all ones. Branch-free, so that inlined callers never have to materialize
a structure at a join point. -/
@[inline] def select (m : UInt64) (a b : Fp) : Fp :=
  ⟨a.l0 ^^^ ((a.l0 ^^^ b.l0) &&& m), a.l1 ^^^ ((a.l1 ^^^ b.l1) &&& m),
   a.l2 ^^^ ((a.l2 ^^^ b.l2) &&& m), a.l3 ^^^ ((a.l3 ^^^ b.l3) &&& m),
   a.l4 ^^^ ((a.l4 ^^^ b.l4) &&& m), a.l5 ^^^ ((a.l5 ^^^ b.l5) &&& m)⟩

/-- Map `[0, 2p)` onto `[0, p)` by one conditional subtraction. -/
@[inline] def reduceOnce (t : Fp) : Fp :=
  let (d, b) := subP t
  select (0 - b) d t

/-! ## Montgomery multiplication (CIOS)

`mul` runs six rows. Row `i` adds `a_i · b` to the accumulator (`mulRow`),
then adds the multiple `m · p` that clears the low word and drops that word
(`redRow`). After every row the accumulator is below `2p`, and after the
sixth it equals `a · b · R⁻¹` modulo `p`.

Each half-row computes its six products first and then adds the low words
and the (shifted) high words in two separate `adc` chains. Every chain
compiles to one run of add-with-carry instructions, which is about half the
instructions of accumulating each product with its own carries. -/

/-- Seven-word accumulator between the two halves of a row. -/
structure Acc7 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64

/-- `t + a · b` for a six-word `t` and a single word `a`. The top word
cannot overflow: the sum is below `2^448`. -/
@[inline] def mulRow (t : Fp) (a : UInt64) (b : Fp) : Acc7 :=
  let (s0, c) := adc t.l0 (a * b.l0) 0
  let (s1, c) := adc t.l1 (a * b.l1) c
  let (s2, c) := adc t.l2 (a * b.l2) c
  let (s3, c) := adc t.l3 (a * b.l3) c
  let (s4, c) := adc t.l4 (a * b.l4) c
  let (s5, c) := adc t.l5 (a * b.l5) c
  let (u1, d) := adc s1 (mulHi a b.l0) 0
  let (u2, d) := adc s2 (mulHi a b.l1) d
  let (u3, d) := adc s3 (mulHi a b.l2) d
  let (u4, d) := adc s4 (mulHi a b.l3) d
  let (u5, d) := adc s5 (mulHi a b.l4) d
  ⟨s0, u1, u2, u3, u4, u5, c + mulHi a b.l5 + d⟩

/-- `(t + m · p) / 2^64` with `m = t₀ · N0 mod 2^64`, so the division is
exact. The low word of the sum is zero; only its carry is kept. -/
@[inline] def redRow (t : Acc7) : Fp :=
  let m := t.w0 * N0
  -- The modulus words come from memory here too: inside the larger
  -- kernels (`Fp2` products, inlined curve formulas) that measured faster
  -- than rebuilding them as immediates (`N0` stays an immediate).
  let q := modulusWords
  let (_, c) := adc t.w0 (m * q.l0) 0
  let (s1, c) := adc t.w1 (m * q.l1) c
  let (s2, c) := adc t.w2 (m * q.l2) c
  let (s3, c) := adc t.w3 (m * q.l3) c
  let (s4, c) := adc t.w4 (m * q.l4) c
  let (s5, c) := adc t.w5 (m * q.l5) c
  let (u1, d) := adc s1 (mulHi m q.l0) 0
  let (u2, d) := adc s2 (mulHi m q.l1) d
  let (u3, d) := adc s3 (mulHi m q.l2) d
  let (u4, d) := adc s4 (mulHi m q.l3) d
  let (u5, d) := adc s5 (mulHi m q.l4) d
  ⟨u1, u2, u3, u4, u5, t.w6 + c + mulHi m q.l5 + d⟩

/-! ## Wide products and Montgomery reduction

For lazy reduction in `Fp2`: `mulWide` is the full 768-bit product (six
`mulRow`s sliding along the accumulator, no reduction), and `redc` is the
Montgomery reduction of a 768-bit value below `p · R` (six `redRow`s on the
low half, then the high half added). One `mulWide` plus one `redc` is the
same work as a `mul`, but sums and differences of wide products can be
reduced once. -/

/-- A 768-bit value, twelve little-endian words. -/
structure W12 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64

/-- `a · b` as twelve words. -/
@[inline] def mulWide (a b : Fp) : W12 :=
  let r0 := mulRow zero a.l0 b
  let r1 := mulRow ⟨r0.w1, r0.w2, r0.w3, r0.w4, r0.w5, r0.w6⟩ a.l1 b
  let r2 := mulRow ⟨r1.w1, r1.w2, r1.w3, r1.w4, r1.w5, r1.w6⟩ a.l2 b
  let r3 := mulRow ⟨r2.w1, r2.w2, r2.w3, r2.w4, r2.w5, r2.w6⟩ a.l3 b
  let r4 := mulRow ⟨r3.w1, r3.w2, r3.w3, r3.w4, r3.w5, r3.w6⟩ a.l4 b
  let r5 := mulRow ⟨r4.w1, r4.w2, r4.w3, r4.w4, r4.w5, r4.w6⟩ a.l5 b
  ⟨r0.w0, r1.w0, r2.w0, r3.w0, r4.w0, r5.w0, r5.w1, r5.w2, r5.w3, r5.w4, r5.w5, r5.w6⟩

/-- `a + b` with no reduction; callers keep the sum below `2^384`. -/
@[inline] def addRaw (a b : Fp) : Fp :=
  let (s0, c) := adc a.l0 b.l0 0
  let (s1, c) := adc a.l1 b.l1 c
  let (s2, c) := adc a.l2 b.l2 c
  let (s3, c) := adc a.l3 b.l3 c
  let (s4, c) := adc a.l4 b.l4 c
  let (s5, _) := adc a.l5 b.l5 c
  ⟨s0, s1, s2, s3, s4, s5⟩

/-- `t · R⁻¹ mod p`, canonical, for `t < p · R`. The six rows compute
`(t_lo + M·p) / R ≤ p` for the low half `t_lo`, and the high half
`t_hi < p` is added, so one conditional subtraction finishes. -/
@[inline] def redc (t : W12) : Fp :=
  let v := redRow ⟨t.w0, t.w1, t.w2, t.w3, t.w4, t.w5, 0⟩
  let v := redRow ⟨v.l0, v.l1, v.l2, v.l3, v.l4, v.l5, 0⟩
  let v := redRow ⟨v.l0, v.l1, v.l2, v.l3, v.l4, v.l5, 0⟩
  let v := redRow ⟨v.l0, v.l1, v.l2, v.l3, v.l4, v.l5, 0⟩
  let v := redRow ⟨v.l0, v.l1, v.l2, v.l3, v.l4, v.l5, 0⟩
  let v := redRow ⟨v.l0, v.l1, v.l2, v.l3, v.l4, v.l5, 0⟩
  reduceOnce (addRaw v ⟨t.w6, t.w7, t.w8, t.w9, t.w10, t.w11⟩)

/-- Twelve-word subtraction and its final borrow. -/
@[inline] def sub12 (a b : W12) : W12 × UInt64 :=
  let (d0, br) := sbb a.w0 b.w0 0
  let (d1, br) := sbb a.w1 b.w1 br
  let (d2, br) := sbb a.w2 b.w2 br
  let (d3, br) := sbb a.w3 b.w3 br
  let (d4, br) := sbb a.w4 b.w4 br
  let (d5, br) := sbb a.w5 b.w5 br
  let (d6, br) := sbb a.w6 b.w6 br
  let (d7, br) := sbb a.w7 b.w7 br
  let (d8, br) := sbb a.w8 b.w8 br
  let (d9, br) := sbb a.w9 b.w9 br
  let (d10, br) := sbb a.w10 b.w10 br
  let (d11, br) := sbb a.w11 b.w11 br
  (⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, br)

/-- `a − b`, plus `p · R` when that borrows (`p` added to the high half),
so the result stays in `[0, p · R)` for `a, b < p · R`. -/
@[inline] def subWideModPR (a b : W12) : W12 :=
  let (d, br) := sub12 a b
  let m := 0 - br
  let q := modulusWords
  let (h0, c) := adc d.w6 (q.l0 &&& m) 0
  let (h1, c) := adc d.w7 (q.l1 &&& m) c
  let (h2, c) := adc d.w8 (q.l2 &&& m) c
  let (h3, c) := adc d.w9 (q.l3 &&& m) c
  let (h4, c) := adc d.w10 (q.l4 &&& m) c
  let (h5, _) := adc d.w11 (q.l5 &&& m) c
  ⟨d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, h0, h1, h2, h3, h4, h5⟩

/-! Every operation comes in two forms: an `@[inline]` one (`mulI`,
`addI`, …) for fused callers such as `Fp2`, where the intermediate
structures cancel against their projections and no `Fp` is allocated, and
a plain one (`mul`, `add`, …) that is one function call. They are equal by
definition. -/

/-- Montgomery product `a · b · R⁻¹ mod p`; in Montgomery form, the field
product. -/
@[inline] def mulI (a b : Fp) : Fp :=
  let t := redRow (mulRow zero a.l0 b)
  let t := redRow (mulRow t a.l1 b)
  let t := redRow (mulRow t a.l2 b)
  let t := redRow (mulRow t a.l3 b)
  let t := redRow (mulRow t a.l4 b)
  let t := redRow (mulRow t a.l5 b)
  reduceOnce t

def mul (a b : Fp) : Fp := mulI a b

/-- Field squaring. A function of its own (not `mul a a`), so that an
exclusive argument's memory is reused for the result: in exponentiation
loops this saves an allocation and a free per squaring. -/
def sqr (a : Fp) : Fp := mulI a a

/-! ## Additive operations -/

@[inline] def addI (a b : Fp) : Fp :=
  let (s0, c) := adc a.l0 b.l0 0
  let (s1, c) := adc a.l1 b.l1 c
  let (s2, c) := adc a.l2 b.l2 c
  let (s3, c) := adc a.l3 b.l3 c
  let (s4, c) := adc a.l4 b.l4 c
  let (s5, _) := adc a.l5 b.l5 c
  reduceOnce ⟨s0, s1, s2, s3, s4, s5⟩

@[inline] def add (a b : Fp) : Fp := addI a b

/-- `a - b`, adding `p` back (masked) when the subtraction borrows. -/
@[inline] def subI (a b : Fp) : Fp :=
  let (d0, br) := sbb a.l0 b.l0 0
  let (d1, br) := sbb a.l1 b.l1 br
  let (d2, br) := sbb a.l2 b.l2 br
  let (d3, br) := sbb a.l3 b.l3 br
  let (d4, br) := sbb a.l4 b.l4 br
  let (d5, br) := sbb a.l5 b.l5 br
  let m := 0 - br
  let q := modulusWords
  let (s0, c) := adc d0 (q.l0 &&& m) 0
  let (s1, c) := adc d1 (q.l1 &&& m) c
  let (s2, c) := adc d2 (q.l2 &&& m) c
  let (s3, c) := adc d3 (q.l3 &&& m) c
  let (s4, c) := adc d4 (q.l4 &&& m) c
  let (s5, _) := adc d5 (q.l5 &&& m) c
  ⟨s0, s1, s2, s3, s4, s5⟩

@[inline] def sub (a b : Fp) : Fp := subI a b

@[inline] def isZero (a : Fp) : Bool :=
  (a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) == 0

/-- `p - a`, or `0` for `a = 0`. -/
@[inline] def negI (a : Fp) : Fp :=
  let q := modulusWords
  let (d0, br) := sbb q.l0 a.l0 0
  let (d1, br) := sbb q.l1 a.l1 br
  let (d2, br) := sbb q.l2 a.l2 br
  let (d3, br) := sbb q.l3 a.l3 br
  let (d4, br) := sbb q.l4 a.l4 br
  let (d5, _) := sbb q.l5 a.l5 br
  -- `m` is all ones iff `a ≠ 0`.
  let m := 0 - ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) != 0).toUInt64
  ⟨d0 &&& m, d1 &&& m, d2 &&& m, d3 &&& m, d4 &&& m, d5 &&& m⟩

@[inline] def neg (a : Fp) : Fp := negI a

@[inline] def doubleI (a : Fp) : Fp := addI a a

@[inline] def double (a : Fp) : Fp := add a a

@[inline] def beq (a b : Fp) : Bool :=
  a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3 &&
    a.l4 == b.l4 && a.l5 == b.l5

instance : Add Fp := ⟨add⟩
instance : Sub Fp := ⟨sub⟩
instance : Mul Fp := ⟨mul⟩
instance : Neg Fp := ⟨neg⟩
instance : BEq Fp := ⟨beq⟩

/-! ## Conversions -/

/-- `n mod p` as a field element. Mirrors the spec's `Fp.ofNat`. -/
def ofNat (n : Nat) : Fp := mul (ofRaw (n % modulus)) R2

/-- The canonical integer in `[0, p)` that `a` stands for. -/
def toNat (a : Fp) : Nat := raw (mul a rawOne)

/-- `a` out of Montgomery form, as words. -/
@[inline] def decode (a : Fp) : Fp := mul a rawOne

/-- `(p - 1) / 2`, the largest value whose spec `signBit` is false. -/
def halfP : Fp := ofRaw
  0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd555

/-- Spec `Fp.signBit`: `y > p - y`, i.e. the decoded value exceeds
`(p - 1) / 2`. -/
def signBit (y : Fp) : Bool :=
  let v := decode y
  let (_, b) := sbb halfP.l0 v.l0 0
  let (_, b) := sbb halfP.l1 v.l1 b
  let (_, b) := sbb halfP.l2 v.l2 b
  let (_, b) := sbb halfP.l3 v.l3 b
  let (_, b) := sbb halfP.l4 v.l4 b
  let (_, b) := sbb halfP.l5 v.l5 b
  b != 0

/-- Parity of the decoded value (RFC 9380 `sgn0` on `Fp`). -/
def parity (y : Fp) : Bool := (decode y).l0 &&& 1 == 1

/-! ## Exponentiation by fixed 4-bit windows

Exponents are passed as base-16 digits, most significant first. Constant
exponents (inversion, square root) precompute their digits once at module
initialization. -/

/-- Base-16 digits of `e`, most significant first (`#[0]` for `e = 0`). -/
def nibbles (e : Nat) : ByteArray :=
  ⟨((List.range (e.log2 / 4 + 1)).reverse.map
    fun i => ((e >>> (4 * i)) % 16).toUInt8).toArray⟩

/-- `#[a⁰, a¹, …, a¹⁵]`. -/
def powTable (a : Fp) : Array Fp := Id.run do
  let mut t : Array Fp := Array.mkEmpty 16
  let mut acc := one
  for _ in [0:16] do
    t := t.push acc
    acc := mul acc a
  return t

/-- `a ^ e` where `ds` are the base-16 digits of `e`, most significant
first. The four squarings per digit are inlined, so the loop allocates
only when it multiplies by a table entry, and that product takes the
exclusive accumulator as its second argument, whose memory it reuses. -/
def powNibbles (a : Fp) (ds : ByteArray) : Fp := Id.run do
  let tbl := powTable a
  let mut acc := one
  for i in [0:ds.size] do
    acc := mulI acc acc
    acc := mulI acc acc
    acc := mulI acc acc
    acc := mulI acc acc
    let d := ds.get! i
    if d != 0 then acc := mul tbl[d.toNat]! acc
  return acc

/-- `a ^ e` for an arbitrary exponent. -/
def powNat (a : Fp) (e : Nat) : Fp := powNibbles a (nibbles e)

/-! ## Sliding-window exponentiation for fixed exponents

A fixed exponent is compiled once into a window program: an initial odd
digit `d0` (`a^d0` is the starting accumulator, so nothing is squared from
`one`) and steps `(n, d)` meaning "square `n` times, then multiply by
`a^d`" (`d = 0`: no multiplication, a final run of squarings). Digits are odd
and below 32, so the table holds only `a, a³, …, a³¹`. -/

/-- A window program: the initial digit and the remaining steps. -/
abbrev WinProg := Nat × Array (Nat × Nat)

/-- Shrink a window `(v, w)` (`w` bits, value `v`) until it is odd: its
trailing zero bits go back to the pending run of squarings. -/
def winTrim : Nat → Nat → Nat → Nat × Nat
  | 0, v, w => (v, w)
  | f + 1, v, w => if w > 1 && v % 2 == 0 then winTrim f (v / 2) (w - 1) else (v, w)

/-- Left-to-right scan of the bits of `e` below position `k` (structural on
`fuel`, one bit at least per round): `z` zero bits are pending, `acc` holds
the steps so far. -/
def winGo (e : Nat) : Nat → Nat → Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | 0, _, z, acc => if z == 0 then acc else acc.push (z, 0)
  | fuel + 1, k, z, acc =>
    if k == 0 then (if z == 0 then acc else acc.push (z, 0))
    else if (e >>> (k - 1)) % 2 == 0 then winGo e fuel (k - 1) (z + 1) acc
    else
      let w := min 5 k
      let (v, w) := winTrim 5 ((e >>> (k - w)) % 2 ^ w) w
      winGo e fuel (k - w) 0 (acc.push (z + w, v))

/-- The window program of `e` (`(0, #[])` for `e = 0`). -/
def windows (e : Nat) : WinProg :=
  let steps := winGo e (e.log2 + 1) (e.log2 + 1) 0 #[]
  if h : steps.size = 0 then (0, #[]) else (steps[0].2, steps.extract 1 steps.size)

/-- `#[a, a³, …, a³¹]`, built by one squaring and fifteen products. -/
def oddPush (a2 : Fp) : Nat → Fp → Array Fp → Array Fp
  | 0, _, t => t
  | k + 1, cur, t =>
    let nx := mul cur a2
    oddPush a2 k nx (t.push nx)

def oddTable (a : Fp) : Array Fp := oddPush (sqr a) 15 a #[a]

/-- `n` squarings, in place on an exclusive accumulator; the common short
runs are unrolled so the products fuse into straight-line code. -/
def sqrN (acc : Fp) : Nat → Fp
  | 0 => acc
  | 1 => mulI acc acc
  | 2 => let x := mulI acc acc; mulI x x
  | 3 => let x := mulI acc acc; let x := mulI x x; mulI x x
  | 4 => let x := mulI acc acc; let x := mulI x x; let x := mulI x x; mulI x x
  | 5 =>
    let x := mulI acc acc; let x := mulI x x; let x := mulI x x; let x := mulI x x; mulI x x
  | n + 6 =>
    let x := mulI acc acc; let x := mulI x x; let x := mulI x x; let x := mulI x x
    let x := mulI x x; Nat.repeat (fun x => mulI x x) (n + 1) x

/-- One program step: `n` squarings of the exclusive accumulator, then a
table product (the accumulator is the second argument, whose memory `mul`
reuses) unless `d = 0`. -/
@[inline] def winStep (tbl : Array Fp) (acc : Fp) (st : Nat × Nat) : Fp :=
  let r := sqrN acc st.1
  if st.2 != 0 then mul tbl[st.2 >>> 1]! r else r

/-- `a ^ e` for the `e` that `prog = windows e` was built from. -/
def powWin (a : Fp) (prog : WinProg) : Fp :=
  let tbl := oddTable a
  prog.2.foldl (winStep tbl) tbl[prog.1 >>> 1]!

/-- Window program of `(p + 1) / 4` (square root, valid since `p ≡ 3 (mod 4)`). -/
def sqrtWin : WinProg := windows ((modulus + 1) / 4)

/-- Window program of `(p - 3) / 4` (`Fp2` square root). -/
def invSqrtWin : WinProg := windows ((modulus - 3) / 4)

/-! ## Inversion

Kaliski's almost Montgomery inverse. For a canonical nonzero `a` whose words
spell `A < p`, a binary extended GCD runs on the pair `(p, A)` with state
`(u, v, r, s, k)`, starting from `(p, A, 0, 1, 0)`. Each step halves `u` or
`v` (moving the power of two into `s` or `r` and into `k`), or subtracts the
smaller of the two odd values from the larger (adding `s` to `r`, or `r` to
`s`). It stops when `u = v = 1` and returns `(s, k)`.

The invariant, over the integers, is
`p = u·s + v·r`, `A·r + u·2^k ≡ 0` and `A·s ≡ v·2^k (mod p)`,
`1 ≤ u ≤ p`, `1 ≤ v < p`, and `u·v·2^k ≤ p·A`. At the stop it gives
`A·s ≡ 2^k (mod p)` with `s < p`.

The last bound also gives `k < 762` (since `p·A < 2^762`), so the `UInt64`
counter never wraps and `s`, `r` stay below `2^384`. Every iteration that
does not stop adds at least one to `k`, so the loop stops within `762`
iterations; the fuel `1000` is only there to make the recursion structural
and is never exhausted.

The result is `s · 2^(768 - k) mod p`: with `a = A·R⁻¹` in Montgomery form,
`s ≡ 2^k · A⁻¹`, so `s · 2^(768 - k) · R⁻¹ ≡ A⁻¹ · R`, which is the
Montgomery form of `a⁻¹`. The correction `· 2^j` splits `j` into three
pieces of at most 256, each two Montgomery products (by `R²`, then by
`2^j'`; `mulPow2`).

The loop is **variable time**: its iteration count and branches depend on
the input. That is acceptable here: the library only verifies signatures and
aggregates public keys, so every value that is ever inverted is public; it
never signs. (Fermat inversion, which it replaces, is constant time in the
input but costs about three times as much.)

The loop keeps every limb an unboxed `UInt64` argument: passing `Fp`
objects around the loop allocates on every iteration. -/

namespace Inv

/-- Trailing zeros of a nonzero word, by binary search with selects. -/
@[inline] def ctz (x : UInt64) : UInt64 :=
  let z := (x &&& 0xFFFFFFFF) == 0
  let n : UInt64 := if z then 32 else 0
  let x := if z then x >>> 32 else x
  let z := (x &&& 0xFFFF) == 0
  let n := if z then n + 16 else n
  let x := if z then x >>> 16 else x
  let z := (x &&& 0xFF) == 0
  let n := if z then n + 8 else n
  let x := if z then x >>> 8 else x
  let z := (x &&& 0xF) == 0
  let n := if z then n + 4 else n
  let x := if z then x >>> 4 else x
  let z := (x &&& 0x3) == 0
  let n := if z then n + 2 else n
  let x := if z then x >>> 2 else x
  if (x &&& 0x1) == 0 then n + 1 else n

/-- A shift count `t ∈ [1, 63]` with `2^t ∣ d` for a nonzero even `d`: its
trailing-zero count when the low word is nonzero, and `63` when it is zero
(still an exact shift; the loop then simply takes the even branch again). -/
@[inline] def tz (d : Fp) : UInt64 := if d.l0 == 0 then 63 else ctz d.l0

/-- `a / 2^t` for `t ∈ [1, 63]`. -/
@[inline] def shr (a : Fp) (t : UInt64) : Fp :=
  let s := 64 - t
  ⟨(a.l0 >>> t) ||| (a.l1 <<< s), (a.l1 >>> t) ||| (a.l2 <<< s), (a.l2 >>> t) ||| (a.l3 <<< s),
   (a.l3 >>> t) ||| (a.l4 <<< s), (a.l4 >>> t) ||| (a.l5 <<< s), a.l5 >>> t⟩

/-- `a · 2^t` for `t ∈ [1, 63]`, when that is below `2^384`. -/
@[inline] def shl (a : Fp) (t : UInt64) : Fp :=
  let s := 64 - t
  ⟨a.l0 <<< t, (a.l1 <<< t) ||| (a.l0 >>> s), (a.l2 <<< t) ||| (a.l1 >>> s),
   (a.l3 <<< t) ||| (a.l2 >>> s), (a.l4 <<< t) ||| (a.l3 >>> s), (a.l5 <<< t) ||| (a.l4 >>> s)⟩

/-- `a + b` over six words, dropping the carry (callers keep the sum below
`2^384`). -/
@[inline] def add6 (a b : Fp) : Fp := addRaw a b

/-- `a - b` over six words and the final borrow (`1` iff `a < b`). -/
@[inline] def sub6 (a b : Fp) : Fp × UInt64 :=
  let (d0, br) := sbb a.l0 b.l0 0
  let (d1, br) := sbb a.l1 b.l1 br
  let (d2, br) := sbb a.l2 b.l2 br
  let (d3, br) := sbb a.l3 b.l3 br
  let (d4, br) := sbb a.l4 b.l4 br
  let (d5, br) := sbb a.l5 b.l5 br
  (⟨d0, d1, d2, d3, d4, d5⟩, br)

/-- The loop of the algorithm above, on `(u, v, r, s, k)` with the limbs of
each vector as separate arguments. It returns `(s, k)` at the stop `u = v`.
`fuel` only makes it structurally recursive. -/
def go (fuel : Nat) (u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    r0 r1 r2 r3 r4 r5 s0 s1 s2 s3 s4 s5 k : UInt64) : Fp × UInt64 :=
  let s : Fp := ⟨s0, s1, s2, s3, s4, s5⟩
  match fuel with
  | 0 => (s, k)
  | fuel + 1 =>
    let u : Fp := ⟨u0, u1, u2, u3, u4, u5⟩
    let v : Fp := ⟨v0, v1, v2, v3, v4, v5⟩
    let r : Fp := ⟨r0, r1, r2, r3, r4, r5⟩
    if u0 &&& 1 == 0 then
      let t := tz u
      let u' := shr u t
      let s' := shl s t
      go fuel u'.l0 u'.l1 u'.l2 u'.l3 u'.l4 u'.l5 v0 v1 v2 v3 v4 v5
        r0 r1 r2 r3 r4 r5 s'.l0 s'.l1 s'.l2 s'.l3 s'.l4 s'.l5 (k + t)
    else if v0 &&& 1 == 0 then
      let t := tz v
      let v' := shr v t
      let r' := shl r t
      go fuel u0 u1 u2 u3 u4 u5 v'.l0 v'.l1 v'.l2 v'.l3 v'.l4 v'.l5
        r'.l0 r'.l1 r'.l2 r'.l3 r'.l4 r'.l5 s0 s1 s2 s3 s4 s5 (k + t)
    else
      let (d, br) := sub6 u v
      if br == 0 then
        if (d.l0 ||| d.l1 ||| d.l2 ||| d.l3 ||| d.l4 ||| d.l5) == 0 then (s, k)
        else
          let t := tz d
          let u' := shr d t
          let r' := add6 r s
          let s' := shl s t
          go fuel u'.l0 u'.l1 u'.l2 u'.l3 u'.l4 u'.l5 v0 v1 v2 v3 v4 v5
            r'.l0 r'.l1 r'.l2 r'.l3 r'.l4 r'.l5 s'.l0 s'.l1 s'.l2 s'.l3 s'.l4 s'.l5 (k + t)
      else
        let (d, _) := sub6 v u
        let t := tz d
        let v' := shr d t
        let r' := shl r t
        let s' := add6 r s
        go fuel u0 u1 u2 u3 u4 u5 v'.l0 v'.l1 v'.l2 v'.l3 v'.l4 v'.l5
          r'.l0 r'.l1 r'.l2 r'.l3 r'.l4 r'.l5 s'.l0 s'.l1 s'.l2 s'.l3 s'.l4 s'.l5 (k + t)

/-- The word vector of `2^j`, for `j < 384`. -/
@[inline] def pow2 (j : UInt64) : Fp :=
  let w := j >>> 6
  let b : UInt64 := 1 <<< (j &&& 63)
  ⟨if w == 0 then b else 0, if w == 1 then b else 0, if w == 2 then b else 0,
   if w == 3 then b else 0, if w == 4 then b else 0, if w == 5 then b else 0⟩

/-- `x · 2^j` for `j ≤ 256`: `mul (mul x R2) (pow2 j)` is `x · R · 2^j / R`
(`mul` needs only its second argument canonical, and `2^256 < p`). -/
@[inline] def mulPow2Small (x : Fp) (j : Nat) : Fp := mul (mul x R2) (pow2 j.toUInt64)

/-- `x · 2^j mod p` for `j ≤ 768`, in three pieces of at most 256 (no
recursion, so nothing to prove about termination here). -/
def mulPow2 (x : Fp) (j : Nat) : Fp :=
  let j1 := min j 256
  let j2 := min (j - j1) 256
  let j3 := j - j1 - j2
  mulPow2Small (mulPow2Small (mulPow2Small x j1) j2) j3

end Inv

/-- Multiplicative inverse by Kaliski's almost Montgomery inverse (see
above); maps `0` to `0`, like the spec. Variable time, which is fine for the
public values this library inverts. -/
def inverse (a : Fp) : Fp :=
  if a.isZero then zero else
  let (x, k) := Inv.go 1000 P0 P1 P2 P3 P4 P5 a.l0 a.l1 a.l2 a.l3 a.l4 a.l5
    0 0 0 0 0 0 1 0 0 0 0 0 0
  Inv.mulPow2 x (768 - k.toNat)

instance (priority := high) : Div Fp := ⟨fun a b => a * b.inverse⟩

/-- Spec `Fp.sqrt`: the candidate `a^((p+1)/4)` if it squares back to `a`. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand := powWin a sqrtWin
  if (cand * cand).beq a then .ok cand else .error .notASquare

/-! ## Byte encoding -/

/-- Big-endian 64-bit word at `b[off..off+8]`. -/
@[inline] def be64 (b : ByteArray) (off : Nat) : UInt64 :=
  ((b.get! off).toUInt64 <<< 56) ||| ((b.get! (off + 1)).toUInt64 <<< 48) |||
  ((b.get! (off + 2)).toUInt64 <<< 40) ||| ((b.get! (off + 3)).toUInt64 <<< 32) |||
  ((b.get! (off + 4)).toUInt64 <<< 24) ||| ((b.get! (off + 5)).toUInt64 <<< 16) |||
  ((b.get! (off + 6)).toUInt64 <<< 8) ||| (b.get! (off + 7)).toUInt64

/-- Spec `Fp.fromBytesBE`: 48 big-endian bytes encoding an integer below `p`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fp :=
  if b.size ≠ 48 then .error .nonCanonicalFieldElement
  else
    let t : Fp := ⟨be64 b 40, be64 b 32, be64 b 24, be64 b 16, be64 b 8, be64 b 0⟩
    let (_, br) := subP t
    if br == 0 then .error .nonCanonicalFieldElement else .ok (mul t R2)

/-- `2^256 · R² mod p`: `mul a C256` sends a 256-bit integer `a` to
`a · 2^256` in Montgomery form. -/
def C256 : Fp := ofRaw
  0x10a8c1a49a064ff0a85a3f35446d0bcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58

/-- The 64 big-endian bytes at `b[off..off+64]`, as an integer modulo `p`
(RFC 9380 `hash_to_field`'s OS2IP-and-reduce). With `N = A·2^256 + B`,
both halves below `p`, this is `A·2^256 + B` assembled in Montgomery form,
without big-number arithmetic. -/
def ofBytes64BE (b : ByteArray) (off : Nat) : Fp :=
  let a : Fp := ⟨be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off, 0, 0⟩
  let c : Fp := ⟨be64 b (off + 56), be64 b (off + 48), be64 b (off + 40), be64 b (off + 32), 0, 0⟩
  add (mul a C256) (mul c R2)

/-- Append the 8 big-endian bytes of `w`. -/
@[inline] def pushBE64 (out : ByteArray) (w : UInt64) : ByteArray :=
  out |>.push (w >>> 56).toUInt8 |>.push (w >>> 48).toUInt8
      |>.push (w >>> 40).toUInt8 |>.push (w >>> 32).toUInt8
      |>.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8
      |>.push (w >>> 8).toUInt8 |>.push w.toUInt8

/-- Spec `Fp.toBytesBE`: 48 big-endian bytes. -/
def toBytesBE (a : Fp) : ByteArray :=
  let v := decode a
  (ByteArray.emptyWithCapacity 48)
    |> (pushBE64 · v.l5) |> (pushBE64 · v.l4) |> (pushBE64 · v.l3)
    |> (pushBE64 · v.l2) |> (pushBE64 · v.l1) |> (pushBE64 · v.l0)

end Fp

end EthLibImpl.Cryptography.Bls
