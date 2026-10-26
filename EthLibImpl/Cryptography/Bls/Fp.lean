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

/-- `t - p` and the final borrow (`1` iff `t < p`). -/
@[inline] def subP (t : Fp) : Fp × UInt64 :=
  let (d0, b) := sbb t.l0 P0 0
  let (d1, b) := sbb t.l1 P1 b
  let (d2, b) := sbb t.l2 P2 b
  let (d3, b) := sbb t.l3 P3 b
  let (d4, b) := sbb t.l4 P4 b
  let (d5, b) := sbb t.l5 P5 b
  (⟨d0, d1, d2, d3, d4, d5⟩, b)

/-- `t + p` modulo `2^384`. -/
@[inline] def addP (t : Fp) : Fp :=
  let (s0, c) := adc t.l0 P0 0
  let (s1, c) := adc t.l1 P1 c
  let (s2, c) := adc t.l2 P2 c
  let (s3, c) := adc t.l3 P3 c
  let (s4, c) := adc t.l4 P4 c
  let (s5, _) := adc t.l5 P5 c
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
sixth it equals `a · b · R⁻¹` modulo `p`. -/

/-- Seven-word accumulator between the two halves of a row. -/
structure Acc7 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64

/-- `t + a · b` for a six-word `t` and a single word `a`. -/
@[inline] def mulRow (t : Fp) (a : UInt64) (b : Fp) : Acc7 :=
  let (r0, c) := mac t.l0 a b.l0 0
  let (r1, c) := mac t.l1 a b.l1 c
  let (r2, c) := mac t.l2 a b.l2 c
  let (r3, c) := mac t.l3 a b.l3 c
  let (r4, c) := mac t.l4 a b.l4 c
  let (r5, c) := mac t.l5 a b.l5 c
  ⟨r0, r1, r2, r3, r4, r5, c⟩

/-- `(t + m · p) / 2^64` with `m = t₀ · N0 mod 2^64`, so the division is
exact. -/
@[inline] def redRow (t : Acc7) : Fp :=
  let m := t.w0 * N0
  let (_, c) := mac t.w0 m P0 0
  let (r0, c) := mac t.w1 m P1 c
  let (r1, c) := mac t.w2 m P2 c
  let (r2, c) := mac t.w3 m P3 c
  let (r3, c) := mac t.w4 m P4 c
  let (r4, c) := mac t.w5 m P5 c
  ⟨r0, r1, r2, r3, r4, t.w6 + c⟩

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

/-- Field squaring. -/
@[inline] def sqr (a : Fp) : Fp := mul a a

/-! ## Additive operations -/

@[inline] def addI (a b : Fp) : Fp :=
  let (s0, c) := adc a.l0 b.l0 0
  let (s1, c) := adc a.l1 b.l1 c
  let (s2, c) := adc a.l2 b.l2 c
  let (s3, c) := adc a.l3 b.l3 c
  let (s4, c) := adc a.l4 b.l4 c
  let (s5, _) := adc a.l5 b.l5 c
  reduceOnce ⟨s0, s1, s2, s3, s4, s5⟩

def add (a b : Fp) : Fp := addI a b

/-- `a - b`, adding `p` back (masked) when the subtraction borrows. -/
@[inline] def subI (a b : Fp) : Fp :=
  let (d0, br) := sbb a.l0 b.l0 0
  let (d1, br) := sbb a.l1 b.l1 br
  let (d2, br) := sbb a.l2 b.l2 br
  let (d3, br) := sbb a.l3 b.l3 br
  let (d4, br) := sbb a.l4 b.l4 br
  let (d5, br) := sbb a.l5 b.l5 br
  let m := 0 - br
  let (s0, c) := adc d0 (P0 &&& m) 0
  let (s1, c) := adc d1 (P1 &&& m) c
  let (s2, c) := adc d2 (P2 &&& m) c
  let (s3, c) := adc d3 (P3 &&& m) c
  let (s4, c) := adc d4 (P4 &&& m) c
  let (s5, _) := adc d5 (P5 &&& m) c
  ⟨s0, s1, s2, s3, s4, s5⟩

def sub (a b : Fp) : Fp := subI a b

@[inline] def isZero (a : Fp) : Bool :=
  (a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) == 0

/-- `p - a`, or `0` for `a = 0`. -/
@[inline] def negI (a : Fp) : Fp :=
  let (d0, br) := sbb P0 a.l0 0
  let (d1, br) := sbb P1 a.l1 br
  let (d2, br) := sbb P2 a.l2 br
  let (d3, br) := sbb P3 a.l3 br
  let (d4, br) := sbb P4 a.l4 br
  let (d5, _) := sbb P5 a.l5 br
  -- `m` is all ones iff `a ≠ 0`.
  let m := 0 - ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) != 0).toUInt64
  ⟨d0 &&& m, d1 &&& m, d2 &&& m, d3 &&& m, d4 &&& m, d5 &&& m⟩

def neg (a : Fp) : Fp := negI a

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
first. -/
def powNibbles (a : Fp) (ds : ByteArray) : Fp := Id.run do
  let tbl := powTable a
  let mut acc := one
  for i in [0:ds.size] do
    acc := sqr (sqr (sqr (sqr acc)))
    let d := ds.get! i
    if d != 0 then acc := mul acc tbl[d.toNat]!
  return acc

/-- `a ^ e` for an arbitrary exponent. -/
def powNat (a : Fp) (e : Nat) : Fp := powNibbles a (nibbles e)

/-- Digits of `p - 2` (Fermat inversion). -/
def invDigits : ByteArray := nibbles (modulus - 2)

/-- Digits of `(p + 1) / 4` (square root, valid since `p ≡ 3 (mod 4)`). -/
def sqrtDigits : ByteArray := nibbles ((modulus + 1) / 4)

/-- Multiplicative inverse by Fermat; maps `0` to `0`, like the spec. -/
def inverse (a : Fp) : Fp := powNibbles a invDigits

instance (priority := high) : Div Fp := ⟨fun a b => a * b.inverse⟩

/-- Spec `Fp.sqrt`: the candidate `a^((p+1)/4)` if it squares back to `a`. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand := powNibbles a sqrtDigits
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
