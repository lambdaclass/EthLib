import EthLibImpl.Cryptography.Bls.Fp
import EthLibImpl.Cryptography.Proofs.Bls.Limbs
import EthLib.Cryptography.Proofs.Bls.FpZMod
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.IdLoops

/-!
# Proofs: the Montgomery base field computes the spec's `Fp`

`EthLibImpl.Cryptography.Bls.Fp` stores a field element as six `UInt64`
words holding `a · R mod p` with `R = 2^384`. This file proves that every
operation of that module computes the spec field
`EthLib.Cryptography.Bls.Fp` (`Fin p`, definitionally `ZMod p`).

## The decoding map

* `raw a` is the integer the six words spell (no Montgomery decoding).
* `Canonical a` is `a.raw < p`; every operation preserves it.
* `val a = Fp.ofNat a.raw * rInv` (spec field) where `rInv = R⁻¹ mod p`;
  `val_eq_natCast` gives the `Nat.cast` form `(a.raw : S) * rInv`.

On canonical inputs `val` is injective (`val_inj`), and every operation is
a homomorphism for it: `val_mulI`, `val_addI`, `val_subI`, `val_negI`,
`val_doubleI` (and the same for the plain wrappers `mul`, `add`, ...).

## Doing algebra downstream

The spec field's `+`, `*`, `-`, `0`, `1` are core's `Fin` instances, on
which Mathlib's `ring` does not run (and `map_sub`/`map_neg` do not
match them). Ring reasoning goes through
`EthLib.Cryptography.Bls.Fp.toZMod` (a ring isomorphism that is the
identity): `apply toZMod.injective`, push `toZMod` through with the `rfl`
lemmas `toZMod_add`, `toZMod_sub`, `toZMod_neg`, `toZMod_mul`,
`toZMod_zero`, `toZMod_one`, `toZMod_pow`, `toZMod_ofNat` (namespace
`EthLib.Cryptography.Bls.Fp`, first section below), and finish with
`ring` / `linear_combination` over `ZMod p`. On the implementation side
`toZ_val` (`toZMod a.val = a.raw * toZMod rInv`) is the entry point.
Powers `x ^ n` on the spec field are Mathlib's monoid power on the scoped
field instance (`powNat_eq_monoid_pow`); this file removes core's grind
`HPow (Fin n) Nat` instances, as FrZMod does.

## Coverage

Arithmetic (`mul`, `sqr`, `add`, `sub`, `neg`, `double`, `ofNat`,
`powNat`, `inverse`, `sqrt`), predicates (`isZero`, `beq`, `signBit`,
`parity`), conversions (`decode`, `toNat`) and the byte codecs
(`fromBytesBE`, `toBytesBE`, `ofBytes64BE`) all match the spec. The
statements about `decode`, `toNat`, `toBytesBE`, `signBit` and `parity`
need no canonicity hypothesis, since `decode` (a Montgomery product by
`rawOne`) canonicalizes any input.

## Proof structure

The carry chains (`sbb`, `adc`, `mac` over six words) are restated as
projection-style helpers (`sbb6`, `adc6`, `mulRow_eq`, `redRow_eq`) that
are definitionally the implementation's destructuring `let`s; their
`Nat` specifications follow from `Limbs`' word lemmas by `omega`, with
products of words treated as atoms. Montgomery multiplication keeps the
accumulator below `2p` after every row, and one conditional subtraction
(`reduceOnce`) then lands in `[0, p)`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLib.Cryptography.Bls.Fp

/-! ## `toZMod` against the spec's core `Fin` operations

The spec field's `+`, `*`, `-`, `0`, `1` are core's `Fin` instances, which
Mathlib's `ring` does not see as ring operations. `toZMod` is the identity
ring isomorphism to `ZMod p`, and these `rfl` lemmas push it through the
`Fin` operations so that ring reasoning can happen in `ZMod p`. -/

theorem toZMod_add (x y : Fp) : toZMod (x + y) = toZMod x + toZMod y := rfl

theorem toZMod_sub (x y : Fp) : toZMod (x - y) = toZMod x - toZMod y := rfl

theorem toZMod_neg (x : Fp) : toZMod (-x) = -toZMod x := rfl

theorem toZMod_mul (x y : Fp) : toZMod (x * y) = toZMod x * toZMod y := rfl

theorem toZMod_zero : toZMod 0 = 0 := rfl

theorem toZMod_one : toZMod 1 = 1 := rfl

/-- Monoid power (on the scoped field instance) commutes with `toZMod`. -/
theorem toZMod_pow (x : Fp) (n : Nat) : toZMod (x ^ n) = toZMod x ^ n := rfl

theorem toZMod_ofNat (n : Nat) : toZMod (Fp.ofNat n) = (n : ZMod modulus) := by
  rw [ofNat_eq_natCast]; rfl

theorem toZMod_mk (n : Nat) (h : n < modulus) : toZMod (⟨n, h⟩ : Fp) = (n : ZMod modulus) := by
  apply ZMod.val_injective
  show (⟨n, h⟩ : Fp).val = _
  rw [ZMod.val_natCast_of_lt h]

/-- `ZMod.val` after `toZMod` is `Fin.val`. Rewrite with this rather than
relying on the defeq: the kernel can recurse deeply unfolding a concrete
argument. -/
theorem val_toZMod (x : Fp) : (toZMod x).val = x.val := rfl

/-- The spec's `powNat` is Mathlib's monoid power on the scoped field
instance (FpZMod's `powNat_eq_pow` states it with core's grind
`HPow (Fin n) Nat` instance instead). -/
theorem powNat_eq_monoid_pow (x : Fp) (n : Nat) : Fp.powNat x n = x ^ n :=
  powNat_eq_zmod_pow x n

theorem beq_eq_true_iff (x y : Fp) : Fp.beq x y = true ↔ x = y := by
  simp [Fp.beq, Fin.ext_iff]

end EthLib.Cryptography.Bls.Fp

namespace EthLibImpl.Cryptography.Bls.Fp

open Limbs
open scoped EthLib.Cryptography.Bls.Fp
open EthLib.Cryptography.Bls.Fp (toZMod toZMod_add toZMod_sub toZMod_neg toZMod_mul toZMod_zero
  toZMod_one toZMod_pow toZMod_ofNat toZMod_mk val_toZMod powNat_eq_monoid_pow beq_eq_true_iff)

local notation "S" => EthLib.Cryptography.Bls.Fp
local notation "Z" => ZMod EthLib.Cryptography.Bls.Fp.modulus

/-! ## Words and `raw` -/

/-- The implementation's modulus is the spec's. -/
theorem modulus_eq : Fp.modulus = EthLib.Cryptography.Bls.Fp.modulus := rfl

/-- A word vector is canonical when the integer it spells is below `p`. -/
def Canonical (a : Fp) : Prop := a.raw < modulus

theorem raw_mk (x0 x1 x2 x3 x4 x5 : UInt64) :
    (⟨x0, x1, x2, x3, x4, x5⟩ : Fp).raw = x0.toNat + 2^64 * (x1.toNat + 2^64 * (x2.toNat +
      2^64 * (x3.toNat + 2^64 * (x4.toNat + 2^64 * x5.toNat)))) := rfl

/-- Six words spell an integer below `2^384`. -/
theorem raw_lt (a : Fp) : a.raw < 2 ^ 384 := by
  have := a.l0.toNat_lt; have := a.l1.toNat_lt; have := a.l2.toNat_lt
  have := a.l3.toNat_lt; have := a.l4.toNat_lt; have := a.l5.toNat_lt
  unfold raw; omega

/-- `ofRaw` is a right inverse of `raw` below `2^384`. -/
theorem raw_ofRaw {n : Nat} (h : n < 2 ^ 384) : (ofRaw n).raw = n := by
  simp only [raw, ofRaw, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  omega

/-- `raw` is injective: the words are the base-`2^64` digits. -/
theorem eq_of_raw_eq {a b : Fp} (h : a.raw = b.raw) : a = b := by
  have := a.l0.toNat_lt; have := a.l1.toNat_lt; have := a.l2.toNat_lt
  have := a.l3.toNat_lt; have := a.l4.toNat_lt; have := a.l5.toNat_lt
  have := b.l0.toNat_lt; have := b.l1.toNat_lt; have := b.l2.toNat_lt
  have := b.l3.toNat_lt; have := b.l4.toNat_lt; have := b.l5.toNat_lt
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := b
  simp only [raw] at *
  simp only [mk.injEq, ← UInt64.toNat_inj]
  omega

theorem raw_inj {a b : Fp} : a.raw = b.raw ↔ a = b :=
  ⟨eq_of_raw_eq, fun h => h ▸ rfl⟩

set_option exponentiation.threshold 512 in
theorem modulus_lt : modulus < 2 ^ 384 := by decide

set_option exponentiation.threshold 512 in
theorem modulus_lt_381 : modulus < 2 ^ 381 := by decide

/-! ## The decoding map `val` -/

/-- `R⁻¹ = (2^384)⁻¹` in the spec field. -/
def rInv : S :=
  ⟨0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820,
    by decide⟩

/-- The spec field element a word vector stands for: `raw · R⁻¹ mod p`. -/
def val (a : Fp) : S := EthLib.Cryptography.Bls.Fp.ofNat a.raw * rInv

/-- `val` in `Nat.cast` form. -/
theorem val_eq_natCast (a : Fp) : a.val = (a.raw : S) * rInv := by
  rw [val, EthLib.Cryptography.Bls.Fp.ofNat_eq_natCast]

set_option exponentiation.threshold 512 in
theorem toZ_rInv_nat : ((2 ^ 384 : Nat) : Z) * toZMod rInv = 1 := by
  decide

/-- `rInv` inverts `R = 2^384`. -/
theorem toZ_rInv : (2 : Z) ^ 384 * toZMod rInv = 1 := by
  have := toZ_rInv_nat; rwa [Nat.cast_pow, Nat.cast_ofNat] at this

/-- `val` seen in `ZMod p`: the entry point for ring reasoning. -/
theorem toZ_val (a : Fp) :
    toZMod a.val = (a.raw : Z) * toZMod rInv := by
  rw [val, map_mul, toZMod_ofNat]

/-- Two vectors have the same `val` iff their raw integers agree in `ZMod p`. -/
theorem val_eq_val_iff {a b : Fp} : a.val = b.val ↔ (a.raw : Z) = (b.raw : Z) := by
  rw [← toZMod.injective.eq_iff, toZ_val, toZ_val]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  constructor
  · intro h
    linear_combination R * h + ((b.raw : Z) - a.raw) * hr
  · intro h; rw [h]

/-- The `val` of a vector, determined by a `ZMod` value of its raw integer. -/
theorem val_eq_of_raw {a : Fp} {x : S}
    (h : (a.raw : Z) = (2 : Z) ^ 384 * toZMod x) : a.val = x := by
  apply toZMod.injective
  rw [toZ_val, h]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  generalize toZMod x = y
  linear_combination y * hr

/-- Product law from a `ZMod` fact about raw integers. -/
theorem val_mul_of {a b c : Fp} (h : (c.raw : Z) * (2 : Z) ^ 384 = (a.raw : Z) * b.raw) :
    c.val = a.val * b.val := by
  apply toZMod.injective
  rw [map_mul, toZ_val, toZ_val, toZ_val]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  linear_combination ri ^ 2 * h - (c.raw : Z) * ri * hr

/-- Sum law from a `ZMod` fact about raw integers. -/
theorem val_add_of {a b c : Fp} (h : (c.raw : Z) = (a.raw : Z) + b.raw) :
    c.val = a.val + b.val := by
  apply toZMod.injective
  rw [map_add, toZ_val, toZ_val, toZ_val, h]
  ring

/-- Difference law from a `ZMod` fact about raw integers. -/
theorem val_sub_of {a b c : Fp} (h : (c.raw : Z) = (a.raw : Z) - b.raw) :
    c.val = a.val - b.val := by
  apply toZMod.injective
  rw [toZMod_sub, toZ_val, toZ_val, toZ_val, h]
  ring

/-- Negation law from a `ZMod` fact about raw integers. -/
theorem val_neg_of {a c : Fp} (h : (c.raw : Z) = -(a.raw : Z)) :
    c.val = -a.val := by
  apply toZMod.injective
  rw [toZMod_neg, toZ_val, toZ_val, h]
  ring

/-- Canonical vectors with equal `val` are equal. -/
theorem val_inj {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    a.val = b.val ↔ a = b := by
  rw [val_eq_val_iff, ZMod.natCast_eq_natCast_iff', ← raw_inj]
  unfold Canonical at ha hb
  rw [← modulus_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The spec value's representative of a canonical vector is `0` iff the
vector is. -/
theorem val_eq_zero_iff {a : Fp} (ha : Canonical a) : a.val = 0 ↔ a.raw = 0 := by
  have h0 : (zero.raw : Z) = 0 := by simp [zero, raw]
  have hz : zero.val = 0 := by
    apply toZMod.injective
    rw [toZ_val, h0, zero_mul, map_zero]
  rw [← hz, val_inj ha (by unfold Canonical; decide), ← raw_inj]
  rfl

/-! ## Six-word carry chains

Projection-style restatements of the implementation's destructuring
carry chains. Each implementation function is definitionally one of these
(`subP_eq`, `addI_eq`, ...), so the chain specifications transfer by `rw`. -/

/-- `x - y` over six words, with the final borrow. -/
def sbb6 (x y : Fp) : Fp × UInt64 :=
  let r0 := sbb x.l0 y.l0 0
  let r1 := sbb x.l1 y.l1 r0.2
  let r2 := sbb x.l2 y.l2 r1.2
  let r3 := sbb x.l3 y.l3 r2.2
  let r4 := sbb x.l4 y.l4 r3.2
  let r5 := sbb x.l5 y.l5 r4.2
  (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, r5.2)

/-- `x + y` over six words, with the final carry. -/
def adc6 (x y : Fp) : Fp × UInt64 :=
  let r0 := adc x.l0 y.l0 0
  let r1 := adc x.l1 y.l1 r0.2
  let r2 := adc x.l2 y.l2 r1.2
  let r3 := adc x.l3 y.l3 r2.2
  let r4 := adc x.l4 y.l4 r3.2
  let r5 := adc x.l5 y.l5 r4.2
  (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, r5.2)

/-- The words of `p`. -/
def Pw : Fp := ⟨P0, P1, P2, P3, P4, P5⟩

/-- The words of `p`, each masked by `m`. -/
def maskP (m : UInt64) : Fp := ⟨P0 &&& m, P1 &&& m, P2 &&& m, P3 &&& m, P4 &&& m, P5 &&& m⟩

theorem Pw_raw : Pw.raw = modulus := rfl

theorem sbb6_spec (x y : Fp) :
    (sbb6 x y).1.raw + y.raw = x.raw + 2 ^ 384 * (sbb6 x y).2.toNat ∧
      (sbb6 x y).2.toNat ≤ 1 := by
  have h0 := sbb_spec x.l0 y.l0 0 (by decide)
  have h1 := sbb_spec x.l1 y.l1 _ h0.2
  have h2 := sbb_spec x.l2 y.l2 _ h1.2
  have h3 := sbb_spec x.l3 y.l3 _ h2.2
  have h4 := sbb_spec x.l4 y.l4 _ h3.2
  have h5 := sbb_spec x.l5 y.l5 _ h4.2
  simp only [sbb6, raw, UInt64.reduceToNat] at *
  omega

theorem adc6_spec (x y : Fp) :
    (adc6 x y).1.raw + 2 ^ 384 * (adc6 x y).2.toNat = x.raw + y.raw ∧
      (adc6 x y).2.toNat ≤ 1 := by
  have h0 := adc_spec x.l0 y.l0 0 (by decide)
  have h1 := adc_spec x.l1 y.l1 _ h0.2
  have h2 := adc_spec x.l2 y.l2 _ h1.2
  have h3 := adc_spec x.l3 y.l3 _ h2.2
  have h4 := adc_spec x.l4 y.l4 _ h3.2
  have h5 := adc_spec x.l5 y.l5 _ h4.2
  simp only [adc6, raw, UInt64.reduceToNat] at *
  omega

/-- A borrow or carry of at most one is `0` or `1`. -/
theorem eq_zero_or_one {c : UInt64} (h : c.toNat ≤ 1) : c = 0 ∨ c = 1 := by
  rcases (show c.toNat = 0 ∨ c.toNat = 1 by omega) with h | h
  · exact Or.inl (UInt64.toNat_inj.mp h)
  · exact Or.inr (UInt64.toNat_inj.mp h)

theorem subP_eq (t : Fp) : subP t = sbb6 t Pw := rfl

theorem addP_eq (t : Fp) : addP t = (adc6 t Pw).1 := rfl

theorem reduceOnce_eq (t : Fp) :
    reduceOnce t = select (0 - (sbb6 t Pw).2) (sbb6 t Pw).1 t := rfl

theorem addI_eq (a b : Fp) : addI a b = reduceOnce (adc6 a b).1 := rfl

theorem subI_eq (a b : Fp) :
    subI a b = (adc6 (sbb6 a b).1 (maskP (0 - (sbb6 a b).2))).1 := rfl

theorem negI_eq (a : Fp) : negI a =
    let m := 0 - ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) != 0).toUInt64
    let d := (sbb6 Pw a).1
    ⟨d.l0 &&& m, d.l1 &&& m, d.l2 &&& m, d.l3 &&& m, d.l4 &&& m, d.l5 &&& m⟩ := rfl

/-! ## Word-vector helpers: `select`, `subP`, `addP`, `reduceOnce` -/

/-- `select` with the zero mask returns its first vector. -/
theorem select_zero (a b : Fp) : select 0 a b = a := by
  simp [select]

/-- `select` with the all-ones mask returns its second vector. -/
theorem select_ones (a b : Fp) : select (0 - 1) a b = b := by
  simp [select, ← UInt64.xor_assoc]

set_option exponentiation.threshold 512 in
/-- `subP t` is `t - p` modulo `2^384`, with borrow `1` iff `t < p`. -/
theorem subP_spec (t : Fp) :
    (subP t).1.raw + modulus = t.raw + 2 ^ 384 * (subP t).2.toNat ∧
      ((subP t).2 = 1 ↔ t.raw < modulus) ∧ ((subP t).2 = 0 ↔ modulus ≤ t.raw) := by
  rw [subP_eq]
  obtain ⟨h1, h2⟩ := sbb6_spec t Pw
  rw [Pw_raw] at h1
  have hd := raw_lt (sbb6 t Pw).1
  have ht := raw_lt t
  have hp := modulus_lt
  rcases eq_zero_or_one h2 with h | h <;> rw [h] at h1 ⊢ <;> simp at h1 ⊢ <;> omega

/-- `addP t` is `t + p` modulo `2^384`. -/
theorem addP_raw (t : Fp) : (addP t).raw = (t.raw + modulus) % 2 ^ 384 := by
  rw [addP_eq]
  obtain ⟨h1, h2⟩ := adc6_spec t Pw
  rw [Pw_raw] at h1
  have hd := raw_lt (adc6 t Pw).1
  omega

/-- One conditional subtraction maps `[0, 2p)` onto `[0, p)`. -/
theorem reduceOnce_raw (t : Fp) (h : t.raw < 2 * modulus) :
    (reduceOnce t).raw = t.raw % modulus := by
  rw [reduceOnce_eq]
  have hs := subP_spec t
  rw [subP_eq] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  generalize sbb6 t Pw = r at *
  obtain ⟨d, br⟩ := r
  simp only at *
  have hp : 0 < modulus := by decide
  by_cases hlt : t.raw < modulus
  · rw [h2.mpr hlt, select_ones, Nat.mod_eq_of_lt hlt]
  · rw [h3.mpr (by omega), show (0 : UInt64) - 0 = 0 from rfl, select_zero]
    have : br = 0 := h3.mpr (by omega)
    rw [this] at h1
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at h1
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem reduceOnce_canonical (t : Fp) (h : t.raw < 2 * modulus) : Canonical (reduceOnce t) := by
  unfold Canonical; rw [reduceOnce_raw t h]; exact Nat.mod_lt _ (by decide)

/-! ## Montgomery multiplication -/

/-- The integer a seven-word accumulator spells. -/
def Acc7.val (t : Acc7) : Nat :=
  t.w0.toNat + 2^64 * (t.w1.toNat + 2^64 * (t.w2.toNat + 2^64 * (t.w3.toNat +
    2^64 * (t.w4.toNat + 2^64 * (t.w5.toNat + 2^64 * t.w6.toNat)))))

theorem mulRow_eq (t : Fp) (a : UInt64) (b : Fp) : mulRow t a b =
    let s0 := adc t.l0 (a * b.l0) 0
    let s1 := adc t.l1 (a * b.l1) s0.2
    let s2 := adc t.l2 (a * b.l2) s1.2
    let s3 := adc t.l3 (a * b.l3) s2.2
    let s4 := adc t.l4 (a * b.l4) s3.2
    let s5 := adc t.l5 (a * b.l5) s4.2
    let u1 := adc s1.1 (mulHi a b.l0) 0
    let u2 := adc s2.1 (mulHi a b.l1) u1.2
    let u3 := adc s3.1 (mulHi a b.l2) u2.2
    let u4 := adc s4.1 (mulHi a b.l3) u3.2
    let u5 := adc s5.1 (mulHi a b.l4) u4.2
    ⟨s0.1, u1.1, u2.1, u3.1, u4.1, u5.1, s5.2 + mulHi a b.l5 + u5.2⟩ := rfl

/-- `mulRow` adds `a · b` to the accumulator exactly. -/
theorem mulRow_val (t : Fp) (a : UInt64) (b : Fp) :
    (mulRow t a b).val = t.raw + a.toNat * b.raw := by
  have hb : a.toNat * b.raw = a.toNat * b.l0.toNat + 2^64 * (a.toNat * b.l1.toNat +
      2^64 * (a.toNat * b.l2.toNat + 2^64 * (a.toNat * b.l3.toNat + 2^64 * (a.toNat * b.l4.toNat +
      2^64 * (a.toNat * b.l5.toNat))))) := by unfold raw; ring
  have hab : a.toNat * b.raw ≤ (2 ^ 64 - 1) * (2 ^ 384 - 1) :=
    Nat.mul_le_mul (by have := a.toNat_lt; omega) (by
      have := b.l0.toNat_lt; have := b.l1.toNat_lt; have := b.l2.toNat_lt
      have := b.l3.toNat_lt; have := b.l4.toNat_lt; have := b.l5.toNat_lt
      unfold raw; omega)
  have htb : t.raw < 2 ^ 384 := by
    have := t.l0.toNat_lt; have := t.l1.toNat_lt; have := t.l2.toNat_lt
    have := t.l3.toNat_lt; have := t.l4.toNat_lt; have := t.l5.toNat_lt
    unfold raw; omega
  rw [hb] at hab
  rw [hb, mulRow_eq]
  simp only [Acc7.val, raw] at *
  have p0 := mul_toNat_add_mulHi a b.l0
  have p1 := mul_toNat_add_mulHi a b.l1
  have p2 := mul_toNat_add_mulHi a b.l2
  have p3 := mul_toNat_add_mulHi a b.l3
  have p4 := mul_toNat_add_mulHi a b.l4
  have p5 := mul_toNat_add_mulHi a b.l5
  have h0 := adc_spec t.l0 (a * b.l0) 0 (by decide)
  generalize adc t.l0 (a * b.l0) 0 = s0 at *
  have h1 := adc_spec t.l1 (a * b.l1) s0.2 h0.2
  generalize adc t.l1 (a * b.l1) s0.2 = s1 at *
  have h2 := adc_spec t.l2 (a * b.l2) s1.2 h1.2
  generalize adc t.l2 (a * b.l2) s1.2 = s2 at *
  have h3 := adc_spec t.l3 (a * b.l3) s2.2 h2.2
  generalize adc t.l3 (a * b.l3) s2.2 = s3 at *
  have h4 := adc_spec t.l4 (a * b.l4) s3.2 h3.2
  generalize adc t.l4 (a * b.l4) s3.2 = s4 at *
  have h5 := adc_spec t.l5 (a * b.l5) s4.2 h4.2
  generalize adc t.l5 (a * b.l5) s4.2 = s5 at *
  have g1 := adc_spec s1.1 (mulHi a b.l0) 0 (by decide)
  generalize adc s1.1 (mulHi a b.l0) 0 = u1 at *
  have g2 := adc_spec s2.1 (mulHi a b.l1) u1.2 g1.2
  generalize adc s2.1 (mulHi a b.l1) u1.2 = u2 at *
  have g3 := adc_spec s3.1 (mulHi a b.l2) u2.2 g2.2
  generalize adc s3.1 (mulHi a b.l2) u2.2 = u3 at *
  have g4 := adc_spec s4.1 (mulHi a b.l3) u3.2 g3.2
  generalize adc s4.1 (mulHi a b.l3) u3.2 = u4 at *
  have g5 := adc_spec s5.1 (mulHi a b.l4) u4.2 g4.2
  generalize adc s5.1 (mulHi a b.l4) u4.2 = u5 at *
  simp only [UInt64.reduceToNat] at h0 g1
  obtain ⟨e0, -⟩ := h0
  obtain ⟨e1, -⟩ := h1
  obtain ⟨e2, -⟩ := h2
  obtain ⟨e3, -⟩ := h3
  obtain ⟨e4, -⟩ := h4
  obtain ⟨e5, -⟩ := h5
  obtain ⟨f1, -⟩ := g1
  obtain ⟨f2, -⟩ := g2
  obtain ⟨f3, -⟩ := g3
  obtain ⟨f4, -⟩ := g4
  obtain ⟨f5, -⟩ := g5
  clear hb
  generalize a.toNat * b.l0.toNat = A0 at *
  generalize a.toNat * b.l1.toNat = A1 at *
  generalize a.toNat * b.l2.toNat = A2 at *
  generalize a.toNat * b.l3.toNat = A3 at *
  generalize a.toNat * b.l4.toNat = A4 at *
  generalize a.toNat * b.l5.toNat = A5 at *
  have hT : s5.2.toNat + (mulHi a b.l5).toNat + u5.2.toNat < 2 ^ 64 := by omega
  have hTe : (s5.2 + mulHi a b.l5 + u5.2).toNat =
      s5.2.toNat + (mulHi a b.l5).toNat + u5.2.toNat := by
    have h1 := s5.2.toNat_lt
    have h2 := (mulHi a b.l5).toNat_lt
    simp only [UInt64.toNat_add]
    omega
  rw [hTe]
  omega

theorem redRow_eq (t : Acc7) : redRow t =
    let m := t.w0 * N0
    let s0 := adc t.w0 (m * P0) 0
    let s1 := adc t.w1 (m * P1) s0.2
    let s2 := adc t.w2 (m * P2) s1.2
    let s3 := adc t.w3 (m * P3) s2.2
    let s4 := adc t.w4 (m * P4) s3.2
    let s5 := adc t.w5 (m * P5) s4.2
    let u1 := adc s1.1 (mulHi m P0) 0
    let u2 := adc s2.1 (mulHi m P1) u1.2
    let u3 := adc s3.1 (mulHi m P2) u2.2
    let u4 := adc s4.1 (mulHi m P3) u3.2
    let u5 := adc s5.1 (mulHi m P4) u4.2
    ⟨u1.1, u2.1, u3.1, u4.1, u5.1, t.w6 + s5.2 + mulHi m P5 + u5.2⟩ := rfl

theorem P0_toNat : P0.toNat = 0xb9feffffffffaaab := rfl
theorem P1_toNat : P1.toNat = 0x1eabfffeb153ffff := rfl
theorem P2_toNat : P2.toNat = 0x6730d2a0f6b0f624 := rfl
theorem P3_toNat : P3.toNat = 0x64774b84f38512bf := rfl
theorem P4_toNat : P4.toNat = 0x4b1ba7b6434bacd7 := rfl
theorem P5_toNat : P5.toNat = 0x1a0111ea397fe69a := rfl
theorem N0_toNat : N0.toNat = 0x89f3fffcfffcfffd := rfl

/-- `redRow` divides `t + m·p` by `2^64` exactly (`N0 · p ≡ -1 mod 2^64`
clears the low word), provided the quotient fits. -/
theorem redRow_spec (t : Acc7) (h : t.val + (t.w0 * N0).toNat * modulus < 2 ^ 448) :
    (redRow t).raw * 2 ^ 64 = t.val + (t.w0 * N0).toNat * modulus := by
  rw [redRow_eq]
  simp only [raw, Acc7.val] at *
  generalize hm : t.w0 * N0 = m at *
  have hmv : m.toNat = t.w0.toNat * 0x89f3fffcfffcfffd % 2 ^ 64 := by
    rw [← hm, UInt64.toNat_mul, N0_toNat]
  have p0 := mul_toNat_add_mulHi m P0
  have p1 := mul_toNat_add_mulHi m P1
  have p2 := mul_toNat_add_mulHi m P2
  have p3 := mul_toNat_add_mulHi m P3
  have p4 := mul_toNat_add_mulHi m P4
  have p5 := mul_toNat_add_mulHi m P5
  have h0 := adc_spec t.w0 (m * P0) 0 (by decide)
  generalize adc t.w0 (m * P0) 0 = s0 at *
  have h1 := adc_spec t.w1 (m * P1) s0.2 h0.2
  generalize adc t.w1 (m * P1) s0.2 = s1 at *
  have h2 := adc_spec t.w2 (m * P2) s1.2 h1.2
  generalize adc t.w2 (m * P2) s1.2 = s2 at *
  have h3 := adc_spec t.w3 (m * P3) s2.2 h2.2
  generalize adc t.w3 (m * P3) s2.2 = s3 at *
  have h4 := adc_spec t.w4 (m * P4) s3.2 h3.2
  generalize adc t.w4 (m * P4) s3.2 = s4 at *
  have h5 := adc_spec t.w5 (m * P5) s4.2 h4.2
  generalize adc t.w5 (m * P5) s4.2 = s5 at *
  have g1 := adc_spec s1.1 (mulHi m P0) 0 (by decide)
  generalize adc s1.1 (mulHi m P0) 0 = u1 at *
  have g2 := adc_spec s2.1 (mulHi m P1) u1.2 g1.2
  generalize adc s2.1 (mulHi m P1) u1.2 = u2 at *
  have g3 := adc_spec s3.1 (mulHi m P2) u2.2 g2.2
  generalize adc s3.1 (mulHi m P2) u2.2 = u3 at *
  have g4 := adc_spec s4.1 (mulHi m P3) u3.2 g3.2
  generalize adc s4.1 (mulHi m P3) u3.2 = u4 at *
  have g5 := adc_spec s5.1 (mulHi m P4) u4.2 g4.2
  generalize adc s5.1 (mulHi m P4) u4.2 = u5 at *
  simp only [UInt64.reduceToNat, P0_toNat, P1_toNat, P2_toNat, P3_toNat, P4_toNat,
    P5_toNat] at h0 h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 p0 p1 p2 p3 p4 p5
  obtain ⟨e0, -⟩ := h0
  obtain ⟨e1, -⟩ := h1
  obtain ⟨e2, -⟩ := h2
  obtain ⟨e3, -⟩ := h3
  obtain ⟨e4, -⟩ := h4
  obtain ⟨e5, -⟩ := h5
  obtain ⟨f1, -⟩ := g1
  obtain ⟨f2, -⟩ := g2
  obtain ⟨f3, -⟩ := g3
  obtain ⟨f4, -⟩ := g4
  obtain ⟨f5, -⟩ := g5
  unfold modulus at *
  have hlow : s0.1.toNat = 0 := by
    have := s0.1.toNat_lt
    have := t.w0.toNat_lt
    have := (m * P0).toNat_lt
    clear e1 e2 e3 e4 e5 f1 f2 f3 f4 f5 p1 p2 p3 p4 p5 h
    omega
  clear hmv
  have hT : t.w6.toNat + s5.2.toNat + (mulHi m P5).toNat + u5.2.toNat < 2 ^ 64 := by omega
  have hTe : (t.w6 + s5.2 + mulHi m P5 + u5.2).toNat =
      t.w6.toNat + s5.2.toNat + (mulHi m P5).toNat + u5.2.toNat := by
    have h1 := t.w6.toNat_lt
    have h2 := s5.2.toNat_lt
    have h3 := (mulHi m P5).toNat_lt
    simp only [UInt64.toNat_add]
    omega
  rw [hTe]
  omega

/-- One CIOS row: from an accumulator below `2p` and a canonical `b`, the
new accumulator is `(t + aᵢ·b + m·p) / 2^64` for some word `m`, again
below `2p`. -/
theorem row_spec (t b : Fp) (ai : UInt64) (ht : t.raw < 2 * modulus) (hb : b.raw < modulus) :
    ∃ m : Nat, (redRow (mulRow t ai b)).raw * 2 ^ 64 = t.raw + ai.toNat * b.raw + m * modulus ∧
      (redRow (mulRow t ai b)).raw < 2 * modulus := by
  have hV := mulRow_val t ai b
  generalize mulRow t ai b = V at *
  refine ⟨(V.w0 * N0).toNat, ?_⟩
  have hprod : ai.toNat * b.raw ≤ (2 ^ 64 - 1) * modulus :=
    Nat.mul_le_mul (by have := ai.toNat_lt; omega) (by omega)
  have hm := (V.w0 * N0).toNat_lt
  have hmp : (V.w0 * N0).toNat * modulus ≤ (2 ^ 64 - 1) * modulus :=
    Nat.mul_le_mul_right _ (by omega)
  have hr := redRow_spec V (by have := modulus_lt_381; omega)
  constructor
  · omega
  · have := modulus_lt; omega

theorem mulI_eq (a b : Fp) : mulI a b =
    reduceOnce (redRow (mulRow (redRow (mulRow (redRow (mulRow (redRow (mulRow (redRow
      (mulRow (redRow (mulRow zero a.l0 b)) a.l1 b)) a.l2 b)) a.l3 b)) a.l4 b)) a.l5 b)) := rfl

theorem zero_raw : zero.raw = 0 := rfl

/-- The CIOS invariant, end to end: `mulI a b · R ≡ a · b (mod p)` and the
result is canonical, for any `a` and canonical `b`. -/
theorem mulI_spec (a : Fp) {b : Fp} (hb : Canonical b) :
    Canonical (mulI a b) ∧ (mulI a b).raw * 2 ^ 384 % modulus = a.raw * b.raw % modulus := by
  unfold Canonical at hb
  rw [mulI_eq]
  have h0 : zero.raw < 2 * modulus := by rw [zero_raw]; decide
  obtain ⟨m0, e0, t0⟩ := row_spec zero b a.l0 h0 hb
  generalize redRow (mulRow zero a.l0 b) = T1 at *
  obtain ⟨m1, e1, t1⟩ := row_spec T1 b a.l1 t0 hb
  generalize redRow (mulRow T1 a.l1 b) = T2 at *
  obtain ⟨m2, e2, t2⟩ := row_spec T2 b a.l2 t1 hb
  generalize redRow (mulRow T2 a.l2 b) = T3 at *
  obtain ⟨m3, e3, t3⟩ := row_spec T3 b a.l3 t2 hb
  generalize redRow (mulRow T3 a.l3 b) = T4 at *
  obtain ⟨m4, e4, t4⟩ := row_spec T4 b a.l4 t3 hb
  generalize redRow (mulRow T4 a.l4 b) = T5 at *
  obtain ⟨m5, e5, t5⟩ := row_spec T5 b a.l5 t4 hb
  generalize redRow (mulRow T5 a.l5 b) = T6 at *
  refine ⟨reduceOnce_canonical T6 t5, ?_⟩
  rw [reduceOnce_raw T6 t5, Nat.mod_mul_mod]
  rw [zero_raw] at e0
  generalize b.raw = B at *
  have hA : a.raw * B = a.l0.toNat * B + 2^64 * (a.l1.toNat * B + 2^64 * (a.l2.toNat * B +
      2^64 * (a.l3.toNat * B + 2^64 * (a.l4.toNat * B + 2^64 * (a.l5.toNat * B))))) := by
    simp only [raw]; ring
  have hM : (m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5))))) * modulus =
      m0 * modulus + 2^64 * (m1 * modulus + 2^64 * (m2 * modulus + 2^64 * (m3 * modulus +
      2^64 * (m4 * modulus + 2^64 * (m5 * modulus))))) := by ring
  have hT : T6.raw * 2 ^ 384 = a.raw * B +
      (m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5))))) * modulus := by
    rw [hA, hM]; omega
  rw [hT, Nat.add_mul_mod_self_right]

/-- `mulI` keeps canonicity (only `b` needs to be canonical). -/
theorem mulI_canonical (a : Fp) {b : Fp} (hb : Canonical b) : Canonical (mulI a b) :=
  (mulI_spec a hb).1

/-- `mulI` is field multiplication on `val`. -/
theorem val_mulI (a : Fp) {b : Fp} (hb : Canonical b) : (mulI a b).val = a.val * b.val := by
  apply val_mul_of
  have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (mulI_spec a hb).2
  rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h

theorem mul_eq_mulI (a b : Fp) : mul a b = mulI a b := rfl

theorem mul_def (a b : Fp) : a * b = mul a b := rfl

theorem sqr_eq (a : Fp) : sqr a = mul a a := rfl

theorem mul_canonical (a : Fp) {b : Fp} (hb : Canonical b) : Canonical (mul a b) :=
  mulI_canonical a hb

theorem val_mul (a : Fp) {b : Fp} (hb : Canonical b) : (mul a b).val = a.val * b.val :=
  val_mulI a hb

theorem sqr_canonical {a : Fp} (ha : Canonical a) : Canonical (sqr a) :=
  mulI_canonical a ha

theorem val_sqr {a : Fp} (ha : Canonical a) : (sqr a).val = a.val * a.val :=
  val_mulI a ha

/-! ## Additive operations -/

theorem natCast_raw_mod (n : Nat) : ((n % modulus : Nat) : Z) = (n : Z) :=
  ZMod.natCast_mod n _

theorem natCast_modulus : ((modulus : Nat) : Z) = 0 := ZMod.natCast_self _

/-- `addI` of canonical vectors is `(a + b) mod p`. -/
theorem addI_raw {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    (addI a b).raw = (a.raw + b.raw) % modulus := by
  unfold Canonical at ha hb
  rw [addI_eq]
  obtain ⟨h1, -⟩ := adc6_spec a b
  have hs : (adc6 a b).1.raw = a.raw + b.raw := by
    have := modulus_lt_381; have := raw_lt (adc6 a b).1; omega
  rw [reduceOnce_raw _ (by rw [hs]; omega), hs]

theorem addI_canonical {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    Canonical (addI a b) := by
  unfold Canonical; rw [addI_raw ha hb]; exact Nat.mod_lt _ (by decide)

/-- `addI` is field addition on `val`. -/
theorem val_addI {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    (addI a b).val = a.val + b.val := by
  apply val_add_of
  rw [addI_raw ha hb, natCast_raw_mod, Nat.cast_add]

theorem add_eq_addI (a b : Fp) : add a b = addI a b := rfl

theorem add_def (a b : Fp) : a + b = add a b := rfl

theorem add_canonical {a b : Fp} (ha : Canonical a) (hb : Canonical b) : Canonical (add a b) :=
  addI_canonical ha hb

theorem val_add {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    (add a b).val = a.val + b.val :=
  val_addI ha hb

theorem doubleI_eq (a : Fp) : doubleI a = addI a a := rfl

theorem double_eq (a : Fp) : double a = add a a := rfl

theorem doubleI_canonical {a : Fp} (ha : Canonical a) : Canonical (doubleI a) :=
  addI_canonical ha ha

theorem val_doubleI {a : Fp} (ha : Canonical a) : (doubleI a).val = a.val + a.val :=
  val_addI ha ha

theorem double_canonical {a : Fp} (ha : Canonical a) : Canonical (double a) :=
  addI_canonical ha ha

theorem val_double {a : Fp} (ha : Canonical a) : (double a).val = a.val + a.val :=
  val_addI ha ha

theorem maskP_zero : maskP 0 = zero := by simp [maskP, zero]

theorem maskP_ones : maskP (0 - 1) = Pw := by simp [maskP, Pw]

theorem zero_canonical : Canonical zero := by unfold Canonical; rw [zero_raw]; decide

/-- `subI` of canonical vectors: the result plus `b` is `a`, up to one `p`. -/
theorem subI_spec {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    Canonical (subI a b) ∧ ∃ k : Nat, (subI a b).raw + b.raw = a.raw + k * modulus := by
  unfold Canonical at *
  rw [subI_eq]
  obtain ⟨s1, s2⟩ := sbb6_spec a b
  generalize sbb6 a b = r at *
  obtain ⟨d, br⟩ := r
  simp only at *
  have hd := raw_lt d
  have hp := modulus_lt_381
  rcases eq_zero_or_one s2 with rfl | rfl
  · rw [show (0 : UInt64) - 0 = 0 from rfl, maskP_zero]
    obtain ⟨c1, -⟩ := adc6_spec d zero
    have := raw_lt (adc6 d zero).1
    rw [zero_raw] at c1
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at s1
    exact ⟨by omega, 0, by omega⟩
  · rw [maskP_ones]
    obtain ⟨c1, -⟩ := adc6_spec d Pw
    have := raw_lt (adc6 d Pw).1
    rw [Pw_raw] at c1
    simp only [UInt64.toNat_one, Nat.mul_one] at s1
    exact ⟨by omega, 1, by omega⟩

theorem subI_canonical {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    Canonical (subI a b) :=
  (subI_spec ha hb).1

/-- `subI` is field subtraction on `val`. -/
theorem val_subI {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    (subI a b).val = a.val - b.val := by
  apply val_sub_of
  obtain ⟨k, hk⟩ := (subI_spec ha hb).2
  have h := congrArg (fun n : Nat => (n : Z)) hk
  simp only [Nat.cast_add, Nat.cast_mul, natCast_modulus, mul_zero, add_zero] at h
  rw [← h]; ring

theorem sub_eq_subI (a b : Fp) : sub a b = subI a b := rfl

theorem sub_def (a b : Fp) : a - b = sub a b := rfl

theorem sub_canonical {a b : Fp} (ha : Canonical a) (hb : Canonical b) : Canonical (sub a b) :=
  subI_canonical ha hb

theorem val_sub {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    (sub a b).val = a.val - b.val :=
  val_subI ha hb

/-- The OR of the six words vanishes exactly on the zero vector. -/
theorem or_words_eq_zero (a : Fp) :
    (a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) = 0 ↔ a.raw = 0 := by
  have := a.l0.toNat_lt; have := a.l1.toNat_lt; have := a.l2.toNat_lt
  have := a.l3.toNat_lt; have := a.l4.toNat_lt; have := a.l5.toNat_lt
  simp only [UInt64.or_eq_zero_iff, and_assoc]
  simp only [← UInt64.toNat_inj, UInt64.toNat_zero, raw]
  omega

/-- `negI` of a canonical vector: the result plus `a` is a multiple of `p`. -/
theorem negI_spec {a : Fp} (ha : Canonical a) :
    Canonical (negI a) ∧ ∃ k : Nat, (negI a).raw + a.raw = k * modulus := by
  unfold Canonical at *
  rw [negI_eq]
  obtain ⟨s1, s2⟩ := sbb6_spec Pw a
  rw [Pw_raw] at s1
  have hd := raw_lt (sbb6 Pw a).1
  have hp := modulus_lt_381
  have hm : (0 - ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) != 0).toUInt64) =
      if a.raw = 0 then 0 else 0 - 1 := by
    split
    · rename_i h0
      rw [(or_words_eq_zero a).mpr h0]; rfl
    · rename_i h0
      have : ((a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5) != 0) = true := by
        rw [bne_iff_ne]; exact fun h => h0 ((or_words_eq_zero a).mp h)
      rw [this]; rfl
  simp only [hm]
  by_cases h0 : a.raw = 0
  · simp only [h0, if_true, UInt64.and_zero]
    rw [show (⟨0, 0, 0, 0, 0, 0⟩ : Fp) = zero from rfl, zero_raw]
    exact ⟨by omega, 0, by omega⟩
  · simp only [h0, if_false]
    have hsel : ∀ x : UInt64, x &&& (0 - 1) = x := fun x => by simp
    simp only [hsel]
    rw [show (⟨(sbb6 Pw a).1.l0, (sbb6 Pw a).1.l1, (sbb6 Pw a).1.l2, (sbb6 Pw a).1.l3,
      (sbb6 Pw a).1.l4, (sbb6 Pw a).1.l5⟩ : Fp) = (sbb6 Pw a).1 from rfl]
    have := s2
    exact ⟨by omega, 1, by omega⟩

theorem negI_canonical {a : Fp} (ha : Canonical a) : Canonical (negI a) :=
  (negI_spec ha).1

/-- `negI` is field negation on `val`. -/
theorem val_negI {a : Fp} (ha : Canonical a) : (negI a).val = -a.val := by
  apply val_neg_of
  obtain ⟨k, hk⟩ := (negI_spec ha).2
  have h := congrArg (fun n : Nat => (n : Z)) hk
  simp only [Nat.cast_add, Nat.cast_mul, natCast_modulus, mul_zero] at h
  rw [eq_neg_iff_add_eq_zero, h]

theorem neg_eq_negI (a : Fp) : neg a = negI a := rfl

theorem neg_def (a : Fp) : -a = neg a := rfl

theorem neg_canonical {a : Fp} (ha : Canonical a) : Canonical (neg a) := negI_canonical ha

theorem val_neg {a : Fp} (ha : Canonical a) : (neg a).val = -a.val := val_negI ha

/-! ## Equality tests -/

/-- `isZero` decides `val = 0` on canonical vectors. -/
theorem isZero_iff {a : Fp} (ha : Canonical a) : a.isZero = true ↔ a.val = 0 := by
  rw [val_eq_zero_iff ha, ← or_words_eq_zero]
  simp only [isZero, beq_iff_eq]

/-- `beq` is word-wise equality. -/
theorem beq_true_iff_eq {a b : Fp} : a.beq b = true ↔ a = b := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := b
  simp [beq, and_assoc]

/-- `beq` decides equality of `val` on canonical vectors. -/
theorem beq_iff {a b : Fp} (ha : Canonical a) (hb : Canonical b) :
    a.beq b = true ↔ a.val = b.val := by
  rw [beq_true_iff_eq, val_inj ha hb]

theorem beq_def (a b : Fp) : (a == b) = a.beq b := rfl

/-! ## Constants -/

theorem val_zero : zero.val = 0 := (val_eq_zero_iff zero_canonical).mpr zero_raw

set_option exponentiation.threshold 512 in
theorem one_raw : one.raw = 2 ^ 384 % modulus := by
  rw [one, raw_ofRaw (by decide)]; decide

theorem one_canonical : Canonical one := by
  unfold Canonical; rw [one_raw]; exact Nat.mod_lt _ (by decide)

theorem val_one : one.val = 1 := by
  apply val_eq_of_raw
  rw [one_raw, natCast_raw_mod, toZMod_one, mul_one, Nat.cast_pow, Nat.cast_ofNat]

set_option exponentiation.threshold 1024 in
theorem R2_raw : R2.raw = 2 ^ 768 % modulus := by
  rw [R2, raw_ofRaw (by decide)]; decide

theorem R2_canonical : Canonical R2 := by
  unfold Canonical; rw [R2_raw]; exact Nat.mod_lt _ (by decide)

/-- `R2` stands for `R = 2^384`. -/
theorem val_R2 : R2.val = EthLib.Cryptography.Bls.Fp.ofNat (2 ^ 384) := by
  apply val_eq_of_raw
  rw [R2_raw, natCast_raw_mod, toZMod_ofNat, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show (768 : Nat) = 384 + 384 from rfl, pow_add]

theorem rawOne_raw : rawOne.raw = 1 := rfl

theorem rawOne_canonical : Canonical rawOne := by
  unfold Canonical; rw [rawOne_raw]; decide

/-- `rawOne` stands for `R⁻¹`. -/
theorem val_rawOne : rawOne.val = rInv := by
  apply toZMod.injective
  rw [toZ_val, rawOne_raw, Nat.cast_one, one_mul]

set_option exponentiation.threshold 512 in
theorem halfP_raw : halfP.raw = (modulus - 1) / 2 := by
  rw [halfP, raw_ofRaw (by decide)]; decide

theorem halfP_canonical : Canonical halfP := by
  unfold Canonical; rw [halfP_raw]; decide

set_option exponentiation.threshold 1024 in
theorem C256_raw : C256.raw = 2 ^ 1024 % modulus := by
  rw [C256, raw_ofRaw (by decide)]; decide

theorem C256_canonical : Canonical C256 := by
  unfold Canonical; rw [C256_raw]; exact Nat.mod_lt _ (by decide)

/-- `C256` stands for `2^256 · R = 2^640`. -/
theorem val_C256 : C256.val = EthLib.Cryptography.Bls.Fp.ofNat (2 ^ 640) := by
  apply val_eq_of_raw
  rw [C256_raw, natCast_raw_mod, toZMod_ofNat, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show (1024 : Nat) = 384 + 640 from rfl, pow_add]

/-! ## Conversions -/

theorem ofNat_canonical (n : Nat) : Canonical (ofNat n) :=
  mul_canonical _ R2_canonical

/-- `ofNat` computes the spec's `Fp.ofNat`. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = EthLib.Cryptography.Bls.Fp.ofNat n := by
  rw [ofNat, val_mul _ R2_canonical, val_R2]
  apply toZMod.injective
  rw [toZMod_mul, toZ_val, raw_ofRaw (lt_trans (Nat.mod_lt _ (by decide)) modulus_lt),
    natCast_raw_mod, toZMod_ofNat, toZMod_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  linear_combination (n : Z) * hr

theorem decode_eq (a : Fp) : decode a = mul a rawOne := rfl

theorem decode_canonical (a : Fp) : Canonical (decode a) :=
  mul_canonical a rawOne_canonical

/-- `decode a` holds, as plain words, the canonical representative of
`a.val` (no hypothesis on `a` needed). -/
theorem decode_raw (a : Fp) : (decode a).raw = a.val.val := by
  have h := (mulI_spec a rawOne_canonical).2
  rw [show mulI a rawOne = decode a from rfl, rawOne_raw, Nat.mul_one] at h
  have hz : (((decode a).raw * 2 ^ 384 : Nat) : Z) = ((a.raw : Nat) : Z) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hz
  have hc : ((decode a).raw : Z) = toZMod a.val := by
    rw [toZ_val, ← hz]
    have hr := toZ_rInv
    generalize toZMod rInv = ri at *
    generalize (2 : Z) ^ 384 = R at *
    linear_combination (-((decode a).raw : Z)) * hr
  have hv := congrArg ZMod.val hc
  have hlt : (decode a).raw < EthLib.Cryptography.Bls.Fp.modulus := decode_canonical a
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, val_toZMod] at hv
  exact hv

/-- `toNat` is the spec value's representative. -/
theorem toNat_eq (a : Fp) : a.toNat = a.val.val := decode_raw a

/-! ## Exponentiation -/

/-- A `for i in [:n]` loop in `Id` whose body always yields is a fold. -/
theorem forIn_range_eq_foldl {β : Type} (n : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (g : β → Nat → β) (h : ∀ i b, f i b = ForInStep.yield (g b i)) :
    forIn (m := Id) [:n] init f = (List.range' 0 n).foldl g init := by
  have hf : f = fun i b => ForInStep.yield (g b i) := funext fun i => funext fun b => h i b
  subst hf
  exact EthLib.Cryptography.IdLoops.forIn_range_yield n init (fun i b => g b i)

/-- `a^k` by `k` multiplications from `one`, the table's entries. -/
def powIter (a : Fp) : Nat → Fp
  | 0 => one
  | k + 1 => mul (powIter a k) a

theorem powIter_spec {a : Fp} (ha : Canonical a) (k : Nat) :
    Canonical (powIter a k) ∧
      toZMod (powIter a k).val =
        toZMod a.val ^ k := by
  induction k with
  | zero => exact ⟨one_canonical, by rw [powIter, val_one, toZMod_one, pow_zero]⟩
  | succ k ih =>
    refine ⟨mul_canonical _ ha, ?_⟩
    rw [powIter, val_mul _ ha, toZMod_mul, ih.2, pow_succ]

theorem powTable_eq (a : Fp) : powTable a =
    ((List.range' 0 16).foldl (fun (r : MProd Fp (Array Fp)) _ => ⟨mul r.1 a, r.2.push r.1⟩)
      ⟨one, Array.mkEmpty 16⟩).2 := by
  unfold powTable
  dsimp only
  rw [forIn_range_eq_foldl (g := fun (r : MProd Fp (Array Fp)) _ => ⟨mul r.1 a, r.2.push r.1⟩)]
  · rfl
  · intro i r; rfl

theorem powTable_fold (a : Fp) (k : Nat) :
    (List.range' 0 k).foldl (fun (r : MProd Fp (Array Fp)) _ => ⟨mul r.1 a, r.2.push r.1⟩)
      ⟨one, Array.mkEmpty 16⟩ = ⟨powIter a k, ((List.range k).map (powIter a)).toArray⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range'_1_concat, List.foldl_append, ih]
    simp [List.range_succ, powIter]

theorem powTable_getElem! (a : Fp) {d : Nat} (hd : d < 16) : (powTable a)[d]! = powIter a d := by
  rw [powTable_eq, powTable_fold]
  simp [hd]

/-- One window step of `powNibbles`: four squarings, then a table
multiplication for a nonzero digit. -/
def nibStep (tbl : Array Fp) (acc : Fp) (d : UInt8) : Fp :=
  if (d != 0) = true then mul tbl[d.toNat]! (sqr (sqr (sqr (sqr acc))))
  else sqr (sqr (sqr (sqr acc)))

theorem powNibbles_eq (a : Fp) (ds : ByteArray) :
    powNibbles a ds = ds.data.toList.foldl (nibStep (powTable a)) one := by
  have h : powNibbles a ds =
      (List.range' 0 ds.size).foldl (fun acc i => nibStep (powTable a) acc (ds.get! i)) one := by
    unfold powNibbles
    dsimp only
    rw [forIn_range_eq_foldl (g := fun acc i => nibStep (powTable a) acc (ds.get! i))]
    · rfl
    · intro i acc
      simp only [nibStep]
      split <;> rfl
  rw [h]
  exact EthLib.Cryptography.IdLoops.foldl_range'_getElem! ds.data (nibStep (powTable a)) one

/-- Base-16 Horner evaluation of a digit list. -/
def horner (v : Nat) (l : List UInt8) : Nat := l.foldl (fun v d => 16 * v + d.toNat) v

theorem horner_init (l : List UInt8) (v : Nat) :
    horner v l = v * 16 ^ l.length + horner 0 l := by
  induction l generalizing v with
  | nil => simp [horner]
  | cons d l ih =>
    simp only [horner, List.foldl_cons] at ih ⊢
    rw [ih, ih (16 * 0 + d.toNat), List.length_cons, pow_succ]
    ring

theorem nibStep_spec {a : Fp} (ha : Canonical a) {acc : Fp} (hacc : Canonical acc) {d : UInt8}
    (hd : d.toNat < 16) :
    Canonical (nibStep (powTable a) acc d) ∧
      toZMod (nibStep (powTable a) acc d).val =
        toZMod acc.val ^ 16 *
          toZMod a.val ^ d.toNat := by
  have c1 := sqr_canonical hacc
  have c2 := sqr_canonical c1
  have c3 := sqr_canonical c2
  have c4 := sqr_canonical c3
  have hs : toZMod (sqr (sqr (sqr (sqr acc)))).val =
      toZMod acc.val ^ 16 := by
    rw [val_sqr c3, toZMod_mul, val_sqr c2, toZMod_mul, val_sqr c1, toZMod_mul, val_sqr hacc, toZMod_mul]
    ring
  unfold nibStep
  split
  · rw [powTable_getElem! a hd]
    have hp := powIter_spec ha d.toNat
    refine ⟨mul_canonical _ c4, ?_⟩
    rw [val_mul _ c4, toZMod_mul, hs, hp.2]
    ring
  · rename_i h
    have : d = 0 := by simpa using h
    subst this
    refine ⟨c4, ?_⟩
    rw [hs]; simp

theorem foldl_nibStep {a : Fp} (ha : Canonical a) (l : List UInt8) (hl : ∀ d ∈ l, d.toNat < 16)
    (acc : Fp) (hacc : Canonical acc) (v : Nat)
    (hv : toZMod acc.val = toZMod a.val ^ v) :
    Canonical (l.foldl (nibStep (powTable a)) acc) ∧
      toZMod (l.foldl (nibStep (powTable a)) acc).val =
        toZMod a.val ^ horner v l := by
  induction l generalizing acc v with
  | nil => exact ⟨hacc, hv⟩
  | cons d l ih =>
    have hd := hl d List.mem_cons_self
    obtain ⟨c, e⟩ := nibStep_spec ha hacc hd
    have := ih (fun x hx => hl x (List.mem_cons_of_mem d hx)) _ c (16 * v + d.toNat)
      (by rw [e, hv, ← pow_mul, ← pow_add, Nat.mul_comm v 16])
    simpa [horner] using this

/-- `powNibbles` on a digit array with every digit below 16 is the power by
its Horner value. -/
theorem powNibbles_spec {a : Fp} (ha : Canonical a) (ds : ByteArray)
    (hds : ∀ d ∈ ds.data.toList, d.toNat < 16) :
    Canonical (powNibbles a ds) ∧
      toZMod (powNibbles a ds).val =
        toZMod a.val ^ horner 0 ds.data.toList := by
  rw [powNibbles_eq]
  exact foldl_nibStep ha _ hds one one_canonical 0 (by rw [val_one, toZMod_one, pow_zero])

theorem nibbles_toList (e : Nat) : (nibbles e).data.toList =
    (List.range (e.log2 / 4 + 1)).reverse.map (fun i => ((e >>> (4 * i)) % 16).toUInt8) := by
  simp [nibbles]

theorem digit_toNat (e i : Nat) : ((e >>> (4 * i)) % 16).toUInt8.toNat = e / 16 ^ i % 16 := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, pow_mul]
  have : e / (2 ^ 4) ^ i % 16 < 2 ^ 8 := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt this]
  rfl

theorem nibbles_lt (e : Nat) : ∀ d ∈ (nibbles e).data.toList, d.toNat < 16 := by
  rw [nibbles_toList]
  intro d hd
  simp only [List.mem_map, List.mem_reverse, List.mem_range] at hd
  obtain ⟨i, -, rfl⟩ := hd
  rw [digit_toNat]
  exact Nat.mod_lt _ (by decide)

theorem horner_digits (e k : Nat) :
    horner 0 ((List.range k).reverse.map (fun i => ((e >>> (4 * i)) % 16).toUInt8)) =
      e % 16 ^ k := by
  induction k with
  | zero => simp [horner, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.map_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [show horner 0 (((e >>> (4 * k)) % 16).toUInt8 :: _) =
        horner (16 * 0 + ((e >>> (4 * k)) % 16).toUInt8.toNat) _ from rfl,
      horner_init, ih, List.length_map, List.length_reverse, List.length_range, digit_toNat,
      Nat.mod_pow_succ]
    ring

/-- The digits of `nibbles e` evaluate back to `e`. -/
theorem horner_nibbles (e : Nat) : horner 0 (nibbles e).data.toList = e := by
  rw [nibbles_toList, horner_digits]
  apply Nat.mod_eq_of_lt
  calc e < 2 ^ (e.log2 + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ (4 * (e.log2 / 4 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 ^ (e.log2 / 4 + 1) := by rw [pow_mul]; rfl

/-- Fixed-window exponentiation computes the field power. -/
theorem powNibbles_nibbles {a : Fp} (ha : Canonical a) (e : Nat) :
    Canonical (powNibbles a (nibbles e)) ∧ (powNibbles a (nibbles e)).val = a.val ^ e := by
  obtain ⟨c, h⟩ := powNibbles_spec ha (nibbles e) (nibbles_lt e)
  rw [horner_nibbles, ← toZMod_pow] at h
  exact ⟨c, toZMod.injective h⟩

theorem powNibbles_canonical {a : Fp} (ha : Canonical a) (e : Nat) :
    Canonical (powNibbles a (nibbles e)) :=
  (powNibbles_nibbles ha e).1

theorem val_powNibbles {a : Fp} (ha : Canonical a) (e : Nat) :
    (powNibbles a (nibbles e)).val = a.val ^ e :=
  (powNibbles_nibbles ha e).2

/-- `val_powNibbles` in the spec's `powNat` form. -/
theorem val_powNibbles_powNat {a : Fp} (ha : Canonical a) (e : Nat) :
    (powNibbles a (nibbles e)).val = EthLib.Cryptography.Bls.Fp.powNat a.val e := by
  rw [val_powNibbles ha, powNat_eq_monoid_pow]

/-! ### Sliding-window exponentiation

`powWin a prog` is `a ^ winExp prog` whenever the program's digits are odd (or
zero for a final run of squarings) and below 32. `sqrtWin` and `invSqrtWin`
satisfy that and evaluate to their exponents by kernel computation. -/

/-- The exponent a window program stands for. -/
def winExp (prog : WinProg) : Nat :=
  prog.2.toList.foldl (fun v s => v * 2 ^ s.1 + s.2) prog.1

/-- The digits a window program may use: an odd start, odd steps below 32 or
zero. -/
def WinProg.Valid (prog : WinProg) : Prop :=
  prog.1 % 2 = 1 ∧ prog.1 < 32 ∧ ∀ s ∈ prog.2.toList, s.2 = 0 ∨ (s.2 % 2 = 1 ∧ s.2 < 32)

/-- `a ^ (2 * k + 1)` by `k` products with `a²`, the odd table's entries. -/
def oddIter (a : Fp) : Nat → Fp
  | 0 => a
  | k + 1 => mul (oddIter a k) (sqr a)

theorem oddIter_spec {a : Fp} (ha : Canonical a) (k : Nat) :
    Canonical (oddIter a k) ∧
      toZMod (oddIter a k).val = toZMod a.val ^ (2 * k + 1) := by
  induction k with
  | zero => exact ⟨ha, by simp [oddIter]⟩
  | succ k ih =>
    have hs := sqr_canonical ha
    refine ⟨mul_canonical _ hs, ?_⟩
    rw [oddIter, val_mul _ hs, toZMod_mul, ih.2, val_sqr ha, toZMod_mul, ← pow_two,
      ← pow_add]
    congr 1

theorem oddPush_eq (a : Fp) (k m : Nat) :
    oddPush (sqr a) k (oddIter a m) ((List.range (m + 1)).map (oddIter a)).toArray =
      ((List.range (m + 1 + k)).map (oddIter a)).toArray := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    have e : ((List.range (m + 1)).map (oddIter a)).toArray.push (oddIter a (m + 1)) =
        ((List.range (m + 1 + 1)).map (oddIter a)).toArray := by
      rw [List.range_succ (n := m + 1)]; simp
    rw [oddPush]
    have h := ih (m + 1)
    rw [show m + 1 + (k + 1) = m + 1 + 1 + k by omega, ← h, ← e]
    rfl

theorem oddTable_getElem! (a : Fp) {j : Nat} (hj : j < 16) : (oddTable a)[j]! = oddIter a j := by
  have h : oddTable a = ((List.range 16).map (oddIter a)).toArray := by
    have := oddPush_eq a 15 0
    simpa [oddTable] using this
  rw [h]
  simp [hj]

theorem repeat_spec {x : Fp} (hx : Canonical x) (n : Nat) :
    Canonical (Nat.repeat (fun x => mulI x x) n x) ∧
      toZMod (Nat.repeat (fun x => mulI x x) n x).val = toZMod x.val ^ 2 ^ n := by
  induction n with
  | zero =>
    refine ⟨hx, ?_⟩
    show toZMod x.val = _
    rw [Nat.pow_zero, pow_one]
  | succ n ih =>
    obtain ⟨c0, e0⟩ := ih
    show Canonical (mulI _ _) ∧ toZMod (mulI _ _).val = _
    refine ⟨mulI_canonical _ c0, ?_⟩
    rw [val_mulI _ c0, toZMod_mul, e0, ← pow_add, pow_succ 2 n, Nat.mul_two]

theorem repeat_add {α : Type} (f : α → α) (m k : Nat) (a : α) :
    Nat.repeat f (m + k) a = Nat.repeat f m (Nat.repeat f k a) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add]; exact congrArg f ih

/-- The unrolled squaring run is `n` applications of the squaring. -/
theorem sqrN_eq (acc : Fp) (n : Nat) : sqrN acc n = Nat.repeat (fun x => mulI x x) n acc := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | n + 6 =>
    rw [show n + 6 = (n + 1) + 5 by omega, repeat_add]
    rfl

theorem sqrN_spec {x : Fp} (hx : Canonical x) (n : Nat) :
    Canonical (sqrN x n) ∧ toZMod (sqrN x n).val = toZMod x.val ^ 2 ^ n := by
  rw [sqrN_eq]
  exact repeat_spec hx n

theorem winStep_spec {a : Fp} (ha : Canonical a) {acc : Fp} (hacc : Canonical acc)
    {s : Nat × Nat} (hs : s.2 = 0 ∨ (s.2 % 2 = 1 ∧ s.2 < 32)) :
    Canonical (winStep (oddTable a) acc s) ∧
      toZMod (winStep (oddTable a) acc s).val =
        toZMod acc.val ^ 2 ^ s.1 * toZMod a.val ^ s.2 := by
  obtain ⟨c, e⟩ := sqrN_spec hacc s.1
  unfold winStep
  dsimp only
  split
  · rename_i h
    have hd : s.2 % 2 = 1 ∧ s.2 < 32 := by
      rcases hs with hs | hs
      · simp [hs] at h
      · exact hs
    have hj : s.2 >>> 1 < 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
    rw [oddTable_getElem! a hj]
    obtain ⟨c2, e2⟩ := oddIter_spec ha (s.2 >>> 1)
    refine ⟨mul_canonical _ c, ?_⟩
    have hexp : 2 * (s.2 >>> 1) + 1 = s.2 := by rw [Nat.shiftRight_eq_div_pow]; omega
    rw [val_mul _ c, toZMod_mul, e, e2, hexp, mul_comm]
  · rename_i h
    have : s.2 = 0 := by simpa using h
    refine ⟨c, ?_⟩
    rw [e, this]; simp

theorem foldl_winStep {a : Fp} (ha : Canonical a) (l : List (Nat × Nat))
    (hl : ∀ s ∈ l, s.2 = 0 ∨ (s.2 % 2 = 1 ∧ s.2 < 32))
    (acc : Fp) (hacc : Canonical acc) (v : Nat)
    (hv : toZMod acc.val = toZMod a.val ^ v) :
    Canonical (l.foldl (winStep (oddTable a)) acc) ∧
      toZMod (l.foldl (winStep (oddTable a)) acc).val =
        toZMod a.val ^ l.foldl (fun v s => v * 2 ^ s.1 + s.2) v := by
  induction l generalizing acc v with
  | nil => exact ⟨hacc, hv⟩
  | cons s l ih =>
    obtain ⟨c, e⟩ := winStep_spec ha hacc (hl s List.mem_cons_self)
    have := ih (fun x hx => hl x (List.mem_cons_of_mem s hx)) _ c (v * 2 ^ s.1 + s.2)
      (by rw [e, hv, ← pow_mul, ← pow_add])
    simpa using this

/-- A valid window program computes the field power by its exponent. -/
theorem powWin_spec {a : Fp} (ha : Canonical a) {prog : WinProg} (hp : prog.Valid) :
    Canonical (powWin a prog) ∧ (powWin a prog).val = a.val ^ winExp prog := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hj : prog.1 >>> 1 < 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hz : (powWin a prog) = prog.2.toList.foldl (winStep (oddTable a)) (oddIter a (prog.1 >>> 1)) := by
    unfold powWin
    dsimp only
    rw [oddTable_getElem! a hj, ← Array.foldl_toList]
  obtain ⟨c0, e0⟩ := oddIter_spec ha (prog.1 >>> 1)
  have hv : toZMod (oddIter a (prog.1 >>> 1)).val = toZMod a.val ^ prog.1 := by
    have hexp : 2 * (prog.1 >>> 1) + 1 = prog.1 := by rw [Nat.shiftRight_eq_div_pow]; omega
    rw [e0, hexp]
  obtain ⟨c, e⟩ := foldl_winStep ha prog.2.toList h3 _ c0 prog.1 hv
  rw [hz]
  refine ⟨c, ?_⟩
  rw [← toZMod_pow] at e
  exact toZMod.injective e

theorem powWin_canonical {a : Fp} (ha : Canonical a) {prog : WinProg} (hp : prog.Valid) :
    Canonical (powWin a prog) :=
  (powWin_spec ha hp).1

/-- The window power in the spec's `powNat` form, for a program of `e`. -/
theorem val_powWin_powNat {a : Fp} (ha : Canonical a) {prog : WinProg} (hp : prog.Valid)
    {e : Nat} (he : winExp prog = e) :
    (powWin a prog).val = EthLib.Cryptography.Bls.Fp.powNat a.val e := by
  rw [(powWin_spec ha hp).2, he, powNat_eq_monoid_pow]

theorem sqrtWin_valid : sqrtWin.Valid := by
  unfold sqrtWin WinProg.Valid; decide +kernel

theorem invSqrtWin_valid : invSqrtWin.Valid := by
  unfold invSqrtWin WinProg.Valid; decide +kernel

theorem winExp_sqrtWin : winExp sqrtWin = (modulus + 1) / 4 := by
  unfold sqrtWin winExp; decide +kernel

theorem winExp_invSqrtWin : winExp invSqrtWin = (modulus - 3) / 4 := by
  unfold invSqrtWin winExp; decide +kernel

theorem powWin_sqrtWin_canonical {a : Fp} (ha : Canonical a) : Canonical (powWin a sqrtWin) :=
  powWin_canonical ha sqrtWin_valid

theorem val_powWin_sqrtWin {a : Fp} (ha : Canonical a) :
    (powWin a sqrtWin).val =
      EthLib.Cryptography.Bls.Fp.powNat a.val ((EthLib.Cryptography.Bls.Fp.modulus + 1) / 4) :=
  val_powWin_powNat ha sqrtWin_valid winExp_sqrtWin

theorem powWin_invSqrtWin_canonical {a : Fp} (ha : Canonical a) :
    Canonical (powWin a invSqrtWin) :=
  powWin_canonical ha invSqrtWin_valid

theorem val_powWin_invSqrtWin {a : Fp} (ha : Canonical a) :
    (powWin a invSqrtWin).val =
      EthLib.Cryptography.Bls.Fp.powNat a.val ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) :=
  val_powWin_powNat ha invSqrtWin_valid winExp_invSqrtWin

theorem powNat_eq (a : Fp) (e : Nat) : powNat a e = powNibbles a (nibbles e) := rfl

theorem powNat_canonical {a : Fp} (ha : Canonical a) (e : Nat) : Canonical (powNat a e) :=
  powNibbles_canonical ha e

theorem val_powNat {a : Fp} (ha : Canonical a) (e : Nat) : (powNat a e).val = a.val ^ e :=
  val_powNibbles ha e

theorem val_powNat_powNat {a : Fp} (ha : Canonical a) (e : Nat) :
    (powNat a e).val = EthLib.Cryptography.Bls.Fp.powNat a.val e :=
  val_powNibbles_powNat ha e

theorem div_def (a b : Fp) : a / b = a * b.inverse := rfl

/-! ## Square root -/

theorem sqrt_eq (a : Fp) : sqrt a =
    if (mul (powWin a sqrtWin) (powWin a sqrtWin)).beq a then
      .ok (powWin a sqrtWin)
    else .error .notASquare := rfl

/-- `sqrt` computes the spec's `Fp.sqrt` (through `val`). -/
theorem sqrt_map_val {a : Fp} (ha : Canonical a) :
    (sqrt a).map val = EthLib.Cryptography.Bls.Fp.sqrt a.val := by
  rw [sqrt_eq, EthLib.Cryptography.Bls.Fp.sqrt]
  have hc := powWin_sqrtWin_canonical ha
  have hv' := val_powWin_sqrtWin ha
  generalize powWin a sqrtWin = c at *
  have hiff : (mul c c).beq a = true ↔
      EthLib.Cryptography.Bls.Fp.beq
        (EthLib.Cryptography.Bls.Fp.powNat a.val ((EthLib.Cryptography.Bls.Fp.modulus + 1) / 4) *
          EthLib.Cryptography.Bls.Fp.powNat a.val ((EthLib.Cryptography.Bls.Fp.modulus + 1) / 4))
        a.val = true := by
    rw [beq_iff (mul_canonical _ hc) ha, val_mul _ hc, beq_eq_true_iff, hv']
  by_cases hb : (mul c c).beq a = true
  · rw [if_pos hb, if_pos (hiff.mp hb)]
    show Except.ok c.val = _
    rw [hv']
  · rw [if_neg hb, if_neg (fun h => hb (hiff.mpr h))]
    rfl

/-- Every root `sqrt` returns is canonical. -/
theorem sqrt_ok_canonical {a c : Fp} (ha : Canonical a) (h : sqrt a = .ok c) : Canonical c := by
  rw [sqrt_eq] at h
  have hc := powWin_sqrtWin_canonical ha
  generalize powWin a sqrtWin = d at hc h
  split at h
  · cases h; exact hc
  · cases h

/-! ## Sign and parity -/

theorem signBit_eq (y : Fp) : signBit y = ((sbb6 halfP (decode y)).2 != 0) := rfl

/-- `signBit` computes the spec's `Fp.signBit`. -/
theorem signBit_eq_spec (y : Fp) : signBit y = EthLib.Cryptography.Bls.Fp.signBit y.val := by
  rw [signBit_eq, EthLib.Cryptography.Bls.Fp.signBit]
  obtain ⟨h1, h2⟩ := sbb6_spec halfP (decode y)
  rw [decode_raw, halfP_raw] at h1
  have hd := raw_lt (sbb6 halfP (decode y)).1
  have hy := y.val.isLt
  have hp : EthLib.Cryptography.Bls.Fp.modulus % 2 = 1 := by decide
  have hm := modulus_eq
  rcases eq_zero_or_one h2 with h | h <;> rw [h] at h1 ⊢
  · simp only [bne_self_eq_false, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at h1 ⊢
    symm; rw [decide_eq_false_iff_not]; omega
  · simp only [UInt64.toNat_one, Nat.mul_one] at h1
    rw [show ((1 : UInt64) != 0) = true from rfl]
    symm; rw [decide_eq_true_iff]; omega

/-- `parity` is the parity of the spec value's representative. -/
theorem parity_eq (y : Fp) : parity y = (y.val.val % 2 == 1) := by
  rw [parity, ← decode_raw]
  have hw : ((decode y).l0 &&& 1).toNat = (decode y).raw % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]
    simp only [raw]
    omega
  have hb : ((decode y).l0 &&& 1 = 1) ↔ (decode y).raw % 2 = 1 := by
    rw [← UInt64.toNat_inj, hw]; rfl
  rw [Bool.eq_iff_iff, _root_.beq_iff_eq, _root_.beq_iff_eq, hb]


/-! ## Byte encoding -/

theorem getElem!_eq_get! (b : ByteArray) (i : Nat) : b[i]! = b.get! i := by
  show b[i]! = b.data[i]!
  by_cases h : i < b.size
  · rw [getElem!_pos b i h, getElem!_pos b.data i h]
    rfl
  · rw [getElem!_neg b i h, getElem!_neg b.data i h]

/-- The big-endian integer of the `n` bytes at `b[off..off+n]`. -/
def bytesVal (b : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bytesVal b off n * 256 + (b.get! (off + n)).toNat

theorem bytesVal_add (b : ByteArray) (off m n : Nat) :
    bytesVal b off (m + n) = bytesVal b off m * 256 ^ n + bytesVal b (off + m) n := by
  induction n with
  | zero => simp [bytesVal]
  | succ n ih =>
    rw [← Nat.add_assoc, bytesVal, ih, bytesVal, Nat.add_assoc off m n, pow_succ]
    ring

theorem bytesVal_lt (b : ByteArray) (off n : Nat) : bytesVal b off n < 256 ^ n := by
  induction n with
  | zero => simp [bytesVal]
  | succ n ih =>
    have := (b.get! (off + n)).toNat_lt
    rw [bytesVal, pow_succ]
    omega

theorem lor_byte (x b m : Nat) (hx : x % 2 ^ (m + 8) = 0) (hb : b < 256) :
    x ||| b * 2 ^ m = x + b * 2 ^ m := by
  obtain ⟨q, rfl⟩ : 2 ^ (m + 8) ∣ x := Nat.dvd_of_mod_eq_zero hx
  have h1 : 2 ^ (m + 8) * q = (q <<< 8) <<< m := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_add]; ring
  have h2 : b * 2 ^ m = b <<< m := (Nat.shiftLeft_eq b m).symm
  rw [h1, h2, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b < 2 ^ 8)]
  simp only [Nat.shiftLeft_eq]; ring

theorem lor_byte0 (x b : Nat) (hx : x % 256 = 0) (hb : b < 256) : x ||| b = x + b := by
  have := lor_byte x b 0 (by simpa using hx) hb
  simpa using this

/-- `be64` reads eight big-endian bytes. -/
theorem be64_toNat (b : ByteArray) (off : Nat) : (be64 b off).toNat = bytesVal b off 8 := by
  have := (b.get! off).toNat_lt
  have := (b.get! (off+1)).toNat_lt
  have := (b.get! (off+2)).toNat_lt
  have := (b.get! (off+3)).toNat_lt
  have := (b.get! (off+4)).toNat_lt
  have := (b.get! (off+5)).toNat_lt
  have := (b.get! (off+6)).toNat_lt
  have := (b.get! (off+7)).toNat_lt
  unfold be64
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftLeft_eq]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  simp (disch := omega) only [lor_byte, lor_byte0]
  simp only [bytesVal, Nat.add_zero]
  omega

/-- The spec's decoding loop is `bytesVal` over the whole array. -/
theorem bytesBEToNat_eq (b : ByteArray) :
    EthLib.Cryptography.Bls.Fp.bytesBEToNat b = bytesVal b 0 b.size := by
  have h : EthLib.Cryptography.Bls.Fp.bytesBEToNat b =
      (List.range' 0 b.size).foldl (fun acc i => (acc <<< 8) ||| b[i]!.toNat) 0 := by
    unfold EthLib.Cryptography.Bls.Fp.bytesBEToNat
    dsimp only
    rw [forIn_range_eq_foldl (g := fun acc i => (acc <<< 8) ||| b[i]!.toNat)]
    · rfl
    · intro i r; rfl
  rw [h]
  suffices ∀ n, (List.range' 0 n).foldl (fun acc i => (acc <<< 8) ||| b[i]!.toNat) 0 =
      bytesVal b 0 n from this _
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_1_concat, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      ← Nat.shiftLeft_add_eq_or_of_lt (by have := b[0 + n]!.toNat_lt; exact this),
      Nat.shiftLeft_eq, bytesVal, getElem!_eq_get!]

/-- The six words `fromBytesBE` reads, least significant first. -/
def wordsBE (b : ByteArray) : Fp :=
  ⟨be64 b 40, be64 b 32, be64 b 24, be64 b 16, be64 b 8, be64 b 0⟩

theorem wordsBE_raw (b : ByteArray) : (wordsBE b).raw = bytesVal b 0 48 := by
  have h1 := bytesVal_add b 0 40 8
  have h2 := bytesVal_add b 0 32 8
  have h3 := bytesVal_add b 0 24 8
  have h4 := bytesVal_add b 0 16 8
  have h5 := bytesVal_add b 0 8 8
  simp only [wordsBE, raw, be64_toNat]
  simp only [Nat.zero_add, Nat.reduceAdd] at h1 h2 h3 h4 h5
  omega

theorem fromBytesBE_eq (b : ByteArray) : fromBytesBE b =
    if b.size ≠ 48 then .error .nonCanonicalFieldElement
    else if (subP (wordsBE b)).2 == 0 then .error .nonCanonicalFieldElement
    else .ok (mul (wordsBE b) R2) := rfl

/-- Multiplying a canonical vector by `R2` encodes its raw integer. -/
theorem val_mul_R2 (t : Fp) :
    toZMod (mul t R2).val = (t.raw : Z) := by
  rw [val_mul _ R2_canonical, toZMod_mul, toZ_val, val_R2, toZMod_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  linear_combination (t.raw : Z) * hr

/-- `fromBytesBE` computes the spec's `Fp.fromBytesBE` (through `val`). -/
theorem fromBytesBE_map_val (b : ByteArray) :
    (fromBytesBE b).map val = EthLib.Cryptography.Bls.Fp.fromBytesBE b := by
  rw [fromBytesBE_eq, EthLib.Cryptography.Bls.Fp.fromBytesBE]
  by_cases hs : b.size ≠ 48
  · rw [if_pos hs, if_pos hs]; rfl
  · rw [if_neg hs, if_neg hs]
    have hn : EthLib.Cryptography.Bls.Fp.bytesBEToNat b = (wordsBE b).raw := by
      rw [bytesBEToNat_eq, wordsBE_raw, show b.size = 48 by omega]
    obtain ⟨-, h1, h0⟩ := subP_spec (wordsBE b)
    have hm := modulus_eq
    by_cases hlt : (wordsBE b).raw < modulus
    · rw [h1.mpr hlt, show ((1 : UInt64) == 0) = false from rfl, if_neg Bool.false_ne_true]
      dsimp only
      rw [dif_pos (by rw [hn]; omega)]
      show Except.ok (mul (wordsBE b) R2).val = _
      congr 1
      apply toZMod.injective
      rw [val_mul_R2, toZMod_mk, hn]
    · rw [h0.mpr (by omega), show ((0 : UInt64) == 0) = true from rfl, if_pos rfl]
      dsimp only
      rw [dif_neg (by rw [hn]; omega)]
      rfl

/-- Every value `fromBytesBE` returns is canonical. -/
theorem fromBytesBE_ok_canonical {b : ByteArray} {c : Fp} (h : fromBytesBE b = .ok c) :
    Canonical c := by
  rw [fromBytesBE_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact mul_canonical _ R2_canonical

/-- The bytes `toBytesBE` emits from a decoded vector. -/
def wordsBytes (v : Fp) : ByteArray :=
  (ByteArray.emptyWithCapacity 48)
    |> (pushBE64 · v.l5) |> (pushBE64 · v.l4) |> (pushBE64 · v.l3)
    |> (pushBE64 · v.l2) |> (pushBE64 · v.l1) |> (pushBE64 · v.l0)

theorem toBytesBE_eq_words (a : Fp) : toBytesBE a = wordsBytes (decode a) := rfl

theorem wordsBytes_toList (v : Fp) : (wordsBytes v).data.toList =
    [(v.l5 >>> 56).toUInt8,
      (v.l5 >>> 48).toUInt8,
      (v.l5 >>> 40).toUInt8,
      (v.l5 >>> 32).toUInt8,
      (v.l5 >>> 24).toUInt8,
      (v.l5 >>> 16).toUInt8,
      (v.l5 >>> 8).toUInt8,
      v.l5.toUInt8,
      (v.l4 >>> 56).toUInt8,
      (v.l4 >>> 48).toUInt8,
      (v.l4 >>> 40).toUInt8,
      (v.l4 >>> 32).toUInt8,
      (v.l4 >>> 24).toUInt8,
      (v.l4 >>> 16).toUInt8,
      (v.l4 >>> 8).toUInt8,
      v.l4.toUInt8,
      (v.l3 >>> 56).toUInt8,
      (v.l3 >>> 48).toUInt8,
      (v.l3 >>> 40).toUInt8,
      (v.l3 >>> 32).toUInt8,
      (v.l3 >>> 24).toUInt8,
      (v.l3 >>> 16).toUInt8,
      (v.l3 >>> 8).toUInt8,
      v.l3.toUInt8,
      (v.l2 >>> 56).toUInt8,
      (v.l2 >>> 48).toUInt8,
      (v.l2 >>> 40).toUInt8,
      (v.l2 >>> 32).toUInt8,
      (v.l2 >>> 24).toUInt8,
      (v.l2 >>> 16).toUInt8,
      (v.l2 >>> 8).toUInt8,
      v.l2.toUInt8,
      (v.l1 >>> 56).toUInt8,
      (v.l1 >>> 48).toUInt8,
      (v.l1 >>> 40).toUInt8,
      (v.l1 >>> 32).toUInt8,
      (v.l1 >>> 24).toUInt8,
      (v.l1 >>> 16).toUInt8,
      (v.l1 >>> 8).toUInt8,
      v.l1.toUInt8,
      (v.l0 >>> 56).toUInt8,
      (v.l0 >>> 48).toUInt8,
      (v.l0 >>> 40).toUInt8,
      (v.l0 >>> 32).toUInt8,
      (v.l0 >>> 24).toUInt8,
      (v.l0 >>> 16).toUInt8,
      (v.l0 >>> 8).toUInt8,
      v.l0.toUInt8] := by
  simp [wordsBytes, pushBE64, ByteArray.push, ByteArray.emptyWithCapacity]
  rfl

/-- `toBytesBE` computes the spec's `Fp.toBytesBE` of `val` (any input:
`decode` canonicalizes). -/
theorem toBytesBE_eq_spec (a : Fp) : toBytesBE a = EthLib.Cryptography.Bls.Fp.toBytesBE a.val := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [toBytesBE_eq_words, wordsBytes_toList, EthLib.Cryptography.Bls.Fp.toBytesBE]
  simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero]
  have hX := decode_raw a
  generalize decode a = v at *
  generalize (a.val : Nat) = X at *
  have := v.l0.toNat_lt; have := v.l1.toNat_lt; have := v.l2.toNat_lt
  have := v.l3.toNat_lt; have := v.l4.toNat_lt; have := v.l5.toNat_lt
  simp only [raw] at hX
  simp only [List.cons.injEq, and_true]
  and_intros <;>
  · apply UInt8.toNat_inj.mp
    simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofNat', UInt64.toNat_shiftRight,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Fin.val_succ,
      Fin.val_zero]
    omega

/-! ## Wide reduction: `ofBytes64BE` -/

theorem extract_get! (b : ByteArray) (s e i : Nat) (hi : s + i < e) (he : e ≤ b.size) :
    (b.extract s e).get! i = b.get! (s + i) := by
  show (b.extract s e).data[i]! = b.data[s + i]!
  rw [ByteArray.data_extract]
  have h1 : i < (b.data.extract s e).size := by
    rw [Array.size_extract]
    have : b.data.size = b.size := rfl
    omega
  have h2 : s + i < b.data.size := by
    have : b.data.size = b.size := rfl
    omega
  rw [getElem!_pos _ i h1, getElem!_pos b.data (s + i) h2, Array.getElem_extract]

theorem bytesVal_extract (b : ByteArray) (s e n : Nat) (hn : s + n ≤ e) (he : e ≤ b.size) :
    bytesVal (b.extract s e) 0 n = bytesVal b s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bytesVal, bytesVal, ih (by omega), extract_get! b s e (0 + n) (by omega) he, Nat.zero_add]

/-- Four big-endian words as the low half of a vector. -/
theorem quad_raw (b : ByteArray) (off : Nat) :
    (⟨be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off, 0, 0⟩ : Fp).raw =
      bytesVal b off 32 := by
  have h1 := bytesVal_add b off 24 8
  have h2 := bytesVal_add b off 16 8
  have h3 := bytesVal_add b off 8 8
  have h4 := bytesVal_add b off 0 8
  simp only [raw, be64_toNat, UInt64.toNat_zero, Nat.reduceAdd, Nat.add_zero] at *
  simp only [bytesVal, Nat.zero_mul, Nat.zero_add] at h4
  omega

theorem ofBytes64BE_eq (b : ByteArray) (off : Nat) : ofBytes64BE b off =
    add (mul ⟨be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off, 0, 0⟩ C256)
      (mul ⟨be64 b (off + 56), be64 b (off + 48), be64 b (off + 40), be64 b (off + 32), 0, 0⟩ R2) :=
  rfl

set_option exponentiation.threshold 512 in
theorem pow256_lt_modulus : 256 ^ 32 < modulus := by decide

/-- `ofBytes64BE` is RFC 9380's OS2IP-and-reduce of the 64 bytes at `off`. -/
theorem ofBytes64BE_spec (b : ByteArray) (off : Nat) (h : off + 64 ≤ b.size) :
    Canonical (ofBytes64BE b off) ∧
      (ofBytes64BE b off).val = EthLib.Cryptography.Bls.Fp.ofNat
        (EthLib.Cryptography.Bls.Fp.bytesBEToNat (b.extract off (off + 64))) := by
  have hA := quad_raw b off
  have hC := quad_raw b (off + 32)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hC
  rw [ofBytes64BE_eq]
  generalize (⟨be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off, 0, 0⟩ : Fp) = A
    at *
  generalize (⟨be64 b (off + 56), be64 b (off + 48), be64 b (off + 40), be64 b (off + 32), 0, 0⟩ :
    Fp) = C at *
  have cA : Canonical A := by
    unfold Canonical; rw [hA]; exact lt_trans (bytesVal_lt _ _ _) pow256_lt_modulus
  have cC : Canonical C := by
    unfold Canonical; rw [hC]; exact lt_trans (bytesVal_lt _ _ _) pow256_lt_modulus
  have m1 := mul_canonical A C256_canonical
  have m2 := mul_canonical C R2_canonical
  refine ⟨add_canonical m1 m2, ?_⟩
  rw [val_add m1 m2, val_mul _ C256_canonical, val_mul _ R2_canonical, val_C256, val_R2]
  apply toZMod.injective
  rw [toZMod_add, toZMod_mul, toZMod_mul, toZ_val, toZ_val, toZMod_ofNat, toZMod_ofNat, toZMod_ofNat,
    bytesBEToNat_eq, ByteArray.size_extract, show min (off + 64) b.size - off = 64 by omega,
    bytesVal_extract b off (off + 64) 64 (by omega) h, show (64 : Nat) = 32 + 32 from rfl,
    bytesVal_add, ← hA, ← hC]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (640 : Nat) = 256 + 384 from rfl, pow_add, show (256 : Z) = 2 ^ 8 by norm_num,
    ← pow_mul]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  generalize (2 : Z) ^ (8 * 32) = T
  linear_combination ((A.raw : Z) * T + C.raw) * hr

/-! ## Wide products and lazy reduction

Proofs for `mulWide`, `addRaw`, `redc`, `sub12` and `subWideModPR`, which
`Fp2.mulI` composes into a lazily reduced Karatsuba product. -/

/-- The low six words of a twelve-word value. -/
def W12.lo (t : W12) : Fp := ⟨t.w0, t.w1, t.w2, t.w3, t.w4, t.w5⟩

/-- The high six words of a twelve-word value. -/
def W12.hi (t : W12) : Fp := ⟨t.w6, t.w7, t.w8, t.w9, t.w10, t.w11⟩

/-- The integer twelve words spell. -/
def W12.val (t : W12) : Nat := t.lo.raw + 2 ^ 384 * t.hi.raw

/-- Twelve words from two halves. -/
def W12.ofHalves (l h : Fp) : W12 :=
  ⟨l.l0, l.l1, l.l2, l.l3, l.l4, l.l5, h.l0, h.l1, h.l2, h.l3, h.l4, h.l5⟩

theorem W12.val_ofHalves (l h : Fp) : (W12.ofHalves l h).val = l.raw + 2 ^ 384 * h.raw := rfl

theorem W12.val_lt (t : W12) : t.val < 2 ^ 768 := by
  have := raw_lt t.lo
  have := raw_lt t.hi
  unfold W12.val
  omega

theorem Acc7.val_split (r : Acc7) :
    r.val = r.w0.toNat + 2 ^ 64 * (⟨r.w1, r.w2, r.w3, r.w4, r.w5, r.w6⟩ : Fp).raw := rfl

/-- `mulWide` is the exact 768-bit product. -/
theorem mulWide_val (a b : Fp) : (mulWide a b).val = a.raw * b.raw := by
  simp only [mulWide]
  have e0 := mulRow_val zero a.l0 b
  have s0 := Acc7.val_split (mulRow zero a.l0 b)
  generalize mulRow zero a.l0 b = r0 at *
  have e1 := mulRow_val ⟨r0.w1, r0.w2, r0.w3, r0.w4, r0.w5, r0.w6⟩ a.l1 b
  have s1 := Acc7.val_split (mulRow ⟨r0.w1, r0.w2, r0.w3, r0.w4, r0.w5, r0.w6⟩ a.l1 b)
  generalize mulRow ⟨r0.w1, r0.w2, r0.w3, r0.w4, r0.w5, r0.w6⟩ a.l1 b = r1 at *
  have e2 := mulRow_val ⟨r1.w1, r1.w2, r1.w3, r1.w4, r1.w5, r1.w6⟩ a.l2 b
  have s2 := Acc7.val_split (mulRow ⟨r1.w1, r1.w2, r1.w3, r1.w4, r1.w5, r1.w6⟩ a.l2 b)
  generalize mulRow ⟨r1.w1, r1.w2, r1.w3, r1.w4, r1.w5, r1.w6⟩ a.l2 b = r2 at *
  have e3 := mulRow_val ⟨r2.w1, r2.w2, r2.w3, r2.w4, r2.w5, r2.w6⟩ a.l3 b
  have s3 := Acc7.val_split (mulRow ⟨r2.w1, r2.w2, r2.w3, r2.w4, r2.w5, r2.w6⟩ a.l3 b)
  generalize mulRow ⟨r2.w1, r2.w2, r2.w3, r2.w4, r2.w5, r2.w6⟩ a.l3 b = r3 at *
  have e4 := mulRow_val ⟨r3.w1, r3.w2, r3.w3, r3.w4, r3.w5, r3.w6⟩ a.l4 b
  have s4 := Acc7.val_split (mulRow ⟨r3.w1, r3.w2, r3.w3, r3.w4, r3.w5, r3.w6⟩ a.l4 b)
  generalize mulRow ⟨r3.w1, r3.w2, r3.w3, r3.w4, r3.w5, r3.w6⟩ a.l4 b = r4 at *
  have e5 := mulRow_val ⟨r4.w1, r4.w2, r4.w3, r4.w4, r4.w5, r4.w6⟩ a.l5 b
  have s5 := Acc7.val_split (mulRow ⟨r4.w1, r4.w2, r4.w3, r4.w4, r4.w5, r4.w6⟩ a.l5 b)
  generalize mulRow ⟨r4.w1, r4.w2, r4.w3, r4.w4, r4.w5, r4.w6⟩ a.l5 b = r5 at *
  rw [zero_raw] at e0
  generalize hB : b.raw = B at *
  have hA : a.raw * B = a.l0.toNat * B + 2^64 * (a.l1.toNat * B + 2^64 * (a.l2.toNat * B +
      2^64 * (a.l3.toNat * B + 2^64 * (a.l4.toNat * B + 2^64 * (a.l5.toNat * B))))) := by
    simp only [raw]; ring
  rw [hA]
  clear hA
  simp only [W12.val, W12.lo, W12.hi, raw] at *
  generalize a.l0.toNat * B = X0 at *
  generalize a.l1.toNat * B = X1 at *
  generalize a.l2.toNat * B = X2 at *
  generalize a.l3.toNat * B = X3 at *
  generalize a.l4.toNat * B = X4 at *
  generalize a.l5.toNat * B = X5 at *
  omega

theorem addRaw_eq (a b : Fp) : addRaw a b = (adc6 a b).1 := rfl

/-- `addRaw` is exact when the sum fits in 384 bits. -/
theorem addRaw_raw {a b : Fp} (h : a.raw + b.raw < 2 ^ 384) :
    (addRaw a b).raw = a.raw + b.raw := by
  rw [addRaw_eq]
  obtain ⟨h1, h2⟩ := adc6_spec a b
  have := raw_lt (adc6 a b).1
  omega

/-- One Montgomery reduction row on a 384-bit value: divides by `2^64` after
adding a multiple `m·p` of the modulus. -/
theorem redStep (x : Fp) : ∃ m : Nat, m < 2 ^ 64 ∧
    (redRow ⟨x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, 0⟩).raw * 2 ^ 64 = x.raw + m * modulus := by
  have hx := raw_lt x
  have hp := modulus_lt_381
  have hv : Acc7.val ⟨x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, 0⟩ = x.raw := by
    simp only [Acc7.val, raw, UInt64.toNat_zero]; omega
  have hm := (x.l0 * N0).toNat_lt
  have hmp : (x.l0 * N0).toNat * modulus ≤ (2 ^ 64 - 1) * modulus :=
    Nat.mul_le_mul_right _ (by omega)
  have hside : Acc7.val ⟨x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, 0⟩ +
      (x.l0 * N0).toNat * modulus < 2 ^ 448 := by
    rw [hv]; omega
  refine ⟨(x.l0 * N0).toNat, hm, ?_⟩
  have h := redRow_spec ⟨x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, 0⟩ hside
  rw [hv] at h
  exact h

/-- `redc` divides a value below `p · R` by `R`, modulo `p`, canonically. -/
theorem redc_spec (t : W12) (h : t.val < modulus * 2 ^ 384) :
    Canonical (redc t) ∧ ((redc t).raw : Z) * 2 ^ 384 = (t.val : Z) := by
  have hlo := raw_lt t.lo
  have hhi : t.hi.raw < modulus := by unfold W12.val at h; omega
  have hH : (⟨t.w6, t.w7, t.w8, t.w9, t.w10, t.w11⟩ : Fp) = t.hi := rfl
  simp only [redc]
  rw [hH]
  obtain ⟨m0, hm0, e0⟩ := redStep ⟨t.w0, t.w1, t.w2, t.w3, t.w4, t.w5⟩
  have e0' : (redRow ⟨t.w0, t.w1, t.w2, t.w3, t.w4, t.w5, 0⟩).raw * 2 ^ 64 =
      t.lo.raw + m0 * modulus := e0
  clear e0
  generalize redRow ⟨t.w0, t.w1, t.w2, t.w3, t.w4, t.w5, 0⟩ = V1 at *
  obtain ⟨m1, hm1, e1⟩ := redStep V1
  generalize redRow ⟨V1.l0, V1.l1, V1.l2, V1.l3, V1.l4, V1.l5, 0⟩ = V2 at *
  obtain ⟨m2, hm2, e2⟩ := redStep V2
  generalize redRow ⟨V2.l0, V2.l1, V2.l2, V2.l3, V2.l4, V2.l5, 0⟩ = V3 at *
  obtain ⟨m3, hm3, e3⟩ := redStep V3
  generalize redRow ⟨V3.l0, V3.l1, V3.l2, V3.l3, V3.l4, V3.l5, 0⟩ = V4 at *
  obtain ⟨m4, hm4, e4⟩ := redStep V4
  generalize redRow ⟨V4.l0, V4.l1, V4.l2, V4.l3, V4.l4, V4.l5, 0⟩ = V5 at *
  obtain ⟨m5, hm5, e5⟩ := redStep V5
  generalize redRow ⟨V5.l0, V5.l1, V5.l2, V5.l3, V5.l4, V5.l5, 0⟩ = V6 at *
  have hM : (m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5))))) * modulus =
      m0 * modulus + 2^64 * (m1 * modulus + 2^64 * (m2 * modulus + 2^64 * (m3 * modulus +
      2^64 * (m4 * modulus + 2^64 * (m5 * modulus))))) := by ring
  have hT : V6.raw * 2 ^ 384 = t.lo.raw +
      (m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5))))) * modulus := by
    rw [hM]
    generalize m0 * modulus = k0 at *
    generalize m1 * modulus = k1 at *
    generalize m2 * modulus = k2 at *
    generalize m3 * modulus = k3 at *
    generalize m4 * modulus = k4 at *
    generalize m5 * modulus = k5 at *
    omega
  have hMb : m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5)))) ≤
      2 ^ 384 - 1 := by omega
  generalize m0 + 2^64 * (m1 + 2^64 * (m2 + 2^64 * (m3 + 2^64 * (m4 + 2^64 * m5)))) = M at *
  have hMp : M * modulus ≤ (2 ^ 384 - 1) * modulus := Nat.mul_le_mul_right _ hMb
  have hV6 : V6.raw ≤ modulus := by
    by_contra hc
    have : (modulus + 1) * 2 ^ 384 ≤ V6.raw * 2 ^ 384 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hsm := modulus_lt_381
  have hadd := addRaw_raw (a := V6) (b := t.hi) (by omega)
  have hlt : (addRaw V6 t.hi).raw < 2 * modulus := by rw [hadd]; omega
  refine ⟨reduceOnce_canonical _ hlt, ?_⟩
  rw [reduceOnce_raw _ hlt, hadd, natCast_raw_mod]
  have hz := congrArg (fun n : Nat => (n : Z)) hT
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, natCast_modulus,
    mul_zero, add_zero] at hz
  simp only [W12.val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  set_option exponentiation.threshold 512 in linear_combination hz

/-- Six-word subtraction with an incoming borrow. -/
def sbb6c (x y : Fp) (c : UInt64) : Fp × UInt64 :=
  let r0 := sbb x.l0 y.l0 c
  let r1 := sbb x.l1 y.l1 r0.2
  let r2 := sbb x.l2 y.l2 r1.2
  let r3 := sbb x.l3 y.l3 r2.2
  let r4 := sbb x.l4 y.l4 r3.2
  let r5 := sbb x.l5 y.l5 r4.2
  (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, r5.2)

theorem sbb6c_spec (x y : Fp) (c : UInt64) (hc : c.toNat ≤ 1) :
    (sbb6c x y c).1.raw + y.raw + c.toNat = x.raw + 2 ^ 384 * (sbb6c x y c).2.toNat ∧
      (sbb6c x y c).2.toNat ≤ 1 := by
  have h0 := sbb_spec x.l0 y.l0 c hc
  have h1 := sbb_spec x.l1 y.l1 _ h0.2
  have h2 := sbb_spec x.l2 y.l2 _ h1.2
  have h3 := sbb_spec x.l3 y.l3 _ h2.2
  have h4 := sbb_spec x.l4 y.l4 _ h3.2
  have h5 := sbb_spec x.l5 y.l5 _ h4.2
  simp only [sbb6c, raw] at *
  omega

theorem sub12_eq (a b : W12) : sub12 a b =
    (W12.ofHalves (sbb6c a.lo b.lo 0).1 (sbb6c a.hi b.hi (sbb6c a.lo b.lo 0).2).1,
     (sbb6c a.hi b.hi (sbb6c a.lo b.lo 0).2).2) := rfl

/-- `sub12` is subtraction modulo `2^768`, with the final borrow. -/
theorem sub12_spec (a b : W12) :
    (sub12 a b).1.val + b.val = a.val + 2 ^ 768 * (sub12 a b).2.toNat ∧
      (sub12 a b).2.toNat ≤ 1 := by
  rw [sub12_eq]
  obtain ⟨l1, l2⟩ := sbb6c_spec a.lo b.lo 0 (by decide)
  obtain ⟨h1, h2⟩ := sbb6c_spec a.hi b.hi _ l2
  generalize sbb6c a.lo b.lo 0 = L at *
  generalize sbb6c a.hi b.hi L.2 = H at *
  simp only [W12.val_ofHalves] at *
  simp only [W12.val, UInt64.toNat_zero] at *
  omega

/-- No borrow when `b ≤ a`. -/
theorem sub12_exact (a b : W12) (h : b.val ≤ a.val) :
    (sub12 a b).1.val + b.val = a.val := by
  obtain ⟨s1, s2⟩ := sub12_spec a b
  have := W12.val_lt (sub12 a b).1
  omega

theorem subWideModPR_eq (a b : W12) : subWideModPR a b =
    W12.ofHalves (sub12 a b).1.lo
      (adc6 (sub12 a b).1.hi (maskP (0 - (sub12 a b).2))).1 := rfl

/-- `subWideModPR` is `a - b`, plus `p · R` exactly when that borrows. -/
theorem subWideModPR_spec (a b : W12) (ha : a.val < modulus * 2 ^ 384)
    (_hb : b.val < modulus * 2 ^ 384) :
    (subWideModPR a b).val < modulus * 2 ^ 384 ∧
    (a.val < b.val → (subWideModPR a b).val + b.val = a.val + modulus * 2 ^ 384) ∧
    (b.val ≤ a.val → (subWideModPR a b).val + b.val = a.val) := by
  obtain ⟨s1, s2⟩ := sub12_spec a b
  have hd := W12.val_lt (sub12 a b).1
  rw [subWideModPR_eq, W12.val_ofHalves]
  generalize sub12 a b = r at *
  obtain ⟨d, br⟩ := r
  simp only at s1 s2 hd ⊢
  have hdl := raw_lt d.lo
  have hdh := raw_lt d.hi
  have hdv : d.val = d.lo.raw + 2 ^ 384 * d.hi.raw := rfl
  rcases eq_zero_or_one s2 with rfl | rfl
  · rw [show (0 : UInt64) - 0 = 0 from rfl, maskP_zero]
    obtain ⟨c1, -⟩ := adc6_spec d.hi zero
    have := raw_lt (adc6 d.hi zero).1
    rw [zero_raw] at c1
    have z0 : (0 : UInt64).toNat = 0 := rfl
    have e : (adc6 d.hi zero).1.raw = d.hi.raw := by omega
    rw [e]
    have z0 : (0 : UInt64).toNat = 0 := rfl
    omega
  · rw [maskP_ones]
    obtain ⟨c1, c2⟩ := adc6_spec d.hi Pw
    have := raw_lt (adc6 d.hi Pw).1
    rw [Pw_raw] at c1
    have z1 : (1 : UInt64).toNat = 1 := rfl
    omega

/-- The wide product of canonical vectors is below `p · R`. -/
theorem mulWide_lt {a b : Fp} (ha : Canonical a) (_hb : Canonical b) :
    (mulWide a b).val < modulus * 2 ^ 384 := by
  rw [mulWide_val]
  have hbR := raw_lt b
  have hp : 0 < modulus := by decide
  unfold Canonical at ha
  calc a.raw * b.raw ≤ a.raw * 2 ^ 384 := Nat.mul_le_mul_left _ hbR.le
    _ < modulus * 2 ^ 384 := Nat.mul_lt_mul_of_pos_right ha (by positivity)

/-- The real part of the lazy Karatsuba product: in range, and congruent to
`a0·b0 - a1·b1` modulo `p`. -/
theorem lazy_re {a0 a1 b0 b1 : Fp} (ha0 : Canonical a0) (ha1 : Canonical a1)
    (hb0 : Canonical b0) (hb1 : Canonical b1) :
    (subWideModPR (mulWide a0 b0) (mulWide a1 b1)).val < modulus * 2 ^ 384 ∧
    (((subWideModPR (mulWide a0 b0) (mulWide a1 b1)).val : Nat) : Z) =
      (a0.raw : Z) * b0.raw - (a1.raw : Z) * b1.raw := by
  have h0 := mulWide_lt ha0 hb0
  have h1 := mulWide_lt ha1 hb1
  obtain ⟨hl, e1, e2⟩ := subWideModPR_spec _ _ h0 h1
  refine ⟨hl, ?_⟩
  have v0 := mulWide_val a0 b0
  have v1 := mulWide_val a1 b1
  generalize mulWide a0 b0 = T0 at *
  generalize mulWide a1 b1 = T1 at *
  generalize subWideModPR T0 T1 = W at *
  rcases Nat.lt_or_ge T0.val T1.val with h | h
  · have e := e1 h
    rw [v0, v1] at e
    have z := congrArg (fun n : Nat => (n : Z)) e
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, natCast_modulus,
      zero_mul, add_zero] at z
    linear_combination z
  · have e := e2 h
    rw [v0, v1] at e
    have z := congrArg (fun n : Nat => (n : Z)) e
    simp only [Nat.cast_add, Nat.cast_mul] at z
    linear_combination z

/-- The imaginary part of the lazy Karatsuba product is exact. -/
theorem lazy_im {a0 a1 b0 b1 : Fp} (ha0 : Canonical a0) (ha1 : Canonical a1)
    (hb0 : Canonical b0) (hb1 : Canonical b1) :
    (sub12 (sub12 (mulWide (addRaw a0 a1) (addRaw b0 b1)) (mulWide a0 b0)).1
      (mulWide a1 b1)).1.val = a0.raw * b1.raw + a1.raw * b0.raw ∧
    (sub12 (sub12 (mulWide (addRaw a0 a1) (addRaw b0 b1)) (mulWide a0 b0)).1
      (mulWide a1 b1)).1.val < modulus * 2 ^ 384 := by
  unfold Canonical at *
  have hp := modulus_lt_381
  have sa : (addRaw a0 a1).raw = a0.raw + a1.raw := addRaw_raw (by omega)
  have sb : (addRaw b0 b1).raw = b0.raw + b1.raw := addRaw_raw (by omega)
  have v0 := mulWide_val a0 b0
  have v1 := mulWide_val a1 b1
  have v2 := mulWide_val (addRaw a0 a1) (addRaw b0 b1)
  rw [sa, sb] at v2
  have hx : (a0.raw + a1.raw) * (b0.raw + b1.raw) =
      a0.raw * b0.raw + a0.raw * b1.raw + a1.raw * b0.raw + a1.raw * b1.raw := by ring
  rw [hx] at v2
  have q01 : a0.raw * b1.raw ≤ modulus * modulus := Nat.mul_le_mul ha0.le hb1.le
  have q10 : a1.raw * b0.raw ≤ modulus * modulus := Nat.mul_le_mul ha1.le hb0.le
  have hpp : modulus * modulus + modulus * modulus < modulus * 2 ^ 384 := by
    have h2 : 2 * modulus < 2 ^ 384 := by omega
    have h3 := Nat.mul_lt_mul_of_pos_left h2 (show 0 < modulus by decide)
    have h4 : modulus * (2 * modulus) = modulus * modulus + modulus * modulus := by ring
    omega
  generalize mulWide a0 b0 = T0 at *
  generalize mulWide a1 b1 = T1 at *
  generalize mulWide (addRaw a0 a1) (addRaw b0 b1) = T2 at *
  generalize a0.raw * b0.raw = P00 at *
  generalize a0.raw * b1.raw = P01 at *
  generalize a1.raw * b0.raw = P10 at *
  generalize a1.raw * b1.raw = P11 at *
  have f1 := sub12_exact T2 T0 (by omega)
  generalize sub12 T2 T0 = D1 at *
  have f2 := sub12_exact D1.1 T1 (by omega)
  generalize sub12 D1.1 T1 = D2 at *
  omega

/-- A product law from a `ZMod` fact about raw integers: `c·R = a0·b0 - a1·b1`. -/
theorem val_sub_mul_of {c a0 b0 a1 b1 : Fp}
    (h : (c.raw : Z) * (2 : Z) ^ 384 = (a0.raw : Z) * b0.raw - (a1.raw : Z) * b1.raw) :
    c.val = a0.val * b0.val - a1.val * b1.val := by
  apply toZMod.injective
  rw [toZMod_sub, toZMod_mul, toZMod_mul, toZ_val, toZ_val, toZ_val, toZ_val, toZ_val]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  linear_combination ri ^ 2 * h - (c.raw : Z) * ri * hr

/-- A product law from a `ZMod` fact about raw integers: `c·R = a0·b1 + a1·b0`. -/
theorem val_add_mul_of {c a0 b1 a1 b0 : Fp}
    (h : (c.raw : Z) * (2 : Z) ^ 384 = (a0.raw : Z) * b1.raw + (a1.raw : Z) * b0.raw) :
    c.val = a0.val * b1.val + a1.val * b0.val := by
  apply toZMod.injective
  rw [map_add, toZMod_mul, toZMod_mul, toZ_val, toZ_val, toZ_val, toZ_val, toZ_val]
  have hr := toZ_rInv
  generalize toZMod rInv = ri at *
  generalize (2 : Z) ^ 384 = R at *
  linear_combination ri ^ 2 * h - (c.raw : Z) * ri * hr

end EthLibImpl.Cryptography.Bls.Fp
