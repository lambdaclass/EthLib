import EthLibImpl.Cryptography.Bls.Fp12
import EthLibImpl.Cryptography.Proofs.Bls.Fp
import EthLibImpl.Cryptography.Proofs.Bls.FpInv
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing

/-!
# Proofs: the implementation's `Fp2` computes the spec's `Fp2`

`toSpec` reads an implementation `Fp2` (twelve words) as the spec's
`Fp2` (a pair of `Fp`), through `Fp.val`. For every operation we prove a
canonicity lemma (canonical inputs give a canonical output) and a value
lemma (`toSpec (op x y) = specOp (toSpec x) (toSpec y)`), for both the
`@[inline]` `…I` form and the plain wrapper. The Karatsuba product and the
`(a + b)(a - b)` square are ring identities in `ZMod p`, proved
componentwise. `sqrt` and the batched inverses are not covered here.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Fp2

open EthLib.Cryptography.Bls.Fp (toZMod toZMod_add toZMod_sub toZMod_neg toZMod_mul toZMod_zero
  toZMod_one)

local notation "S2" => EthLib.Cryptography.Bls.Fp2
local notation "S" => EthLib.Cryptography.Bls.Fp

/-- `c0 + c1·i` has canonical components. -/
def Canonical (x : Fp2) : Prop := x.c0.Canonical ∧ x.c1.Canonical

/-- The spec element an implementation `Fp2` stands for. -/
def toSpec (x : Fp2) : S2 := ⟨x.c0.val, x.c1.val⟩

theorem c0_mk (a b : Fp) : (mk a b).c0 = a := rfl
theorem c1_mk (a b : Fp) : (mk a b).c1 = b := rfl
theorem mk_c0_c1 (x : Fp2) : mk x.c0 x.c1 = x := rfl

theorem toSpec_c0 (x : Fp2) : (toSpec x).c0 = x.c0.val := rfl
theorem toSpec_c1 (x : Fp2) : (toSpec x).c1 = x.c1.val := rfl

theorem toSpec_mk (a b : Fp) : toSpec (mk a b) = ⟨a.val, b.val⟩ := rfl

theorem canonical_mk {a b : Fp} (ha : a.Canonical) (hb : b.Canonical) : Canonical (mk a b) :=
  ⟨ha, hb⟩

/-- Spec `Fp2` extensionality (the spec has no `ext` lemma in scope here). -/
theorem spec_ext {a b : S2} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

/-- Two canonical implementation elements with the same image are equal. -/
theorem toSpec_inj {x y : Fp2} (hx : Canonical x) (hy : Canonical y)
    (h : toSpec x = toSpec y) : x = y := by
  have h0 : x.c0.val = y.c0.val := congrArg EthLib.Cryptography.Bls.Fp2.c0 h
  have h1 : x.c1.val = y.c1.val := congrArg EthLib.Cryptography.Bls.Fp2.c1 h
  rw [Fp.val_inj hx.1 hy.1] at h0
  rw [Fp.val_inj hx.2 hy.2] at h1
  rw [← mk_c0_c1 x, ← mk_c0_c1 y, h0, h1]

/-! ## Constants -/


/-- Prove an equation between spec `Fp` expressions in `ZMod p`. -/
local macro "fp_ring" : tactic =>
  `(tactic| (apply EthLib.Cryptography.Bls.Fp.toZMod.injective
             simp only [toZMod_add, toZMod_sub, toZMod_mul, toZMod_neg, toZMod_zero, toZMod_one]
             ring))

theorem zero_canonical : Canonical zero := ⟨Fp.zero_canonical, Fp.zero_canonical⟩
theorem one_canonical : Canonical one := ⟨Fp.one_canonical, Fp.zero_canonical⟩
theorem ofFp_canonical {x : Fp} (hx : x.Canonical) : Canonical (ofFp x) :=
  ⟨hx, Fp.zero_canonical⟩

theorem toSpec_zero : toSpec zero = EthLib.Cryptography.Bls.Fp2.zero := by
  show (⟨Fp.zero.val, Fp.zero.val⟩ : S2) = _
  rw [Fp.val_zero]; rfl

theorem toSpec_one : toSpec one = EthLib.Cryptography.Bls.Fp2.one := by
  show (⟨Fp.one.val, Fp.zero.val⟩ : S2) = _
  rw [Fp.val_zero, Fp.val_one]; rfl

theorem toSpec_ofFp (x : Fp) : toSpec (ofFp x) = EthLib.Cryptography.Bls.Fp2.ofFp x.val := by
  show (⟨x.val, Fp.zero.val⟩ : S2) = _
  rw [Fp.val_zero]; rfl

/-! ## Additive operations -/

theorem addI_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    Canonical (addI x y) :=
  ⟨Fp.addI_canonical hx.1 hy.1, Fp.addI_canonical hx.2 hy.2⟩

theorem toSpec_addI {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (addI x y) = toSpec x + toSpec y := by
  apply spec_ext
  · exact Fp.val_addI hx.1 hy.1
  · exact Fp.val_addI hx.2 hy.2

theorem add_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (add x y) :=
  addI_canonical hx hy

theorem toSpec_add {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (add x y) = toSpec x + toSpec y := toSpec_addI hx hy

theorem subI_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    Canonical (subI x y) :=
  ⟨Fp.subI_canonical hx.1 hy.1, Fp.subI_canonical hx.2 hy.2⟩

theorem toSpec_subI {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (subI x y) = toSpec x - toSpec y := by
  apply spec_ext
  · exact Fp.val_subI hx.1 hy.1
  · exact Fp.val_subI hx.2 hy.2

theorem sub_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (sub x y) :=
  subI_canonical hx hy

theorem toSpec_sub {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (sub x y) = toSpec x - toSpec y := toSpec_subI hx hy

theorem negI_canonical {x : Fp2} (hx : Canonical x) : Canonical (negI x) :=
  ⟨Fp.negI_canonical hx.1, Fp.negI_canonical hx.2⟩

theorem toSpec_negI {x : Fp2} (hx : Canonical x) : toSpec (negI x) = -toSpec x := by
  apply spec_ext
  · exact Fp.val_negI hx.1
  · exact Fp.val_negI hx.2

theorem neg_canonical {x : Fp2} (hx : Canonical x) : Canonical (neg x) := negI_canonical hx

theorem toSpec_neg {x : Fp2} (hx : Canonical x) : toSpec (neg x) = -toSpec x := toSpec_negI hx

theorem doubleI_canonical {x : Fp2} (hx : Canonical x) : Canonical (doubleI x) :=
  ⟨Fp.doubleI_canonical hx.1, Fp.doubleI_canonical hx.2⟩

theorem toSpec_doubleI {x : Fp2} (hx : Canonical x) : toSpec (doubleI x) = toSpec x + toSpec x := by
  apply spec_ext
  · exact Fp.val_doubleI hx.1
  · exact Fp.val_doubleI hx.2

theorem double_canonical {x : Fp2} (hx : Canonical x) : Canonical (double x) :=
  doubleI_canonical hx

theorem toSpec_double {x : Fp2} (hx : Canonical x) :
    toSpec (double x) = toSpec x + toSpec x := toSpec_doubleI hx

/-! ## Multiplicative operations -/

local notation "Z" => ZMod EthLib.Cryptography.Bls.Fp.modulus

/-- The lazy Karatsuba product: canonical, with parts `c0·R = x0·y0 - x1·y1` and
`c1·R = x0·y1 + x1·y0` on raw integers in `ZMod p`. -/
theorem mulI_parts {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    Canonical (mulI x y) ∧
    ((mulI x y).c0.raw : Z) * (2 : Z) ^ 384 =
      (x.c0.raw : Z) * (y.c0.raw : Z) - (x.c1.raw : Z) * (y.c1.raw : Z) ∧
    ((mulI x y).c1.raw : Z) * (2 : Z) ^ 384 =
      (x.c0.raw : Z) * (y.c1.raw : Z) + (x.c1.raw : Z) * (y.c0.raw : Z) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hW, hWz⟩ := Fp.lazy_re hx0 hx1 hy0 hy1
  obtain ⟨hVz, hV⟩ := Fp.lazy_im hx0 hx1 hy0 hy1
  have r1 := Fp.redc_spec _ hW
  have r2 := Fp.redc_spec _ hV
  have e : mulI x y = mk
      (Fp.redc (Fp.subWideModPR (Fp.mulWide x.c0 y.c0) (Fp.mulWide x.c1 y.c1)))
      (Fp.redc (Fp.sub12 (Fp.sub12 (Fp.mulWide (Fp.addRaw x.c0 x.c1) (Fp.addRaw y.c0 y.c1))
        (Fp.mulWide x.c0 y.c0)).1 (Fp.mulWide x.c1 y.c1)).1) := rfl
  rw [e]
  refine ⟨⟨r1.1, r2.1⟩, ?_, ?_⟩
  · show ((Fp.redc _).raw : Z) * 2 ^ 384 = _
    rw [r1.2, hWz]
  · show ((Fp.redc _).raw : Z) * 2 ^ 384 = _
    rw [r2.2, hVz]
    push_cast
    ring

theorem mulI_canonical {x y : Fp2} (_hx : Canonical x) (hy : Canonical y) :
    Canonical (mulI x y) :=
  (mulI_parts _hx hy).1

theorem toSpec_mulI {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (mulI x y) = toSpec x * toSpec y := by
  obtain ⟨-, h0, h1⟩ := mulI_parts hx hy
  apply spec_ext
  · show (mulI x y).c0.val = x.c0.val * y.c0.val - x.c1.val * y.c1.val
    exact Fp.val_sub_mul_of h0
  · show (mulI x y).c1.val = x.c0.val * y.c1.val + x.c1.val * y.c0.val
    exact Fp.val_add_mul_of h1

theorem mul_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (mul x y) :=
  mulI_canonical hx hy

theorem toSpec_mul {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (mul x y) = toSpec x * toSpec y := toSpec_mulI hx hy

/-- An unreduced sum of canonical elements stands for their sum. -/
theorem val_addRaw {a b : Fp} (ha : a.Canonical) (hb : b.Canonical) :
    (Fp.addRaw a b).val = a.val + b.val := by
  have h : a.raw + b.raw < 2 ^ 384 := by
    have := Fp.modulus_lt_381
    unfold Fp.Canonical at ha hb
    omega
  apply Fp.val_add_of
  rw [Fp.addRaw_raw h]
  push_cast
  ring

theorem sqrI_canonical {x : Fp2} (hx : Canonical x) : Canonical (sqrI x) :=
  ⟨Fp.mulI_canonical _ (Fp.subI_canonical hx.1 hx.2), Fp.mulI_canonical _ hx.2⟩

theorem toSpec_sqrI {x : Fp2} (hx : Canonical x) : toSpec (sqrI x) = toSpec x * toSpec x := by
  have hs := Fp.subI_canonical hx.1 hx.2
  apply spec_ext
  · show (Fp.mulI (Fp.addRaw x.c0 x.c1) (Fp.subI x.c0 x.c1)).val =
      x.c0.val * x.c0.val - x.c1.val * x.c1.val
    rw [Fp.val_mulI _ hs, val_addRaw hx.1 hx.2, Fp.val_subI hx.1 hx.2]
    fp_ring
  · show (Fp.mulI (Fp.addRaw x.c0 x.c0) x.c1).val = x.c0.val * x.c1.val + x.c1.val * x.c0.val
    rw [Fp.val_mulI _ hx.2, val_addRaw hx.1 hx.1]
    fp_ring

theorem sqr_canonical {x : Fp2} (hx : Canonical x) : Canonical (sqr x) := sqrI_canonical hx

theorem toSpec_sqr {x : Fp2} (hx : Canonical x) : toSpec (sqr x) = toSpec x * toSpec x :=
  toSpec_sqrI hx

theorem mulFp_canonical {x : Fp2} {s : Fp} (_hx : Canonical x) (hs : s.Canonical) :
    Canonical (mulFp x s) :=
  ⟨Fp.mulI_canonical _ hs, Fp.mulI_canonical _ hs⟩

theorem toSpec_mulFp {x : Fp2} {s : Fp} (_hx : Canonical x) (hs : s.Canonical) :
    toSpec (mulFp x s) = EthLibImpl.Cryptography.Bls.Mirror.fp2MulFp (toSpec x) s.val := by
  apply spec_ext
  · exact Fp.val_mulI _ hs
  · exact Fp.val_mulI _ hs

theorem mulByXiI_canonical {x : Fp2} (hx : Canonical x) : Canonical (mulByXiI x) :=
  ⟨Fp.subI_canonical hx.1 hx.2, Fp.addI_canonical hx.1 hx.2⟩

theorem toSpec_mulByXiI {x : Fp2} (hx : Canonical x) :
    toSpec (mulByXiI x) = EthLib.Cryptography.Bls.Fp2.mulByOnePlusI (toSpec x) := by
  apply spec_ext
  · exact Fp.val_subI hx.1 hx.2
  · exact Fp.val_addI hx.1 hx.2

theorem mulByXi_canonical {x : Fp2} (hx : Canonical x) : Canonical (mulByXi x) :=
  mulByXiI_canonical hx

theorem toSpec_mulByXi {x : Fp2} (hx : Canonical x) :
    toSpec (mulByXi x) = EthLib.Cryptography.Bls.Fp2.mulByOnePlusI (toSpec x) :=
  toSpec_mulByXiI hx

/-! ## Operator forms -/

theorem canonical_hAdd {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (x + y) :=
  add_canonical hx hy
theorem canonical_hSub {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (x - y) :=
  sub_canonical hx hy
theorem canonical_hMul {x y : Fp2} (hx : Canonical x) (hy : Canonical y) : Canonical (x * y) :=
  mul_canonical hx hy
theorem canonical_hNeg {x : Fp2} (hx : Canonical x) : Canonical (-x) := neg_canonical hx

theorem toSpec_hAdd {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x + y) = toSpec x + toSpec y := toSpec_add hx hy
theorem toSpec_hSub {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x - y) = toSpec x - toSpec y := toSpec_sub hx hy
theorem toSpec_hMul {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x * y) = toSpec x * toSpec y := toSpec_mul hx hy
theorem toSpec_hNeg {x : Fp2} (hx : Canonical x) : toSpec (-x) = -toSpec x := toSpec_neg hx

/-! ## Conjugation, inverse, division -/

theorem conj_eq (x : Fp2) : conj x = mk x.c0 (Fp.negI x.c1) := rfl

theorem conj_canonical {x : Fp2} (hx : Canonical x) : Canonical (conj x) := by
  rw [conj_eq]
  exact canonical_mk hx.1 (Fp.negI_canonical hx.2)

theorem toSpec_conj {x : Fp2} (hx : Canonical x) :
    toSpec (conj x) = EthLib.Cryptography.Bls.Fp2.conjugate (toSpec x) := by
  rw [conj_eq, toSpec_mk]
  apply spec_ext
  · rfl
  · exact Fp.val_negI hx.2

theorem inverse_canonical {x : Fp2} (hx : Canonical x) : Canonical (inverse x) := by
  have hn := Fp.add_canonical (Fp.mul_canonical x.c0 hx.1) (Fp.mul_canonical x.c1 hx.2)
  have hi := Fp.inverse_canonical hn
  exact ⟨Fp.mul_canonical _ hi, Fp.neg_canonical (Fp.mul_canonical _ hi)⟩

theorem toSpec_inverse {x : Fp2} (hx : Canonical x) :
    toSpec (inverse x) = EthLib.Cryptography.Bls.Fp2.inverse (toSpec x) := by
  have hm0 := Fp.mul_canonical x.c0 hx.1
  have hm1 := Fp.mul_canonical x.c1 hx.2
  have hn := Fp.add_canonical hm0 hm1
  have hi := Fp.inverse_canonical hn
  have hv : (Fp.inverse (Fp.add (Fp.mul x.c0 x.c0) (Fp.mul x.c1 x.c1))).val =
      EthLib.Cryptography.Bls.Fp.inverse (x.c0.val * x.c0.val + x.c1.val * x.c1.val) := by
    rw [Fp.val_inverse hn, Fp.val_add hm0 hm1, Fp.val_mul _ hx.1, Fp.val_mul _ hx.2]
  apply spec_ext
  · show (Fp.mul x.c0 (Fp.inverse (Fp.add (Fp.mul x.c0 x.c0) (Fp.mul x.c1 x.c1)))).val = _
    rw [Fp.val_mul _ hi, hv]
    rfl
  · show (Fp.neg (Fp.mul x.c1 (Fp.inverse (Fp.add (Fp.mul x.c0 x.c0) (Fp.mul x.c1 x.c1))))).val = _
    rw [Fp.val_neg (Fp.mul_canonical _ hi), Fp.val_mul _ hi, hv]
    rfl

theorem div_canonical {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    Canonical (x / y) := mulI_canonical hx (inverse_canonical hy)

theorem toSpec_div {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x / y) = toSpec x / toSpec y := by
  show toSpec (mul x (inverse y)) = toSpec x * EthLib.Cryptography.Bls.Fp2.inverse (toSpec y)
  rw [toSpec_mul hx (inverse_canonical hy), toSpec_inverse hy]

/-! ## Exponentiation -/

theorem powNat_canonical {x : Fp2} (hx : Canonical x) (e : Nat) : Canonical (powNat x e) := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [powNat]
    split
    · exact one_canonical
    · rename_i h
      have := ih (e / 2) (by omega) (mul_canonical hx hx)
      split
      · exact mul_canonical hx this
      · exact this

theorem toSpec_powNat {x : Fp2} (hx : Canonical x) (e : Nat) :
    toSpec (powNat x e) = EthLib.Cryptography.Bls.Fp2.powNat (toSpec x) e := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [powNat, EthLib.Cryptography.Bls.Fp2.powNat]
    by_cases h : e = 0
    · rw [if_pos h, if_pos h]; exact toSpec_one
    · rw [if_neg h, if_neg h]
      have h3 : toSpec (x * x) = toSpec x * toSpec x := toSpec_mul hx hx
      have key : toSpec (powNat (x * x) (e / 2)) =
          EthLib.Cryptography.Bls.Fp2.powNat (toSpec x * toSpec x) (e / 2) := by
        rw [← h3]; exact ih (e / 2) (by omega) (mul_canonical hx hx)
      have hc := powNat_canonical (mul_canonical hx hx) (e / 2)
      by_cases h2 : e % 2 = 1
      · rw [if_pos h2, if_pos h2]
        exact (toSpec_mul hx hc).trans (congrArg (toSpec x * ·) key)
      · rw [if_neg h2, if_neg h2]; exact key

/-! ## Predicates -/

theorem spec_isZero_iff (a : S) : a.isZero = true ↔ a = 0 := by
  unfold EthLib.Cryptography.Bls.Fp.isZero
  rw [beq_iff_eq, Fin.ext_iff]
  rfl

theorem fp_isZero_eq {a : Fp} (ha : a.Canonical) : a.isZero = a.val.isZero := by
  rw [Bool.eq_iff_iff, Fp.isZero_iff ha, spec_isZero_iff]

theorem fp_beq_eq {a b : Fp} (ha : a.Canonical) (hb : b.Canonical) :
    a.beq b = a.val.beq b.val := by
  rw [Bool.eq_iff_iff, Fp.beq_iff ha hb, EthLib.Cryptography.Bls.Fp.beq_eq_true_iff]

theorem isZero_eq {x : Fp2} (hx : Canonical x) :
    (toSpec x).isZero = x.isZero := by
  show (x.c0.val.isZero && x.c1.val.isZero) = (x.c0.isZero && x.c1.isZero)
  rw [fp_isZero_eq hx.1, fp_isZero_eq hx.2]

theorem beq_eq {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    (toSpec x).beq (toSpec y) = x.beq y := by
  show (x.c0.val.beq y.c0.val && x.c1.val.beq y.c1.val) = (x.c0.beq y.c0 && x.c1.beq y.c1)
  rw [fp_beq_eq hx.1 hy.1, fp_beq_eq hx.2 hy.2]

theorem beq_iff {x y : Fp2} (hx : Canonical x) (hy : Canonical y) :
    x.beq y = true ↔ toSpec x = toSpec y := by
  rw [← beq_eq hx hy]
  show (x.c0.val.beq y.c0.val && x.c1.val.beq y.c1.val) = true ↔ _
  rw [Bool.and_eq_true, EthLib.Cryptography.Bls.Fp.beq_eq_true_iff,
    EthLib.Cryptography.Bls.Fp.beq_eq_true_iff]
  constructor
  · rintro ⟨h0, h1⟩; exact spec_ext h0 h1
  · intro h; exact ⟨congrArg EthLib.Cryptography.Bls.Fp2.c0 h, congrArg EthLib.Cryptography.Bls.Fp2.c1 h⟩

theorem isZero_iff {x : Fp2} (hx : Canonical x) :
    x.isZero = true ↔ toSpec x = EthLib.Cryptography.Bls.Fp2.zero := by
  rw [← isZero_eq hx]
  show (x.c0.val.isZero && x.c1.val.isZero) = true ↔ _
  rw [Bool.and_eq_true, spec_isZero_iff, spec_isZero_iff]
  constructor
  · rintro ⟨h0, h1⟩; exact spec_ext h0 h1
  · intro h; exact ⟨congrArg EthLib.Cryptography.Bls.Fp2.c0 h, congrArg EthLib.Cryptography.Bls.Fp2.c1 h⟩

end EthLibImpl.Cryptography.Bls.Fp2
