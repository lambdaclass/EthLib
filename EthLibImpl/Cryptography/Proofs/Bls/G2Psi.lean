import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.TwistFrobenius
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.G2Group
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2

/-!
# Proofs: the implementation's `ψ` on Jacobian triples

The spec proves that `ψ(x, y) = (c₁·x̄, c₂·ȳ)` (`x̄` the complex conjugate) is an
additive endomorphism of the twist `y² = x³ + b'` over `Fp2`
(`EthLib.Cryptography.Proofs.Bls.TwistFrobenius`: `mapPoint`, `hom`), that it
satisfies `ψ⁴ - ψ² + 1 = 0` (`G2.add_neg_hom_hom_add`, in
`EthLib.Cryptography.Proofs.Bls.G2Endomorphism`), and that its own `psi`, which
normalizes to affine coordinates first, computes it (`TwistFrobenius.toPoint_psi`).

The implementation applies `ψ` to Jacobian triples without normalizing
(`Mirror.G2.psiJ`), with the constants `c₁`, `c₂` written out. This file shows that
this is the same endomorphism:

* `conj`: conjugation as a ring hom of spec `Fp2`.
* `c1_eq_c1Psi`, `c2_eq_c2Psi`: the written-out constants are the spec's.
* `valid_psiJ`, `toPoint_psiJ`: `psiJ` preserves validity and computes
  `TwistFrobenius.hom` on the points spec triples denote.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2 (Valid toPoint rep curve bTwist c1Psi c2Psi isZero_iff)
open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian

/-! ## Conjugation -/

/-- Complex conjugation `c₀ + c₁·i ↦ c₀ - c₁·i` as a ring hom of spec `Fp2`. -/
def conj : Fp2 →+* Fp2 where
  toFun := Fp2.conjugate
  map_one' := by apply Fp2.ext <;> apply Fp.toZMod.injective <;> simp
  map_zero' := by apply Fp2.ext <;> apply Fp.toZMod.injective <;> simp
  map_mul' := Fp2.conjugate_mul
  map_add' := Fp2.conjugate_add

@[simp] theorem conj_apply (a : Fp2) : conj a = ⟨a.c0, -a.c1⟩ := rfl

theorem conj_eq_conjugate (a : Fp2) : conj a = a.conjugate := rfl

theorem conj_conj (a : Fp2) : conj (conj a) = a := Fp2.conjugate_conjugate a

theorem conj_injective : Function.Injective conj :=
  fun a b h => by rw [← conj_conj a, h, conj_conj]

/-! ## The constants -/

-- `c1` and `c2` are defined in `MirrorG2`, with `psiJ`.

/-- The implementation's `c₁` is the spec's `c1Psi`. -/
theorem c1_eq_c1Psi : c1 = (c1Psi : Fp2) := by
  apply Fp2.eq_of_model
  simp only [c1, HashToCurve.map_c1Psi, Fp2.map_mk, Fp.toModel_ofNat]
  decide +kernel

/-- The implementation's `c₂` is the spec's `c2Psi`. -/
theorem c2_eq_c2Psi : c2 = (c2Psi : Fp2) := by
  apply Fp2.eq_of_model
  simp only [c2, HashToCurve.map_c2Psi, Fp2.map_mk, Fp.toModel_ofNat]
  decide +kernel

theorem c1_ne_zero : c1 ≠ 0 := by
  decide_eq_at_model [c1]

theorem c2_ne_zero : c2 ≠ 0 := by
  decide_eq_at_model [c2]

/-- `c₂² = c₁³`. -/
theorem c2_sq : c2 ^ 2 = c1 ^ 3 := by
  rw [c1_eq_c1Psi, c2_eq_c2Psi, HashToCurve.c1Psi_cube]

/-- `c₂² · conj b' = b'`. -/
theorem c2_sq_mul_conj_b : c2 ^ 2 * conj bTwist = bTwist := by
  rw [c2_eq_c2Psi, conj_eq_conjugate]
  exact HashToCurve.c2Psi_twist

private theorem conj_two : conj (2 : Fp2) = 2 := map_ofNat conj 2

private theorem conj_three : conj (3 : Fp2) = 3 := map_ofNat conj 3

/-! ## `ψ` on spec triples -/

/-- `psiJ` unfolded to an explicit triple. -/
theorem psiJ_eq (P : G2) : psiJ P = ⟨c1 * conj P.x, c2 * conj P.y, conj P.z⟩ := rfl

theorem rep_psiJ_x (P : G2) : rep (psiJ P) 0 = c1 * conj (rep P 0) := rfl
theorem rep_psiJ_y (P : G2) : rep (psiJ P) 1 = c2 * conj (rep P 1) := rfl
theorem rep_psiJ_z (P : G2) : rep (psiJ P) 2 = conj (rep P 2) := rfl

private theorem nonsingular_of_psi {Q Q' : Fin 3 → Fp2}
    (h0 : Q' 0 = c1 * conj (Q 0)) (h1 : Q' 1 = c2 * conj (Q 1)) (h2 : Q' 2 = conj (Q 2))
    (h : curve.Nonsingular Q) : curve.Nonsingular Q' := by
  rw [nonsingular_iff, equation_iff] at h ⊢
  rw [h0, h1, h2]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = bTwist from rfl, zero_mul, mul_zero, add_zero, zero_add,
    zero_sub] at h ⊢
  obtain ⟨he, hn⟩ := h
  have he' := congrArg conj he
  simp only [_root_.map_sub, _root_.map_pow, _root_.map_add, _root_.map_mul,
    _root_.map_zero] at he'
  refine ⟨?_, ?_⟩
  · linear_combination c2 ^ 2 * he' + conj (Q 0) ^ 3 * c2_sq
      + conj (Q 2) ^ 6 * c2_sq_mul_conj_b
  · rcases hn with h | h | h
    · left
      intro h'
      apply h
      have h1 : c1 ^ 2 * conj (-(3 * Q 0 ^ 2)) = 0 := by
        rw [_root_.map_neg, _root_.map_mul, _root_.map_pow, conj_three]
        linear_combination h'
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 c1_ne_zero))
    · right; left
      intro h'
      apply h
      have h1 : c2 * conj (2 * Q 1) = 0 := by
        rw [_root_.map_mul, conj_two]; linear_combination h'
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left c2_ne_zero)
    · right; right
      intro h'
      apply h
      have h1 : c2 ^ 2 * conj (-(6 * bTwist * Q 2 ^ 5)) = 0 := by
        rw [_root_.map_neg, _root_.map_mul, _root_.map_mul, _root_.map_pow, map_ofNat conj 6]
        linear_combination h' + (-6 * conj (Q 2) ^ 5) * c2_sq_mul_conj_b
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 c2_ne_zero))

/-- `ψ` preserves validity. -/
theorem valid_psiJ {P : G2} (h : Valid P) : Valid (psiJ P) :=
  nonsingular_of_psi (rep_psiJ_x P) (rep_psiJ_y P) (rep_psiJ_z P) h

/-- `psiJ` computes the spec's `ψ` (`TwistFrobenius.hom`) on the points spec triples
denote. -/
theorem toPoint_psiJ {P : G2} (h : Valid P) :
    toPoint (psiJ P) = TwistFrobenius.hom (toPoint P) := by
  by_cases hz : P.z.isZero = true
  · have hz' : rep P 2 = 0 := isZero_iff.mp hz
    have hz'' : rep (psiJ P) 2 = 0 := by rw [rep_psiJ_z, hz', _root_.map_zero]
    rw [toPoint, toPoint, Point.toAffine_of_Z_eq_zero hz', Point.toAffine_of_Z_eq_zero hz'',
      _root_.map_zero]
  · have hz' : rep P 2 ≠ 0 := fun h0 => hz (isZero_iff.mpr h0)
    have hz'' : rep (psiJ P) 2 ≠ 0 := by
      rw [rep_psiJ_z]; exact fun h0 => hz' ((map_eq_zero conj).mp h0)
    rw [toPoint, toPoint, Point.toAffine_of_Z_ne_zero (valid_psiJ h) hz'',
      Point.toAffine_of_Z_ne_zero h hz', TwistFrobenius.hom_apply]
    simp only [TwistFrobenius.mapPoint, Affine.Point.some.injEq, rep_psiJ_x, rep_psiJ_y,
      rep_psiJ_z, ← c1_eq_c1Psi, ← c2_eq_c2Psi, ← conj_eq_conjugate]
    refine ⟨?_, ?_⟩
    · rw [map_div₀, _root_.map_pow, mul_div_assoc]
    · rw [map_div₀, _root_.map_pow, mul_div_assoc]

end EthLibImpl.Cryptography.Bls.Mirror.G2
