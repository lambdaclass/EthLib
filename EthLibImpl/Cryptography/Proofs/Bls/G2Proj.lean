import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLib.Cryptography.Bls.Pairing
import EthLib.Cryptography.Proofs.Bls.G1Group

/-!
# Jacobian scaling on spec `G2` triples

The implementation's `hashToG2` skips two inversions by applying `ψ` and `ψ²` to Jacobian
triples without normalizing, so its result is the spec's point but not the spec's triple: the
two differ by a Jacobian scaling `(x, y, z) ↦ (l²x, l³y, lz)`. This file defines that relation,
`G2.ProjEq`, and proves it is compatible with everything the spec does with a point on the
way to the pairing:

* `ProjEq` is an equivalence relation, and `neg`, `double`, `add`, `mulNat` respect it.
  Nothing here needs the curve equation: it is pure formula algebra over the commutative ring
  `Fp2`.
* `isInfinity` and `toAffine` are `ProjEq`-invariant, hence so is `Embedded.ofG2`.
* `pairingCheck_congr_two_g2`: the spec pairing check reads a `G2` point only through
  `Embedded.ofG2`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLib.Cryptography.Bls.G2

open scoped EthLib.Cryptography.Bls.Fp2

/-- Two triples for the same point: both at infinity, or `Q` is `P` scaled. -/
def ProjEq (P Q : G2) : Prop :=
  (P.z = 0 ∧ Q.z = 0) ∨ ∃ l : Fp2, l ≠ 0 ∧ Q = ⟨l * l * P.x, l * l * l * P.y, l * P.z⟩

/-- The Jacobian scaling by `l`. -/
def scale (l : Fp2) (P : G2) : G2 := ⟨l * l * P.x, l * l * l * P.y, l * P.z⟩

theorem ext' {P Q : G2} (hx : P.x = Q.x) (hy : P.y = Q.y) (hz : P.z = Q.z) : P = Q := by
  cases P; cases Q; simp_all

theorem fp2_isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := by
  unfold Fp2.isZero
  rw [Bool.and_eq_true, G1.isZero_iff, G1.isZero_iff, Fp2.ext_iff]
  rfl

theorem fp2_beq_iff {a b : Fp2} : a.beq b = true ↔ a = b := by
  unfold Fp2.beq
  rw [Bool.and_eq_true, G1.beq_iff, G1.beq_iff, Fp2.ext_iff]

theorem isInfinity_iff_z {P : G2} : P.isInfinity = true ↔ P.z = 0 := fp2_isZero_iff

namespace ProjEq

theorem refl (P : G2) : ProjEq P P := by
  by_cases h : P.z = 0
  · exact Or.inl ⟨h, h⟩
  · refine Or.inr ⟨1, one_ne_zero, ?_⟩
    apply ext' <;> simp

theorem z_zero_iff {P Q : G2} (h : ProjEq P Q) : P.z = 0 ↔ Q.z = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨l, hl, rfl⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · simp only [mul_eq_zero, hl, false_or]

theorem symm {P Q : G2} (h : ProjEq P Q) : ProjEq Q P := by
  rcases h with ⟨h1, h2⟩ | ⟨l, hl, rfl⟩
  · exact Or.inl ⟨h2, h1⟩
  · refine Or.inr ⟨l⁻¹, inv_ne_zero hl, ?_⟩
    apply ext' <;> simp <;> field_simp

theorem trans {P Q R : G2} (h1 : ProjEq P Q) (h2 : ProjEq Q R) : ProjEq P R := by
  rcases h1 with ⟨a1, a2⟩ | ⟨l, hl, rfl⟩
  · rcases h2 with ⟨b1, b2⟩ | ⟨m, hm, rfl⟩
    · exact Or.inl ⟨a1, b2⟩
    · exact Or.inl ⟨a1, by simp [a2]⟩
  · rcases h2 with ⟨b1, b2⟩ | ⟨m, hm, rfl⟩
    · exact Or.inl ⟨by simpa [hl] using b1, b2⟩
    · refine Or.inr ⟨m * l, mul_ne_zero hm hl, ?_⟩
      apply ext' <;> simp <;> ring

/-- A scaled triple is `ProjEq` to the original. -/
theorem scale_of_ne {l : Fp2} (hl : l ≠ 0) (P : G2) : ProjEq P (scale l P) :=
  Or.inr ⟨l, hl, rfl⟩

theorem neg {P Q : G2} (h : ProjEq P Q) : ProjEq (neg P) (neg Q) := by
  rcases h with ⟨h1, h2⟩ | ⟨l, hl, rfl⟩
  · exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨l, hl, ?_⟩
    apply ext' <;> simp [G2.neg]

theorem double {P Q : G2} (h : ProjEq P Q) : ProjEq (double P) (double Q) := by
  by_cases hz : P.z = 0
  · have hz' : Q.z = 0 := (z_zero_iff h).mp hz
    have a : ¬ ¬ P.z.isZero = true := not_not.mpr (fp2_isZero_iff.mpr hz)
    have b : ¬ ¬ Q.z.isZero = true := not_not.mpr (fp2_isZero_iff.mpr hz')
    unfold G2.double
    rw [if_pos (not_not.mp a), if_pos (not_not.mp b)]
    exact h
  · rcases h with ⟨h1, h2⟩ | ⟨l, hl, rfl⟩
    · exact absurd h1 hz
    · have hP : ¬ P.z.isZero = true := by rwa [fp2_isZero_iff]
      have hP2 : ¬ (⟨l * l * P.x, l * l * l * P.y, l * P.z⟩ : G2).z.isZero = true := by
        rw [fp2_isZero_iff]; exact mul_ne_zero hl hz
      unfold G2.double
      rw [if_neg hP, if_neg hP2]
      dsimp only
      generalize Fp2.ofFp (Fp.ofNat 2) = two
      generalize Fp2.ofFp (Fp.ofNat 3) = three
      generalize Fp2.ofFp (Fp.ofNat 8) = eight
      refine Or.inr ⟨l ^ 4, pow_ne_zero 4 hl, ?_⟩
      apply ext' <;> dsimp only <;> ring

/-- `add` on two finite points scaled by `l` and `m`. -/
theorem add_scale {l m : Fp2} (hl : l ≠ 0) (hm : m ≠ 0) {P Q : G2} (hP : P.z ≠ 0)
    (hQ : Q.z ≠ 0) : ProjEq (G2.add P Q) (G2.add (scale l P) (scale m Q)) := by
  have hP' : ¬ P.z.isZero = true := by rwa [fp2_isZero_iff]
  have hQ' : ¬ Q.z.isZero = true := by rwa [fp2_isZero_iff]
  have hP2 : ¬ (scale l P).z.isZero = true := by
    rw [fp2_isZero_iff]; exact mul_ne_zero hl hP
  have hQ2 : ¬ (scale m Q).z.isZero = true := by
    rw [fp2_isZero_iff]; exact mul_ne_zero hm hQ
  have hlm : l * m ≠ 0 := mul_ne_zero hl hm
  have hsq : l * l * (m * m) ≠ 0 := mul_ne_zero (mul_ne_zero hl hl) (mul_ne_zero hm hm)
  have hcu : l * l * (m * m) * (l * l * (m * m)) * (l * l * (m * m)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hsq hsq) hsq
  unfold G2.add
  rw [if_neg hP', if_neg hQ', if_neg hP2, if_neg hQ2]
  dsimp only [scale]
  generalize Fp2.ofFp (Fp.ofNat 2) = two
  by_cases hu : P.x * (Q.z * Q.z) = Q.x * (P.z * P.z)
  · have hu' : l * l * P.x * (m * Q.z * (m * Q.z)) = m * m * Q.x * (l * P.z * (l * P.z)) := by
      linear_combination (l * l * (m * m)) * hu
    rw [if_pos (fp2_beq_iff.mpr hu), if_pos (fp2_beq_iff.mpr hu')]
    by_cases hs : P.y * Q.z * (Q.z * Q.z) = Q.y * P.z * (P.z * P.z)
    · have hs' : l * l * l * P.y * (m * Q.z) * (m * Q.z * (m * Q.z)) =
          m * m * m * Q.y * (l * P.z) * (l * P.z * (l * P.z)) := by
        linear_combination (l * l * l * (m * m * m)) * hs
      rw [if_pos (fp2_beq_iff.mpr hs), if_pos (fp2_beq_iff.mpr hs')]
      exact double (scale_of_ne hl P)
    · have hs' : ¬ (l * l * l * P.y * (m * Q.z) * (m * Q.z * (m * Q.z))).beq
          (m * m * m * Q.y * (l * P.z) * (l * P.z * (l * P.z))) = true := by
        intro h
        have h := fp2_beq_iff.mp h
        apply hs
        have h2 : (l * l * l * (m * m * m)) * (P.y * Q.z * (Q.z * Q.z)) =
            (l * l * l * (m * m * m)) * (Q.y * P.z * (P.z * P.z)) := by
          linear_combination h
        exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hl hl) hl)
          (mul_ne_zero (mul_ne_zero hm hm) hm)) h2
      rw [if_neg (fun h => hs (fp2_beq_iff.mp h)), if_neg hs']
      exact refl _
  · have hu' : ¬ (l * l * P.x * (m * Q.z * (m * Q.z))).beq
        (m * m * Q.x * (l * P.z * (l * P.z))) = true := by
      intro h
      have h := fp2_beq_iff.mp h
      apply hu
      have h2 : (l * l * (m * m)) * (P.x * (Q.z * Q.z)) =
          (l * l * (m * m)) * (Q.x * (P.z * P.z)) := by
        linear_combination h
      exact mul_left_cancel₀ hsq h2
    rw [if_neg (fun h => hu (fp2_beq_iff.mp h)), if_neg hu']
    refine Or.inr ⟨(l * m) ^ 3, pow_ne_zero 3 hlm, ?_⟩
    apply ext' <;> dsimp only <;> ring

theorem add {P P' Q Q' : G2} (hP : ProjEq P P') (hQ : ProjEq Q Q') :
    ProjEq (G2.add P Q) (G2.add P' Q') := by
  by_cases hz : P.z = 0
  · have hz' : P'.z = 0 := (z_zero_iff hP).mp hz
    unfold G2.add
    rw [if_pos (fp2_isZero_iff.mpr hz), if_pos (fp2_isZero_iff.mpr hz')]
    exact hQ
  have hz' : P'.z ≠ 0 := fun h => hz ((z_zero_iff hP).mpr h)
  by_cases hw : Q.z = 0
  · have hw' : Q'.z = 0 := (z_zero_iff hQ).mp hw
    unfold G2.add
    rw [if_neg (fun h => hz (fp2_isZero_iff.mp h)), if_pos (fp2_isZero_iff.mpr hw),
      if_neg (fun h => hz' (fp2_isZero_iff.mp h)), if_pos (fp2_isZero_iff.mpr hw')]
    exact hP
  rcases hP with ⟨h1, _⟩ | ⟨l, hl, rfl⟩
  · exact absurd h1 hz
  rcases hQ with ⟨h1, _⟩ | ⟨m, hm, rfl⟩
  · exact absurd h1 hw
  exact add_scale hl hm hz hw

private theorem mulNat_eq (p : G2) (k : Nat) : G2.mulNat p k =
    if k = 0 then G2.zero
    else
      let half := G2.mulNat (G2.double p) (k / 2)
      if k % 2 = 1 then G2.add p half else half := by
  rw [G2.mulNat]

theorem mulNat (k : Nat) : ∀ {P P' : G2}, ProjEq P P' → ProjEq (G2.mulNat P k) (G2.mulNat P' k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P P' h
    rw [mulNat_eq P k, mulNat_eq P' k]
    by_cases hk : k = 0
    · simp only [hk, if_true]
      exact refl _
    · simp only [hk, if_false]
      have := ih (k / 2) (by omega) (double h)
      split_ifs
      · exact add h this
      · exact this

theorem isInfinity_eq {P Q : G2} (h : ProjEq P Q) : P.isInfinity = Q.isInfinity := by
  rw [Bool.eq_iff_iff, isInfinity_iff_z, isInfinity_iff_z]
  exact z_zero_iff h

theorem toAffine_eq {P Q : G2} (h : ProjEq P Q) : P.toAffine = Q.toAffine := by
  by_cases hz : P.z = 0
  · have hz' : Q.z = 0 := (z_zero_iff h).mp hz
    unfold G2.toAffine
    rw [if_pos (fp2_isZero_iff.mpr hz), if_pos (fp2_isZero_iff.mpr hz')]
  · rcases h with ⟨h1, _⟩ | ⟨l, hl, rfl⟩
    · exact absurd h1 hz
    · have hP : ¬ P.z.isZero = true := by rwa [fp2_isZero_iff]
      have hP2 : ¬ (⟨l * l * P.x, l * l * l * P.y, l * P.z⟩ : G2).z.isZero = true := by
        rw [fp2_isZero_iff]; exact mul_ne_zero hl hz
      unfold G2.toAffine
      rw [if_neg hP, if_neg hP2]
      dsimp only
      simp only [Fp2.inverse_eq_inv, mul_inv]
      refine Prod.ext ?_ ?_ <;> dsimp only <;> field_simp

/-- `Embedded.ofG2` reads a point only through `isInfinity` and `toAffine`, which `ProjEq`
preserves. -/
theorem ofG2_eq {P Q : G2} (h : ProjEq P Q) : Embedded.ofG2 P = Embedded.ofG2 Q := by
  unfold Embedded.ofG2
  rw [isInfinity_eq h, toAffine_eq h]

end ProjEq

end EthLib.Cryptography.Bls.G2

namespace EthLib.Cryptography.Bls

/-- `pairingCheck` on two pairs reads the second `G2` point only through `Embedded.ofG2` and
`isInfinity`, which `G2.ProjEq` preserves. -/
theorem pairingCheck_congr_two_g2 (a : G1 × G2) (p : G1) {h h' : G2} (e : G2.ProjEq h h') :
    pairingCheck #[a, (p, h)] = pairingCheck #[a, (p, h')] := by
  simp only [pairingCheck, List.forIn_toArray, List.forIn_cons, List.forIn_nil]
  rw [G2.ProjEq.isInfinity_eq e, G2.ProjEq.ofG2_eq e]

end EthLib.Cryptography.Bls
