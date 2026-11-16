import EthLibImpl.Cryptography.Proofs.Bls.FinalExp
import EthLibImpl.Cryptography.Proofs.Bls.MillerStep
import EthLib.Cryptography.Proofs.Bls.PairingCongr

/-!
# Proofs: the implementation's pairing check is the spec's

`Mirror.pairingCheck_eq`: for every array of pairs (any spec `G1 × G2` values, on
the curve or not, of any order), the implementation's pairing check (mirrored over
spec types in `MirrorPairing`) returns the spec's `pairingCheck`.

The two Miller loops do not compute the same `Fp12` value: the spec runs one loop
per pair from the affine points, while the implementation runs all pairs at once
from their Jacobian triples. Each of the implementation's steps is the spec's step
on a rescaled point, and stores the spec's line times `ι2 k` for a nonzero
`k : Fp2` (`MillerStep`). The final exponentiation sends such a factor to `1`
(`Killed`), so the two products differ by a factor it erases.

* Per pair (`SpecState`, `Rel`, `rel_dbl`, `rel_add`): a mirror entry `(pi, t)`
  stands for the spec's state when `pi` stands for the spec's affine inputs
  (`InputRel`) and `t` is the spec's point rescaled by some `l ≠ 0`.
* All pairs (`dblAll_rel`, `addAll_rel`, `millerSteps_rel`): the mirror's running
  value is the product of the spec's per-pair values times a killed factor, bit by
  bit.
* Inputs (`inputRel_ofPoints`): `PairInput.ofPoints p q` stands for the spec's
  `q.toAffine` and `p.toAffine` whenever neither point is at infinity.
* Assembly (`pairingCheck_eq`): the spec's check is the final exponentiation of the
  product of its pairs' factors (`pairingCheck_eq_finalExp_prod`), the mirror
  filters the same pairs, conjugation is multiplicative, and `finalExpCube_eq`,
  `isOne_cube` and `(x · k) ^ E = x ^ E` for killed `k` finish.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography (BaseField)
open scoped EthLib.Cryptography.Bls.Fp
open Fp12 (ι2 mk6)

/-! ## Factors erased by the final exponentiation -/

/-- `k` is sent to `1` by the final exponent. -/
def Killed (k : Fp12) : Prop := k ^ finalExpExponent = 1

theorem killed_one : Killed 1 := one_pow _

theorem Killed.mul {a b : Fp12} (ha : Killed a) (hb : Killed b) : Killed (a * b) := by
  rw [Killed, mul_pow, ha, hb, mul_one]

theorem Killed.pow {a : Fp12} (ha : Killed a) (n : ℕ) : Killed (a ^ n) := by
  rw [Killed, ← pow_mul, mul_comm, pow_mul, ha, one_pow]

/-- A nonzero constant of `Fp2` is erased. -/
theorem killed_ι2 {c : Fp2} (hc : c ≠ 0) : Killed (ι2 c) := Fp12.ι2_pow_finalExpExponent hc

/-! ## Lines as `Fp12` elements -/

/-- The spec's line `c0 + c2 w² + c3 w³` in the `w`-power layout. -/
theorem lineValue_eq_mk6 (a b c : Fp2) : lineValue a b c = mk6 a 0 b c 0 0 := by
  rw [← Fp2.zero_eq_zero]; rfl

/-- Multiplying the three coefficients by `k` multiplies the line by `ι2 k`. -/
theorem lineValue_smul (k a b c : Fp2) :
    lineValue (k * a) (k * b) (k * c) = ι2 k * lineValue a b c := by
  rw [lineValue_eq_mk6, lineValue_eq_mk6, Fp12.mk6_decomp, Fp12.mk6_decomp]
  simp only [_root_.map_mul, _root_.map_zero]
  ring

private theorem ofFp_ne_zero {c : Fp} (hc : c ≠ 0) : Fp2.ofFp c ≠ 0 :=
  fun h => hc (congrArg Fp2.c0 h)

/-! ## Per-pair spec state -/

/-- One pair's state in the spec's Miller loop: the affine `Q = (xq, yq)` and
`P = (xp, yp)`, the running point `T` and the running value `f`. -/
structure SpecState where
  xq : Fp2
  yq : Fp2
  xp : Fp
  yp : Fp
  T : G2
  f : Fp12

/-- The spec's doubling step on one pair. -/
def SpecState.dbl (s : SpecState) : SpecState :=
  { s with T := (millerDouble s.T s.xp s.yp s.f).1, f := (millerDouble s.T s.xp s.yp s.f).2 }

/-- The spec's addition step on one pair. -/
def SpecState.add (s : SpecState) : SpecState :=
  { s with T := (millerAdd s.T s.xq s.yq s.xp s.yp s.f).1,
           f := (millerAdd s.T s.xq s.yq s.xp s.yp s.f).2 }

/-- The spec's remaining `n` Miller steps on one pair. -/
def SpecState.run (n : ℕ) (s : SpecState) : Fp12 :=
  EthLib.Cryptography.Bls.millerSteps blsX s.xq s.yq s.xp s.yp n s.T s.f

/-- One spec step: double, then add on a set bit. -/
theorem SpecState.run_succ (n : ℕ) (s : SpecState) :
    s.run (n + 1) = (if (blsX >>> n) &&& 1 = 1 then s.dbl.add else s.dbl).run n := by
  by_cases hb : (blsX >>> n) &&& 1 = 1
  · rw [if_pos hb]
    show EthLib.Cryptography.Bls.millerSteps _ _ _ _ _ _ _ _ = _
    rw [EthLib.Cryptography.Bls.millerSteps]
    simp only [hb, ↓reduceIte]
    rfl
  · rw [if_neg hb]
    show EthLib.Cryptography.Bls.millerSteps _ _ _ _ _ _ _ _ = _
    rw [EthLib.Cryptography.Bls.millerSteps]
    simp only [hb, ↓reduceIte]
    rfl

/-- A mirror loop entry `(pi, t)` stands for a spec state. -/
def Rel (x : PairInput × TwistPoint) (s : SpecState) : Prop :=
  InputRel x.1 s.xq s.yq s.xp s.yp ∧ ∃ l : Fp2, l ≠ 0 ∧ x.2 = scale s.T l

/-- One pair's doubling step: the mirror's line is the spec's line times a killed
factor, and the relation is kept. -/
theorem rel_dbl {x : PairInput × TwistPoint} {s : SpecState} (h : Rel x s) :
    ∃ L k, Killed k ∧ s.dbl.f = s.f * s.f * L ∧ (dblStep x.1 x.2).2.toFp12 = L * k ∧
      Rel (x.1, (dblStep x.1 x.2).1) s.dbl := by
  obtain ⟨hin, l, hl, hx⟩ := h
  obtain ⟨l', hl', hp⟩ := dblStep_point x.1 s.T hl
  have hk : Fp2.ofFp x.1.cz * l ^ 6 ≠ 0 := mul_ne_zero (ofFp_ne_zero hin.cz_ne) (pow_ne_zero 6 hl)
  refine ⟨lineValue (3 * (s.T.x * s.T.x) * s.T.x - 2 * (s.T.y * s.T.y))
      (-(3 * (s.T.x * s.T.x) * (s.T.z * s.T.z) * Fp2.ofFp s.xp))
      (2 * s.T.y * (s.T.z * s.T.z) * s.T.z * Fp2.ofFp s.yp),
    ι2 (Fp2.ofFp x.1.cz * l ^ 6), killed_ι2 hk, ?_, ?_, hin, l', hl', ?_⟩
  · show (millerDouble s.T s.xp s.yp s.f).2 = _
    rw [millerDouble_eq, three_eq, two_eq]
  · rw [hx, dblStep_line hin s.T l, lineValue_smul, mul_comm]
  · rw [hx, hp]
    rfl

/-- One pair's addition step: the mirror's line is the spec's line times a killed
factor, and the relation is kept. -/
theorem rel_add {x : PairInput × TwistPoint} {s : SpecState} (h : Rel x s) :
    ∃ L k, Killed k ∧ s.add.f = s.f * L ∧ (addStep x.1 x.2).2.toFp12 = L * k ∧
      Rel (x.1, (addStep x.1 x.2).1) s.add := by
  obtain ⟨hin, l, hl, hx⟩ := h
  obtain ⟨l', hl', hp⟩ := addStep_point hin.r_eq hin.rz_ne s.T hl
  have hk : Fp2.ofFp x.1.cz * (l ^ 3 * x.1.r.z ^ 5) ≠ 0 :=
    mul_ne_zero (ofFp_ne_zero hin.cz_ne) (mul_ne_zero (pow_ne_zero 3 hl) (pow_ne_zero 5 hin.rz_ne))
  refine ⟨lineValue
      ((s.yq * (s.T.z * s.T.z) * s.T.z - s.T.y) * s.xq - (s.xq * (s.T.z * s.T.z) - s.T.x) * s.T.z * s.yq)
      (-((s.yq * (s.T.z * s.T.z) * s.T.z - s.T.y) * Fp2.ofFp s.xp))
      ((s.xq * (s.T.z * s.T.z) - s.T.x) * s.T.z * Fp2.ofFp s.yp),
    ι2 (Fp2.ofFp x.1.cz * (l ^ 3 * x.1.r.z ^ 5)), killed_ι2 hk, ?_, ?_, hin, l', hl', ?_⟩
  · show (millerAdd s.T s.xq s.yq s.xp s.yp s.f).2 = _
    rw [millerAdd_eq]
  · rw [hx, addStep_line hin s.T l, lineValue_smul, mul_comm]
  · rw [hx, hp]
    rfl

/-! ## All pairs at once -/

theorem dblAll_nil (g : Fp12) : dblAll g [] = (g, []) := rfl

theorem dblAll_cons (g : Fp12) (pi : PairInput) (t : TwistPoint)
    (rest : List (PairInput × TwistPoint)) :
    dblAll g ((pi, t) :: rest) =
      ((dblAll (g * (dblStep pi t).2.toFp12) rest).1,
        (pi, (dblStep pi t).1) :: (dblAll (g * (dblStep pi t).2.toFp12) rest).2) := rfl

theorem addAll_nil (g : Fp12) : addAll g [] = (g, []) := rfl

theorem addAll_cons (g : Fp12) (pi : PairInput) (t : TwistPoint)
    (rest : List (PairInput × TwistPoint)) :
    addAll g ((pi, t) :: rest) =
      ((addAll (g * (addStep pi t).2.toFp12) rest).1,
        (pi, (addStep pi t).1) :: (addAll (g * (addStep pi t).2.toFp12) rest).2) := rfl

/-- `dblAll` multiplies the squared spec values by every pair's spec line, up to a
killed factor. -/
theorem dblAll_rel {st : List (PairInput × TwistPoint)} {ss : List SpecState}
    (hst : List.Forall₂ Rel st ss) :
    ∀ g h, g = (ss.map SpecState.f).prod ^ 2 * h → ∃ k, Killed k ∧
      (dblAll g st).1 = ((ss.map SpecState.dbl).map SpecState.f).prod * h * k ∧
      List.Forall₂ Rel (dblAll g st).2 (ss.map SpecState.dbl) := by
  induction hst with
  | nil =>
    intro g h hg
    refine ⟨1, killed_one, ?_, List.Forall₂.nil⟩
    rw [dblAll_nil, hg]
    simp
  | @cons x s st ss hxs _ ih =>
    intro g h hg
    obtain ⟨pi, t⟩ := x
    obtain ⟨L, k1, hk1, hf, hl, hr⟩ := rel_dbl hxs
    obtain ⟨k2, hk2, h1, h2⟩ := ih (g * (dblStep pi t).2.toFp12) (s.dbl.f * h * k1) (by
      rw [hg, hl, hf, List.map_cons, List.prod_cons]
      ring)
    refine ⟨k1 * k2, hk1.mul hk2, ?_, ?_⟩
    · rw [dblAll_cons, h1, List.map_cons, List.map_cons, List.prod_cons]
      ring
    · rw [dblAll_cons, List.map_cons]
      exact List.Forall₂.cons hr h2

/-- `addAll` multiplies the spec values by every pair's spec line, up to a killed
factor. -/
theorem addAll_rel {st : List (PairInput × TwistPoint)} {ss : List SpecState}
    (hst : List.Forall₂ Rel st ss) :
    ∀ g h, g = (ss.map SpecState.f).prod * h → ∃ k, Killed k ∧
      (addAll g st).1 = ((ss.map SpecState.add).map SpecState.f).prod * h * k ∧
      List.Forall₂ Rel (addAll g st).2 (ss.map SpecState.add) := by
  induction hst with
  | nil =>
    intro g h hg
    refine ⟨1, killed_one, ?_, List.Forall₂.nil⟩
    rw [addAll_nil, hg]
    simp
  | @cons x s st ss hxs _ ih =>
    intro g h hg
    obtain ⟨pi, t⟩ := x
    obtain ⟨L, k1, hk1, hf, hl, hr⟩ := rel_add hxs
    obtain ⟨k2, hk2, h1, h2⟩ := ih (g * (addStep pi t).2.toFp12) (s.add.f * h * k1) (by
      rw [hg, hl, hf, List.map_cons, List.prod_cons]
      ring)
    refine ⟨k1 * k2, hk1.mul hk2, ?_, ?_⟩
    · rw [addAll_cons, h1, List.map_cons, List.map_cons, List.prod_cons]
      ring
    · rw [addAll_cons, List.map_cons]
      exact List.Forall₂.cons hr h2

/-- One step of the mirror's loop, with the pair-destructuring `let`s unfolded. -/
theorem millerSteps_succ (n : ℕ) (st : List (PairInput × TwistPoint)) (f : Fp12) :
    millerSteps (n + 1) st f =
      millerSteps n
        (if (blsX >>> n) &&& 1 = 1 then addAll (dblAll (f * f) st).1 (dblAll (f * f) st).2
        else dblAll (f * f) st).2
        (if (blsX >>> n) &&& 1 = 1 then addAll (dblAll (f * f) st).1 (dblAll (f * f) st).2
        else dblAll (f * f) st).1 := by
  rw [millerSteps]

/-- The mirror's Miller steps compute the product of the spec's per-pair Miller
steps, up to a killed factor. -/
theorem millerSteps_rel (n : ℕ) : ∀ (st : List (PairInput × TwistPoint)) (ss : List SpecState),
    List.Forall₂ Rel st ss → ∀ g k, Killed k → g = (ss.map SpecState.f).prod * k →
      ∃ k', Killed k' ∧ millerSteps n st g = (ss.map (SpecState.run n)).prod * k' := by
  induction n with
  | zero =>
    intro st ss _ g k hk hg
    exact ⟨k, hk, hg⟩
  | succ n ih =>
    intro st ss hst g k hk hg
    obtain ⟨k1, hk1, h1, h2⟩ := dblAll_rel hst (g * g) (k ^ 2 * 1) (by rw [hg]; ring)
    rw [millerSteps_succ]
    by_cases hb : (blsX >>> n) &&& 1 = 1
    · simp only [if_pos hb]
      obtain ⟨k2, hk2, h3, h4⟩ := addAll_rel h2 (dblAll (g * g) st).1 (k ^ 2 * 1 * k1)
        (by rw [h1, mul_assoc])
      obtain ⟨k', hk', h5⟩ := ih _ _ h4 (addAll (dblAll (g * g) st).1 (dblAll (g * g) st).2).1 _
        ((((hk.pow 2).mul killed_one).mul hk1).mul hk2) (by rw [h3, mul_assoc])
      refine ⟨k', hk', ?_⟩
      have hrun : ss.map (SpecState.run (n + 1)) =
          ((ss.map SpecState.dbl).map SpecState.add).map (SpecState.run n) := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun s _ => by rw [SpecState.run_succ, if_pos hb]; rfl
      rw [h5, hrun]
    · simp only [if_neg hb]
      obtain ⟨k', hk', h5⟩ := ih _ _ h2 (dblAll (g * g) st).1 _
        (((hk.pow 2).mul killed_one).mul hk1) (by rw [h1, mul_assoc])
      refine ⟨k', hk', ?_⟩
      have hrun :
          ss.map (SpecState.run (n + 1)) = (ss.map SpecState.dbl).map (SpecState.run n) := by
        rw [List.map_map]
        exact List.map_congr_left fun s _ => by rw [SpecState.run_succ, if_neg hb]; rfl
      rw [h5, hrun]

/-! ## The loop's inputs -/

/-- The spec's affine coordinates of a twist point off infinity. -/
theorem G2.toAffine_of_ne {q : G2} (hz : q.z ≠ 0) :
    q.toAffine = (q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹)) := by
  have h : q.z.isZero = false := by rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; exact hz
  unfold G2.toAffine
  rw [h]
  rfl

/-- The spec's affine coordinates of a `G1` point off infinity. -/
theorem G1.toAffine_of_ne {p : G1} (hz : p.z ≠ 0) :
    p.toAffine = (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) := by
  have h : BaseField.isZero p.z = false := by
    rw [Fp.baseField_isZero, Bool.eq_false_iff, ne_eq, Fp.isZero_iff]; exact hz
  unfold G1.toAffine
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte, Fp.baseField_inverse, Fp.inverse_eq_inv]

private theorem g2_z_ne {q : G2} (hq : ¬q.isInfinity = true) : q.z ≠ 0 := by
  intro h; exact hq (Fp2.isZero_iff.mpr h)

private theorem g1_z_ne {p : G1} (hp : ¬p.isInfinity = true) : p.z ≠ 0 := by
  intro h; apply hp
  show BaseField.isZero p.z = true
  rw [Fp.baseField_isZero, Fp.isZero_iff]; exact h

/-- `PairInput.ofPoints p q` stands for the spec's affine `q` and `p`. -/
theorem inputRel_ofPoints {p : G1} {q : G2} (hp : ¬p.isInfinity = true)
    (hq : ¬q.isInfinity = true) :
    InputRel (PairInput.ofPoints p q) q.toAffine.1 q.toAffine.2 p.toAffine.1 p.toAffine.2 := by
  have hqz := g2_z_ne hq
  have hpz := g1_z_ne hp
  rw [G2.toAffine_of_ne hqz, G1.toAffine_of_ne hpz]
  have hr : (PairInput.ofPoints p q).r = ⟨q.x, q.y, q.z⟩ := by
    unfold PairInput.ofPoints; split <;> rfl
  have hrel : (PairInput.ofPoints p q).r =
      scale ⟨q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹), Fp2.one⟩
        (PairInput.ofPoints p q).r.z := by
    rw [hr]
    simp only [scale, Fp2.one_eq_one, mul_one, TwistPoint.mk.injEq]
    refine ⟨?_, ?_, trivial⟩ <;> field_simp
  have hcz : (PairInput.ofPoints p q).cz = if p.z.beq Fp.one then Fp.one else p.z * p.z * p.z := by
    unfold PairInput.ofPoints; split <;> rfl
  have hcx : (PairInput.ofPoints p q).cx = if p.z.beq Fp.one then p.x else p.x * p.z := by
    unfold PairInput.ofPoints; split <;> rfl
  have hcy : (PairInput.ofPoints p q).cy = p.y := by
    unfold PairInput.ofPoints; split <;> rfl
  have hpa : (PairInput.ofPoints p q).pAffine = p.z.beq Fp.one := by
    unfold PairInput.ofPoints
    split <;> rename_i h
    · exact h.symm
    · exact (Bool.eq_false_iff.mpr h).symm
  refine ⟨hrel, by rw [hr]; exact hqz, ?_, ?_, ?_, ?_⟩
  · rw [hcz]
    split
    · rw [Fp.one_def]; exact one_ne_zero
    · exact mul_ne_zero (mul_ne_zero hpz hpz) hpz
  · rw [hcx, hcz]
    split
    · rename_i h1
      have h1' : p.z = 1 := by rw [← Fp.one_def]; exact Fp.beq_iff.mp h1
      rw [h1', Fp.one_def]; simp
    · field_simp
  · rw [hcy, hcz]
    split
    · rename_i h1
      have h1' : p.z = 1 := by rw [← Fp.one_def]; exact Fp.beq_iff.mp h1
      rw [h1', Fp.one_def]; simp
    · field_simp
  · intro ha
    rw [hcz, if_pos (by rw [← hpa]; exact ha), Fp.one_def]

/-! ## Assembly -/

/-- `pq` contributes to the pairing product: neither point is at infinity. -/
def pairCounts (pq : G1 × G2) : Bool := !(pq.1.isInfinity || pq.2.isInfinity)

/-- One pair's Miller loop in the spec. -/
def pairMiller (pq : G1 × G2) : Fp12 :=
  EthLib.Cryptography.Bls.millerLoop blsX pq.2.toAffine pq.1.toAffine

/-- The spec's factors are the conjugated Miller values of the counted pairs. -/
theorem filterMap_pairFactor (l : List (G1 × G2)) :
    l.filterMap pairFactor = (l.filter pairCounts).map fun pq => (pairMiller pq).conjugate := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    unfold pairFactor pairCounts pairMiller
    cases (pq.1.isInfinity || pq.2.isInfinity) <;> rfl

/-- The mirror's input list is the counted pairs, mapped. -/
theorem filterMap_ofPoints (l : List (G1 × G2)) :
    l.filterMap (fun (pq : G1 × G2) => if pq.1.isInfinity || pq.2.isInfinity then none
      else some (PairInput.ofPoints pq.1 pq.2))
      = (l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2 := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    unfold pairCounts
    cases (pq.1.isInfinity || pq.2.isInfinity) <;> rfl

/-- The spec's starting state for one pair. -/
def initState (pq : G1 × G2) : SpecState :=
  ⟨pq.2.toAffine.1, pq.2.toAffine.2, pq.1.toAffine.1, pq.1.toAffine.2,
    ⟨pq.2.toAffine.1, pq.2.toAffine.2, Fp2.one⟩, 1⟩

/-- The mirror's starting entry stands for the spec's starting state. -/
theorem rel_init {pq : G1 × G2} (h : pairCounts pq = true) :
    Rel (PairInput.ofPoints pq.1 pq.2, (PairInput.ofPoints pq.1 pq.2).r) (initState pq) := by
  unfold pairCounts at h
  rw [Bool.not_eq_true', Bool.or_eq_false_iff] at h
  have hin := inputRel_ofPoints (p := pq.1) (q := pq.2) (by simp [h.1]) (by simp [h.2])
  exact ⟨hin, _, hin.rz_ne, hin.r_eq⟩

private theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: _, h => List.Forall₂.cons (h x (List.mem_cons_self ..))
      (forall₂_map fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem run_initState (pq : G1 × G2) : (initState pq).run blsX.log2 = pairMiller pq := by
  show EthLib.Cryptography.Bls.millerSteps _ _ _ _ _ _ _ _ = _
  rw [pairMiller, EthLib.Cryptography.Bls.millerLoop, Fp12.one_def]
  rfl

/-- The mirror's Miller loop is the product of the spec's, up to a killed factor. -/
theorem millerLoop_rel (l : List (G1 × G2)) :
    ∃ k, Killed k ∧ millerLoop ((l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2)
      = ((l.filter pairCounts).map pairMiller).prod * k := by
  have hrel : List.Forall₂ Rel
      (((l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2).map fun pi => (pi, pi.r))
      ((l.filter pairCounts).map initState) := by
    rw [List.map_map]
    exact forall₂_map fun pq hpq => rel_init (List.of_mem_filter hpq)
  obtain ⟨k, hk, h⟩ := millerSteps_rel blsX.log2 _ _ hrel 1 1 killed_one (by
    rw [List.map_map, mul_one]
    exact (List.prod_eq_one fun x hx => by
      obtain ⟨pq, _, rfl⟩ := List.mem_map.mp hx
      rfl).symm)
  refine ⟨k, hk, ?_⟩
  have e : ((l.filter pairCounts).map initState).map (SpecState.run blsX.log2)
      = (l.filter pairCounts).map pairMiller := by
    rw [List.map_map]
    exact List.map_congr_left fun pq _ => run_initState pq
  rw [millerLoop, Fp12.one_def, h, e]

/-- Conjugation commutes with list products. -/
theorem conjugate_list_prod (l : List Fp12) :
    l.prod.conjugate = (l.map Fp12.conjugate).prod := by
  induction l with
  | nil => show (1 : Fp12).conjugate = 1; rw [Fp12.conjugate_eq_pow, one_pow]
  | cons a l ih => rw [List.prod_cons, Fp12.conjugate_mul, ih, List.map_cons, List.prod_cons]

theorem pow_card12 (a : Fp12) : a ^ (Fp.modulus ^ 12) = a := by
  rw [show Fp.modulus ^ 12 = Fp.modulus ^ 6 * Fp.modulus ^ 6 by ring, pow_mul,
    ← Fp12.conjugate_eq_pow, ← Fp12.conjugate_eq_pow, Fp12.conjugate_conjugate]

/-- The cube of a final-exponentiation value is one exactly when the value is (it
lies in the `r`-th roots of unity, and `3` is prime to `r`). -/
theorem isOne_cube (f : Fp12) :
    ((finalExponentiation f) ^ 3).isOne = (finalExponentiation f).isOne := by
  rw [Bool.eq_iff_iff, Fp12.isOne_iff, Fp12.isOne_iff]
  refine ⟨fun h3 => ?_, fun h1 => by rw [h1, one_pow]⟩
  by_cases hf : f = 0
  · subst hf
    rw [finalExponentiation_eq_pow, zero_pow (by decide), zero_pow (by decide)] at h3
    exact absurd h3 zero_ne_one
  have hy : (finalExponentiation f) ^ Fr.modulus = 1 := by
    rw [finalExponentiation_eq_pow, ← pow_mul,
      show finalExpExponent * Fr.modulus = Fp.modulus ^ 12 - 1 by decide,
      pow_sub₀ f hf (Nat.one_le_pow _ _ Fp.modulus_pos), pow_one, pow_card12,
      mul_inv_cancel₀ hf]
  obtain ⟨a, b, hab⟩ : ∃ a b : Nat, a * Fr.modulus = 3 * b + 1 := by
    exact ⟨1, Fr.modulus / 3, by decide⟩
  generalize finalExponentiation f = y at hy h3
  generalize Fr.modulus = n at hy hab
  have h1 : y ^ (a * n) = 1 := by rw [mul_comm, pow_mul, hy, one_pow]
  rw [hab, pow_succ, pow_mul, h3, one_pow, one_mul] at h1
  exact h1

/-- The implementation's pairing check (mirrored over spec types) returns the
spec's `pairingCheck` on every input. -/
theorem pairingCheck_eq (pairs : Array (G1 × G2)) :
    Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs := by
  rw [pairingCheck_eq_finalExp_prod, filterMap_pairFactor, Fp12.one_def, ← List.prod_eq_foldl]
  unfold Mirror.pairingCheck
  rw [filterMap_ofPoints]
  obtain ⟨k, hk, h⟩ := millerLoop_rel pairs.toList
  dsimp only
  rw [h, finalExpCube_eq, isOne_cube]
  apply congrArg Fp12.isOne
  rw [finalExponentiation_eq_pow, finalExponentiation_eq_pow, Fp12.conjugate_mul,
    conjugate_list_prod, List.map_map, mul_pow]
  have hk' : k.conjugate ^ finalExpExponent = 1 := by
    rw [Fp12.conjugate_eq_pow, ← pow_mul, mul_comm, pow_mul, hk, one_pow]
  rw [hk', mul_one, Function.comp_def]

end EthLibImpl.Cryptography.Bls.Mirror
