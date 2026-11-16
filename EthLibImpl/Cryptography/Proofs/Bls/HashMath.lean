import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.G2Proj
import EthLibImpl.Cryptography.Proofs.Bls.G2Psi
import EthLibImpl.Cryptography.Proofs.Bls.SwuMath
import EthLib.Cryptography.Proofs.Bls.Isogeny

/-!
# The implementation's hash-to-curve is the spec's, up to Jacobian scaling

Proves that `Mirror.HashToCurve.hashToG2` (the implementation's algorithm over spec
types) returns the same point as the spec's `HashToCurve.hashToG2`: both fail with the same
error, or both succeed and the results are `G2.ProjEq`.

* The batched SSWU inversion is the spec's two inversions (`batchInverse2_eq`).
* The implementation's SSWU, which reuses `gx1`'s failed square-root candidate for `gx2`,
  returns the spec's `simpleSwu` result (`simpleSwuWith_eq`). The spec's map never fails
  (`HashToCurve.simpleSwu_sqrt_complete`), so the implementation's unreachable panic is
  never taken.
* The isogeny, `ψ` and `ψ²` stay Jacobian, so each is proved `ProjEq` to the spec's affine
  version: `isoMapJac_proj` on the points of `E'` that SSWU returns (the spec's isogeny
  returns the identity at its pole, which no point of `E'` reaches,
  `HashToCurve.isoMapG2_curve_eq`), and `psi_proj`, `psi2_proj`. `clearCofactor_proj`
  combines them with the `ProjEq` laws of `G2Proj`.

Kernel notes. A defeq check between two applications of one matcher unfolds the matcher and
evaluates its discriminant: matchers are `abbrev`s, so their arguments are not compared first.
The spec's `simpleSwu` matches on `Fp2.sqrt` of a symbolic expression, and the mirror's
`hashToG2` on `simpleSwuWith`'s result; evaluating either runs through the Montgomery limbs
until the kernel reports deep recursion. The spec's equation lemma `simpleSwu.eq_1` carries
`save_info` metadata around `x1`, so a term rebuilt from `swuGx (swuX1 u)` is only defeq to its
discriminant, and rewriting with it triggers that check. Generalizing `Fp2.sqrt` or
`simpleSwuWith` with `generalize` does not help, since the kernel checks the instantiated terms.
So:

* `simpleSwu_ok`, `simpleSwu_ok2` split on the spec's own discriminant (`cases hq : Fp2.sqrt _`)
  and reach the second branch through the matcher's equation `simpleSwu.match_1.eq_2`;
* the mirror's `hashToG2` is `hashToG2With simpleSwuWith` by `rfl`, and `hashToG2With_ok` reduces
  the matches with the SSWU still a variable.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.HashToCurve

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.HashToCurve
open scoped EthLib.Cryptography.Bls.Fp2

open EthLib.Cryptography.Bls.HashToCurve (sgn0Fp2 Z Aprime Bprime k10 k11 k12 k13 k20 k21 k30 k31
  k32 k33 k40 k41 k42 c1Psi2 mulNegX simpleSwu isoMapG2 psi2 swuG simpleSwu_sqrt_complete
  simpleSwu_curve_eq isoMapG2_curve_eq swuG_x2_eq)
open EthLib.Cryptography.Bls.G2 (c1Psi c2Psi psi frobeniusFp2)

theorem fp2_isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := Fp2.isZero_iff

/-- `if x.isZero then 1 else x` is nonzero. -/
theorem sel_ne_zero (x : Fp2) : (if x.isZero then Fp2.one else x) ≠ 0 := by
  by_cases h : x.isZero = true
  · rw [if_pos h, Fp2.one_eq_one]; exact one_ne_zero
  · rw [if_neg h]; exact fun h0 => h (fp2_isZero_iff.mpr h0)

theorem sel_inv (x : Fp2) (hx : x ≠ 0) : (if x.isZero then Fp2.one else x) = x := by
  rw [if_neg (fun h => hx (fp2_isZero_iff.mp h))]

/-- Batched inversion of two values equals two inversions. -/
theorem batchInverse2_eq (a b : Fp2) : batchInverse2 a b = (a.inverse, b.inverse) := by
  unfold batchInverse2
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha hb; simp [fp2_isZero_iff]
  · subst ha
    simp [fp2_isZero_iff, hb, Fp2.inverse_eq_inv]
  · subst hb
    simp [fp2_isZero_iff, ha, Fp2.inverse_eq_inv]
  · simp only [fp2_isZero_iff, ha, hb, if_false, Fp2.inverse_eq_inv]
    simp only [Prod.mk.injEq]
    constructor <;> field_simp


/-- Batched inversion of four values equals four inversions. -/
theorem batchInverse4_eq (a b c d : Fp2) :
    batchInverse4 a b c d = (a.inverse, b.inverse, c.inverse, d.inverse) := by
  unfold batchInverse4
  simp only [Fp2.inverse_eq_inv]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> by_cases hd : d = 0 <;>
    simp [fp2_isZero_iff, ha, hb, hc, hd, Prod.ext_iff] <;> (field_simp <;> simp)


theorem panicWPD_eq {α : Type} [Inhabited α] (a b : String) (c d : Nat) (e : String) :
    panicWithPosWithDecl a b c d e = (default : α) := rfl

/-! ## SSWU

`simpleSwuWith` first decides on `gx1`'s norm and, when `gx1` is not a square, reuses the
failed candidate for `gx2`. To compare it with the spec, its body after `x1` is `swuTail`, and
the spec's `simpleSwu` is described by `simpleSwu_ok` and `simpleSwu_ok2` (its two successful
outcomes; `sqrt_x1_or_x2` rules out the third, where both square roots fail). -/

/-- `simpleSwuWith`'s body once `x1` is known. -/
def swuTail (u zu2 denom x1 : Fp2) : Fp2 × Fp2 :=
  let gx1 := x1 * x1 * x1 + Aprime * x1 + Bprime
  if gx1.c1.isZero || denom.isZero then
    simpleSwuSlow u zu2 x1 gx1
  else
    let n1 := gx1.c0 * gx1.c0 + gx1.c1 * gx1.c1
    let c := Fp.powNat n1 ((Fp.modulus + 1) / 4)
    if (c * c).beq n1 then
      let y := sqrtGivenNorm gx1 c
      let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
      (x1, y)
    else
      let x2 := zu2 * x1
      let gx2 := x2 * x2 * x2 + Aprime * x2 + Bprime
      if gx2.c1.isZero then
        simpleSwuSlow u zu2 x1 gx1
      else
        let nu := u.c0 * u.c0 + u.c1 * u.c1
        let y := sqrtGivenNorm gx2 (s125 * (nu * nu * nu) * c)
        let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
        (x2, y)

theorem simpleSwuWith_eq_tail (u zu2 denom di : Fp2) :
    simpleSwuWith u zu2 denom di =
      swuTail u zu2 denom (if denom.isZero then x1Exceptional else negBOverA * (Fp2.one + di)) :=
  rfl

/-- The spec's `Z·u²`. -/
def swuZu (u : Fp2) : Fp2 := Z * (u * u)
/-- The spec's `denom`. -/
def swuDen (u : Fp2) : Fp2 := swuZu u * swuZu u + swuZu u
/-- The spec's `x1`. -/
def swuX1 (u : Fp2) : Fp2 :=
  if (swuDen u).isZero then Bprime / (Z * Aprime)
  else -Bprime / Aprime * (Fp2.one + (swuDen u).inverse)
/-- The curve polynomial `x³ + A'x + B'`. -/
def swuGx (x : Fp2) : Fp2 := x * x * x + Aprime * x + Bprime

theorem tail_x1 (u : Fp2) :
    swuTail u (swuDenom u).1 (swuDenom u).2 (if (swuDenom u).2.isZero then x1Exceptional
      else negBOverA * (Fp2.one + (swuDenom u).2.inverse)) =
    swuTail u (swuZu u) (swuDen u) (swuX1 u) := rfl

/-- One of `g(x1)` and `g(Z·u²·x1)` is a square, so the spec's `simpleSwu` never fails. -/
theorem sqrt_x1_or_x2 (u : Fp2) :
    (∃ y, Fp2.sqrt (swuGx (swuX1 u)) = .ok y) ∨
      (∃ y, Fp2.sqrt (swuGx (swuZu u * swuX1 u)) = .ok y) :=
  simpleSwu_sqrt_complete u

/-- The spec's `simpleSwu` when `gx1` has a square root.

The case split is on the spec's own discriminant (`cases hq : Fp2.sqrt _`), never on
`Fp2.sqrt (swuGx (swuX1 u))`: that term is only defeq to it (see the module note). -/
theorem simpleSwu_ok {u y : Fp2} (h : Fp2.sqrt (swuGx (swuX1 u)) = .ok y) :
    simpleSwu u = .ok (swuX1 u, if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  rw [simpleSwu]
  cases hq : Fp2.sqrt (F := Fp) _ with
  | ok y' =>
    obtain rfl : y' = y := Except.ok.inj (hq.symm.trans h)
    rfl
  | error e => exact absurd (hq.symm.trans h) (by simp)

-- The matcher is named on purpose: its equation selects the branch without evaluation.
set_option linter.auxLemma false in
/-- The spec's `simpleSwu` when `gx1` has none and `gx2` has a square root. -/
theorem simpleSwu_ok2 {u y : Fp2} {e : BlsError} (h1 : Fp2.sqrt (swuGx (swuX1 u)) = .error e)
    (h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) = .ok y) :
    simpleSwu u = .ok (swuZu u * swuX1 u, if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  rw [simpleSwu]
  cases hq : Fp2.sqrt (F := Fp) _ with
  | ok y' => exact absurd (hq.symm.trans h1) (by simp)
  | error e' =>
    simp (config := { zeta := false, iota := false, beta := false }) only
      [simpleSwu.match_1.eq_2]
    extract_lets x2
    cases hq2 : Fp2.sqrt (F := Fp) _ with
    | ok y' =>
      obtain rfl : y' = y := Except.ok.inj (hq2.symm.trans h2)
      rfl
    | error e2 => exact absurd (hq2.symm.trans h2) (by simp)

theorem simpleSwuSlow_ok {u zu2 x1 g1 z : Fp2} (h : Fp2.sqrtAlt g1 = .ok z) :
    simpleSwuSlow u zu2 x1 g1 = (x1, if sgn0Fp2 u = sgn0Fp2 z then z else -z) := by
  rw [simpleSwuSlow, h]

-- The matcher is named on purpose: its equation selects the branch without evaluation.
set_option linter.auxLemma false in
theorem simpleSwuSlow_ok2 {u zu2 x1 g1 z : Fp2} {e : BlsError} (h1 : Fp2.sqrtAlt g1 = .error e)
    (h2 : Fp2.sqrtAlt (swuGx (zu2 * x1)) = .ok z) :
    simpleSwuSlow u zu2 x1 g1 =
      (zu2 * x1, if sgn0Fp2 u = sgn0Fp2 z then z else -z) := by
  rw [simpleSwuSlow, h1]
  simp (config := { zeta := false, iota := false, beta := false }) only
    [simpleSwuSlow.match_1.eq_2]
  extract_lets x2 gx2
  cases hq : Fp2.sqrtAlt gx2 with
  | ok z' =>
    obtain rfl : z' = z := Except.ok.inj (hq.symm.trans h2)
    rfl
  | error e' => exact absurd (hq.symm.trans h2) (by simp)

-- The matcher is named on purpose: its equation selects the branch without evaluation.
set_option linter.auxLemma false in
theorem simpleSwuSlow_panic {u zu2 x1 g1 : Fp2} {e1 e2 : BlsError}
    (h1 : Fp2.sqrtAlt g1 = .error e1) (h2 : Fp2.sqrtAlt (swuGx (zu2 * x1)) = .error e2) :
    simpleSwuSlow u zu2 x1 g1 = default := by
  rw [simpleSwuSlow, h1]
  simp (config := { zeta := false, iota := false, beta := false }) only
    [simpleSwuSlow.match_1.eq_2]
  extract_lets x2 gx2
  cases hq : Fp2.sqrtAlt gx2 with
  | ok z' => exact absurd (hq.symm.trans h2) (by simp)
  | error e' => rfl

/-- The slow path of the implementation returns the spec's `simpleSwu` result. -/
theorem simpleSwuSlow_eq (u : Fp2) :
    simpleSwu u = .ok (simpleSwuSlow u (swuZu u) (swuX1 u) (swuGx (swuX1 u))) := by
  have hi1 := Fp2.sqrtAlt_isOk (swuGx (swuX1 u))
  have hi2 := Fp2.sqrtAlt_isOk (swuGx (swuZu u * swuX1 u))
  cases h1' : Fp2.sqrtAlt (swuGx (swuX1 u)) with
  | ok z =>
    rw [h1'] at hi1
    cases h1 : Fp2.sqrt (swuGx (swuX1 u)) with
    | ok y =>
      rw [simpleSwuSlow_ok h1', simpleSwu_ok h1,
        Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h1') (Fp2.sqrt_ok h1) u]
    | error e => rw [h1] at hi1; simp [Except.isOk, Except.toBool] at hi1
  | error e' =>
    rw [h1'] at hi1
    cases h1 : Fp2.sqrt (swuGx (swuX1 u)) with
    | ok y => rw [h1] at hi1; simp [Except.isOk, Except.toBool] at hi1
    | error e =>
      cases h2' : Fp2.sqrtAlt (swuGx (swuZu u * swuX1 u)) with
      | ok z =>
        rw [h2'] at hi2
        cases h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) with
        | ok y =>
          rw [simpleSwuSlow_ok2 h1' h2', simpleSwu_ok2 h1 h2,
            Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h2') (Fp2.sqrt_ok h2) u]
        | error e2 => rw [h2] at hi2; simp [Except.isOk, Except.toBool] at hi2
      | error e2' =>
        exfalso
        rcases sqrt_x1_or_x2 u with ⟨y, hy⟩ | ⟨y, hy⟩
        · rw [h1] at hy; cases hy
        · rw [h2', hy] at hi2; cases hi2

theorem swuTail_slow {u zu2 denom x1 : Fp2}
    (h : ((swuGx x1).c1.isZero || denom.isZero) = true) :
    swuTail u zu2 denom x1 = simpleSwuSlow u zu2 x1 (swuGx x1) := by
  unfold swuGx at h ⊢
  unfold swuTail
  dsimp only
  rw [if_pos h]

theorem swuTail_fast1 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : (c * c).beq n1 = true) :
    swuTail u zu2 denom x1 = (x1, if sgn0Fp2 u = sgn0Fp2 (sqrtGivenNorm (swuGx x1) c)
      then sqrtGivenNorm (swuGx x1) c else -sqrtGivenNorm (swuGx x1) c) := by
  subst hn hc
  unfold swuGx at h hb ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_pos hb]

theorem swuTail_slow2 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : ¬ (c * c).beq n1 = true) (h2 : (swuGx (zu2 * x1)).c1.isZero = true) :
    swuTail u zu2 denom x1 = simpleSwuSlow u zu2 x1 (swuGx x1) := by
  subst hn hc
  unfold swuGx at h hb h2 ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_neg hb, if_pos h2]

theorem swuTail_fast2 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : ¬ (c * c).beq n1 = true) (h2 : ¬ (swuGx (zu2 * x1)).c1.isZero = true) :
    swuTail u zu2 denom x1 = (zu2 * x1,
      let y := sqrtGivenNorm (swuGx (zu2 * x1))
        (s125 * ((u.c0 * u.c0 + u.c1 * u.c1) * (u.c0 * u.c0 + u.c1 * u.c1) *
          (u.c0 * u.c0 + u.c1 * u.c1)) * c)
      if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  subst hn hc
  unfold swuGx at h hb h2 ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_neg hb, if_neg h2]

theorem fp2_isZero_iff' {a : Fp2} : a.isZero = true ↔ a = 0 := fp2_isZero_iff

theorem Aprime_ne_zero : Aprime ≠ (0 : Fp2) := by
  decide_eq_at_model [Aprime]

/-- The SSWU identity at the spec's `x1`: `g(Z·u²·x1) = (Z·u²)³·g(x1)`. -/
theorem swuGx_zu2 {u : Fp2} (hd : ¬ (swuDen u).isZero = true) :
    swuGx (swuZu u * swuX1 u) = swuZu u * swuZu u * swuZu u * swuGx (swuX1 u) :=
  swuG_x2_eq u (Bool.eq_false_iff.mpr hd)

/-- The implementation's SSWU (shared square-root candidate) returns the spec's result. -/
theorem simpleSwuWith_eq (u : Fp2) :
    simpleSwu u = .ok (simpleSwuWith u (swuDenom u).1 (swuDenom u).2 (swuDenom u).2.inverse) := by
  rw [simpleSwuWith_eq_tail, tail_x1]
  by_cases hs : ((swuGx (swuX1 u)).c1.isZero || (swuDen u).isZero) = true
  · rw [swuTail_slow hs]
    exact simpleSwuSlow_eq u
  · have hd : ¬ (swuDen u).isZero = true := fun h => hs (by rw [h, Bool.or_true])
    have hg1 : ¬ (swuGx (swuX1 u)).c1.isZero = true := fun h => hs (by rw [h, Bool.true_or])
    by_cases hb : (Fp.powNat ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) ((Fp.modulus + 1) / 4) *
        Fp.powNat ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) ((Fp.modulus + 1) / 4)).beq
        ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) = true
    · -- `gx1` is a square: its root comes from the candidate
      rw [swuTail_fast1 rfl rfl hs hb]
      have hcc := Fp.beq_iff.mp hb
      have hroot := sqrtGivenNorm_sq hg1 hcc
      cases hq : Fp2.sqrt (swuGx (swuX1 u)) with
      | ok y =>
        rw [simpleSwu_ok hq, Fp2.sgn0Fp2_normalize hroot (Fp2.sqrt_ok hq) u]
      | error e =>
        have := Fp2.sqrt_isOk_iff.mpr ⟨_, hroot⟩
        rw [hq] at this
        simp [Except.isOk, Except.toBool] at this
    · obtain ⟨hcc, hns⟩ := euler_cand hb
      by_cases h2 : (swuGx (swuZu u * swuX1 u)).c1.isZero = true
      · rw [swuTail_slow2 rfl rfl hs hb h2]
        exact simpleSwuSlow_eq u
      · rw [swuTail_fast2 rfl rfl hs hb h2]
        cases hq : Fp2.sqrt (swuGx (swuX1 u)) with
        | ok y =>
          exfalso
          apply hns
          refine ⟨y.c0 * y.c0 + y.c1 * y.c1, ?_⟩
          have := norm_mul y y
          rw [Fp2.sqrt_ok hq] at this
          exact this.symm
        | error e =>
          have e2 := swuGx_zu2 hd
          have hs' := norm_gx2 u (swuGx (swuX1 u)) _ hcc
          have hroot := sqrtGivenNorm_sq h2 (by rw [e2]; exact hs')
          cases hq2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) with
          | ok y =>
            rw [simpleSwu_ok2 hq hq2]
            dsimp only
            rw [Fp2.sgn0Fp2_normalize hroot (Fp2.sqrt_ok hq2) u]
          | error e2 =>
            have := Fp2.sqrt_isOk_iff.mpr ⟨_, hroot⟩
            rw [hq2] at this
            simp [Except.isOk, Except.toBool] at this

open EthLibImpl.Cryptography.Bls.Mirror.G2 (conj)

theorem conjugate_eq (a : Fp2) : a.conjugate = conj a := rfl

theorem frobeniusFp2_eq (a : Fp2) : frobeniusFp2 a = conj a := rfl

theorem conj_ne_zero {a : Fp2} (h : a ≠ 0) : conj a ≠ 0 :=
  fun h0 => h ((map_eq_zero conj).mp h0)

/-- `ψ` on the spec's triples equals `ψ` on its scaled Jacobian form. -/
theorem psi_proj (P : G2) : G2.ProjEq (psi P) (psiJac P) := by
  unfold psi psiJac
  by_cases h : P.z.isZero = true
  · have hz : P.z = 0 := G2.fp2_isZero_iff.mp h
    rw [if_pos h]
    refine Or.inl ⟨hz, ?_⟩
    show P.z.conjugate = 0
    rw [conjugate_eq, hz, _root_.map_zero]
  · have hz : P.z ≠ 0 := fun h0 => h (G2.fp2_isZero_iff.mpr h0)
    rw [if_neg h]
    unfold G2.toAffine
    rw [if_neg h]
    dsimp only
    refine Or.inr ⟨conj P.z, conj_ne_zero hz, ?_⟩
    have hc := conj_ne_zero hz
    apply G2.ext' <;> dsimp only
    all_goals simp only [conjugate_eq, frobeniusFp2_eq, Fp2.inverse_eq_inv, _root_.map_mul,
      map_inv₀]
    · field_simp
    · field_simp
    · rw [Fp2.one_def, mul_one]

/-- `ψ²` on the spec's triples equals `ψ²` on its scaled Jacobian form. -/
theorem psi2_proj (P : G2) : G2.ProjEq (psi2 P) (psi2Jac P) := by
  unfold psi2 psi2Jac
  by_cases h : P.z.isZero = true
  · have hz : P.z = 0 := G2.fp2_isZero_iff.mp h
    rw [if_pos h]
    exact Or.inl ⟨hz, hz⟩
  · have hz : P.z ≠ 0 := fun h0 => h (G2.fp2_isZero_iff.mpr h0)
    rw [if_neg h]
    unfold G2.toAffine
    rw [if_neg h]
    dsimp only
    refine Or.inr ⟨P.z, hz, ?_⟩
    simp only [Fp2.inverse_eq_inv]
    apply G2.ext' <;> dsimp only
    · field_simp
    · field_simp
    · rw [Fp2.one_def, mul_one]

/-- The spec's `ψ` reads a point only through `ProjEq`. -/
theorem psi_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (psi P) (psi Q) := by
  unfold psi
  by_cases hz : P.z.isZero = true
  · have hq : Q.z.isZero = true :=
      G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mp (G2.fp2_isZero_iff.mp hz))
    rw [if_pos hz, if_pos hq]
    exact h
  · have hq : ¬ Q.z.isZero = true := fun hq =>
      hz (G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mpr (G2.fp2_isZero_iff.mp hq)))
    rw [if_neg hz, if_neg hq, G2.ProjEq.toAffine_eq h]
    exact G2.ProjEq.refl _

theorem psi2_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (psi2 P) (psi2 Q) := by
  unfold psi2
  by_cases hz : P.z.isZero = true
  · have hq : Q.z.isZero = true :=
      G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mp (G2.fp2_isZero_iff.mp hz))
    rw [if_pos hz, if_pos hq]
    exact h
  · have hq : ¬ Q.z.isZero = true := fun hq =>
      hz (G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mpr (G2.fp2_isZero_iff.mp hq)))
    rw [if_neg hz, if_neg hq, G2.ProjEq.toAffine_eq h]
    exact G2.ProjEq.refl _

theorem mulNegX_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (mulNegX P) (mulNegX Q) :=
  G2.ProjEq.neg (G2.ProjEq.mulNat _ h)

/-- The spec's cofactor clearing and the Jacobian one return the same point. -/
theorem clearCofactor_proj {P Q : G2} (h : G2.ProjEq P Q) :
    G2.ProjEq (EthLib.Cryptography.Bls.HashToCurve.clearCofactor P) (clearCofactorJac Q) := by
  unfold clearCofactorJac EthLib.Cryptography.Bls.HashToCurve.clearCofactor
  dsimp only
  have t1 := mulNegX_congr h
  have t2 := G2.ProjEq.trans (psi_congr h) (psi_proj Q)
  have t3 := G2.ProjEq.trans (psi2_congr (G2.ProjEq.double h)) (psi2_proj (G2.double Q))
  have t4 := G2.ProjEq.add t3 (G2.ProjEq.neg t2)
  have t5 := G2.ProjEq.add t1 t2
  have t6 := mulNegX_congr t5
  have t7 := G2.ProjEq.add t4 t6
  have t8 := G2.ProjEq.add t7 (G2.ProjEq.neg t1)
  exact G2.ProjEq.add t8 (G2.ProjEq.neg h)

/-- The isogeny's affine point against its Jacobian form, off the pole. -/
theorem iso_core_ne {xNum xDen yNum yDen yp : Fp2} (hx : xDen ≠ 0) (hy : yDen ≠ 0) :
    G2.ProjEq ⟨xNum / xDen, yp * yNum / yDen, Fp2.one⟩
      ⟨xNum * (xDen * yDen * yDen), yp * yNum * (xDen * yDen * yDen * (xDen * xDen)),
        xDen * yDen⟩ := by
  refine Or.inr ⟨xDen * yDen, mul_ne_zero hx hy, ?_⟩
  simp only [Fp2.div_eq_mul_inv']
  apply G2.ext' <;> dsimp only
  · field_simp
  · field_simp
  · rw [Fp2.one_def, mul_one]

/-- The isogeny with the inverses spelled out, against its Jacobian form. -/
theorem iso_core (xNum xDen yNum yDen yp : Fp2) :
    G2.ProjEq ⟨xNum / xDen, yp * yNum / yDen, Fp2.one⟩
      (if xDen.isZero || yDen.isZero then
        ⟨xNum * xDen.inverse, yp * yNum * yDen.inverse, Fp2.one⟩
      else
        ⟨xNum * (xDen * yDen * yDen), yp * yNum * (xDen * yDen * yDen * (xDen * xDen)),
          xDen * yDen⟩) := by
  by_cases h : (xDen.isZero || yDen.isZero) = true
  · rw [if_pos h]
    exact G2.ProjEq.refl _
  · rw [if_neg h]
    simp only [Bool.or_eq_true, not_or, fp2_isZero_iff] at h
    exact iso_core_ne h.1 h.2

/-- On a point of `E'`, the spec's isogeny and its Jacobian form give the same point: the
denominators never vanish there (`HashToCurve.isoMapG2_curve_eq`), so the spec's isogeny does
not return the identity. -/
theorem isoMapJac_proj {xp yp : Fp2} (h : yp * yp = swuG xp) :
    G2.ProjEq (isoMapG2 xp yp) (isoMapJac xp yp) := by
  obtain ⟨a, b, he, -⟩ := isoMapG2_curve_eq h
  unfold isoMapG2 at he ⊢
  unfold isoMapJac isoParts
  dsimp only at he ⊢
  revert he
  split
  · intro he
    have hz : (Fp2.zero : Fp2) = Fp2.one := congrArg G2.z he
    rw [Fp2.zero_eq_zero, Fp2.one_eq_one] at hz
    exact absurd hz zero_ne_one
  · rename_i hc
    intro _
    simp only [Bool.or_eq_true, not_or, fp2_isZero_iff] at hc
    exact iso_core_ne hc.1 hc.2

/-- `ok a >>= f` is `f a`. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → Except BlsError β) :
    (Except.ok a >>= f) = f a := rfl

/-- The spec's `hashToG2`, once both SSWU outputs are known. -/
theorem spec_hashToG2_ok {msg dst : ByteArray} {us : Vector Fp2 2} {p0 p1 : Fp2 × Fp2}
    (hu : hashToFieldFp2 msg dst 2 = .ok us) (h0 : simpleSwu us[0] = .ok p0)
    (h1 : simpleSwu us[1] = .ok p1) :
    EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst =
      .ok (EthLib.Cryptography.Bls.HashToCurve.clearCofactor
        (G2.add (isoMapG2 p0.1 p0.2) (isoMapG2 p1.1 p1.2))) := by
  rw [EthLib.Cryptography.Bls.HashToCurve.hashToG2, hu, ok_bind, h0, ok_bind, h1]
  obtain ⟨x0, y0⟩ := p0
  obtain ⟨x1, y1⟩ := p1
  rfl

-- The matcher is named on purpose: it makes `hashToG2_eq_with` hold by `rfl`.
set_option linter.auxLemma false in
/-- The mirror's `hashToG2` with its SSWU as a parameter, built from the mirror's own matcher, so
that `hashToG2 = hashToG2With simpleSwuWith` holds by `rfl`. With the SSWU a variable, the
kernel can reduce the matches on its result without evaluating it. -/
def hashToG2With (sw : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2) (msg dst : ByteArray) :
    Except BlsError G2 :=
  bind (hashToFieldFp2 msg dst 2) fun us =>
    have u0 : Fp2 := us[0]!
    have u1 : Fp2 := us[1]!
    hashToG2.match_1 (fun _ => Except BlsError G2) (swuDenom u0) fun zu0 den0 =>
    hashToG2.match_1 (fun _ => Except BlsError G2) (swuDenom u1) fun zu1 den1 =>
    hashToG2.match_1 (fun _ => Except BlsError G2) (batchInverse2 den0 den1) fun di0 di1 =>
    hashToG2.match_1 (fun _ => Except BlsError G2) (sw u0 zu0 den0 di0) fun x0 y0 =>
    hashToG2.match_1 (fun _ => Except BlsError G2) (sw u1 zu1 den1 di1) fun x1 y1 =>
    pure (clearCofactorJac (G2.add (isoMapJac x0 y0) (isoMapJac x1 y1)))

theorem hashToG2_eq_with : hashToG2 = hashToG2With simpleSwuWith := rfl

/-- `hashToG2With`, with its two SSWU calls written out. -/
theorem hashToG2With_ok (sw : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2) {msg dst : ByteArray}
    {us : Vector Fp2 2} (hu : hashToFieldFp2 msg dst 2 = .ok us) :
    hashToG2With sw msg dst = .ok (clearCofactorJac (G2.add
      (isoMapJac (sw us[0] (swuDenom us[0]).1 (swuDenom us[0]).2 (swuDenom us[0]).2.inverse).1
        (sw us[0] (swuDenom us[0]).1 (swuDenom us[0]).2 (swuDenom us[0]).2.inverse).2)
      (isoMapJac (sw us[1] (swuDenom us[1]).1 (swuDenom us[1]).2 (swuDenom us[1]).2.inverse).1
        (sw us[1] (swuDenom us[1]).1 (swuDenom us[1]).2 (swuDenom us[1]).2.inverse).2))) := by
  have e0 : us[0]! = us[0] := getElem!_pos us 0 (by decide)
  have e1 : us[1]! = us[1] := getElem!_pos us 1 (by decide)
  unfold hashToG2With
  rw [hu, ok_bind, e0, e1]
  simp only [batchInverse2_eq]
  rfl

/-- Main result: the implementation's hash-to-G2 and the spec's both fail with the same error,
or both succeed with triples for the same point (`G2.ProjEq`: equal up to Jacobian scaling). -/
theorem hashToG2_rel (msg dst : ByteArray) :
    (∃ e, EthLib.Cryptography.Bls.HashToCurve.hashToG2 (F := Fp) msg dst = .error e ∧
        hashToG2 msg dst = .error e) ∨
      ∃ P Q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst = .ok P ∧
        hashToG2 msg dst = .ok Q ∧ G2.ProjEq P Q := by
  cases hu : hashToFieldFp2 (F := Fp) msg dst 2 with
  | error e =>
    refine Or.inl ⟨e, ?_, ?_⟩
    · rw [EthLib.Cryptography.Bls.HashToCurve.hashToG2, hu]
      rfl
    · rw [hashToG2_eq_with]
      unfold hashToG2With
      rw [hu]
      rfl
  | ok us =>
    have h0 := simpleSwuWith_eq us[0]
    have h1 := simpleSwuWith_eq us[1]
    have hm := hashToG2With_ok simpleSwuWith hu
    rw [← hashToG2_eq_with] at hm
    exact Or.inr ⟨_, _, spec_hashToG2_ok hu h0 h1, hm,
      clearCofactor_proj (G2.ProjEq.add (isoMapJac_proj (simpleSwu_curve_eq h0))
        (isoMapJac_proj (simpleSwu_curve_eq h1)))⟩

end EthLibImpl.Cryptography.Bls.Mirror.HashToCurve
