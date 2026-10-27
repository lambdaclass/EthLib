import EthLibImpl.Cryptography.Proofs.Bls.Fp12
import EthLibImpl.Cryptography.Proofs.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.G2Defs
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing
import EthLibImpl.Cryptography.Bls.Pairing

/-!
# Proofs: the implementation's pairing computes its spec-level mirror

For canonical inputs every function of `EthLibImpl.Cryptography.Bls.Pairing`
(`dblStep`, `addStep`, the Miller loop, the final exponentiation and
`pairingCheck`) returns the image under `toSpec` of what the same function in
`Mirror` (`MirrorPairing`) computes over spec types. The proofs are
structural: each implementation field operation is replaced by the spec
operation its lemma gives, and canonicity of every intermediate value is
carried along.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls

/-! ## Definitions -/

/-- Every coordinate of the twist point is canonical. -/
def TwistPoint.Canonical (t : TwistPoint) : Prop :=
  t.x.Canonical ∧ t.y.Canonical ∧ t.z.Canonical

/-- The mirror twist point with the same coordinates. -/
def TwistPoint.toSpec (t : TwistPoint) : Mirror.TwistPoint :=
  ⟨t.x.toSpec, t.y.toSpec, t.z.toSpec⟩

/-- The point and the three `Fp` factors are canonical. -/
def PairInput.Canonical (pi : PairInput) : Prop :=
  pi.r.Canonical ∧ pi.cx.Canonical ∧ pi.cy.Canonical ∧ pi.cz.Canonical

/-- The mirror pair input with the same values. -/
def PairInput.toSpec (pi : PairInput) : Mirror.PairInput :=
  ⟨pi.r.toSpec, pi.cx.val, pi.cy.val, pi.cz.val, pi.pAffine⟩

/-- All three line coefficients are canonical. -/
def Line.Canonical (l : Line) : Prop :=
  l.b0.Canonical ∧ l.b1.Canonical ∧ l.b4.Canonical

/-- The mirror line with the same coefficients. -/
def Line.toSpec (l : Line) : Mirror.Line :=
  ⟨l.b0.toSpec, l.b1.toSpec, l.b4.toSpec⟩

theorem TwistPoint.toSpec_x (t : TwistPoint) : t.toSpec.x = t.x.toSpec := rfl
theorem TwistPoint.toSpec_y (t : TwistPoint) : t.toSpec.y = t.y.toSpec := rfl
theorem TwistPoint.toSpec_z (t : TwistPoint) : t.toSpec.z = t.z.toSpec := rfl
theorem TwistPoint.toSpec_mk (x y z : Fp2) : TwistPoint.toSpec ⟨x, y, z⟩ = ⟨x.toSpec, y.toSpec, z.toSpec⟩ := rfl
theorem PairInput.toSpec_r (pi : PairInput) : pi.toSpec.r = pi.r.toSpec := rfl
theorem PairInput.toSpec_cx (pi : PairInput) : pi.toSpec.cx = pi.cx.val := rfl
theorem PairInput.toSpec_cy (pi : PairInput) : pi.toSpec.cy = pi.cy.val := rfl
theorem PairInput.toSpec_cz (pi : PairInput) : pi.toSpec.cz = pi.cz.val := rfl
theorem PairInput.toSpec_pAffine (pi : PairInput) : pi.toSpec.pAffine = pi.pAffine := rfl
theorem Line.toSpec_mk (a b c : Fp2) : Line.toSpec ⟨a, b, c⟩ = ⟨a.toSpec, b.toSpec, c.toSpec⟩ := rfl

/-! ## Steps -/

theorem PairInput.line_spec {pi : PairInput} (hpi : pi.Canonical) {b0 b1 b4 : Fp2}
    (h0 : b0.Canonical) (h1 : b1.Canonical) (h4 : b4.Canonical) :
    (pi.line b0 b1 b4).Canonical ∧
      (pi.line b0 b1 b4).toSpec = pi.toSpec.line b0.toSpec b1.toSpec b4.toSpec := by
  obtain ⟨_, hcx, hcy, hcz⟩ := hpi
  unfold PairInput.line Mirror.PairInput.line
  cases hA : pi.pAffine
  · simp only [Bool.false_eq_true, if_false]
    refine ⟨⟨Fp2.mulFp_canonical h0 hcz, Fp2.mulFp_canonical h1 hcx,
      Fp2.mulFp_canonical h4 hcy⟩, ?_⟩
    simp only [Line.toSpec_mk, PairInput.toSpec_cx, PairInput.toSpec_cy, PairInput.toSpec_cz,
      PairInput.toSpec_pAffine, hA, Bool.false_eq_true, if_false,
      Fp2.toSpec_mulFp h0 hcz, Fp2.toSpec_mulFp h1 hcx, Fp2.toSpec_mulFp h4 hcy]
  · simp only [if_true]
    refine ⟨⟨h0, Fp2.mulFp_canonical h1 hcx, Fp2.mulFp_canonical h4 hcy⟩, ?_⟩
    simp only [Line.toSpec_mk, PairInput.toSpec_cx, PairInput.toSpec_cy,
      PairInput.toSpec_pAffine, hA, if_true,
      Fp2.toSpec_mulFp h1 hcx, Fp2.toSpec_mulFp h4 hcy]

theorem PairInput.line_canonical {pi : PairInput} (hpi : pi.Canonical) {b0 b1 b4 : Fp2}
    (h0 : b0.Canonical) (h1 : b1.Canonical) (h4 : b4.Canonical) :
    (pi.line b0 b1 b4).Canonical := (PairInput.line_spec hpi h0 h1 h4).1

theorem PairInput.toSpec_line {pi : PairInput} (hpi : pi.Canonical) {b0 b1 b4 : Fp2}
    (h0 : b0.Canonical) (h1 : b1.Canonical) (h4 : b4.Canonical) :
    (pi.line b0 b1 b4).toSpec = pi.toSpec.line b0.toSpec b1.toSpec b4.toSpec :=
  (PairInput.line_spec hpi h0 h1 h4).2

theorem TwistPoint.canonical_mk {x y z : Fp2} :
    TwistPoint.Canonical ⟨x, y, z⟩ ↔ x.Canonical ∧ y.Canonical ∧ z.Canonical := Iff.rfl

section simps

attribute [local simp] Fp2.toSpec_hAdd Fp2.toSpec_hSub Fp2.toSpec_hMul Fp2.toSpec_hNeg
  Fp2.canonical_hAdd Fp2.canonical_hSub Fp2.canonical_hMul Fp2.canonical_hNeg
  Fp2.toSpec_double Fp2.double_canonical Fp2.toSpec_sqr Fp2.sqr_canonical
  Fp2.toSpec_neg Fp2.neg_canonical Fp2.toSpec_zero Fp2.zero_canonical
  TwistPoint.toSpec_mk TwistPoint.toSpec_x TwistPoint.toSpec_y TwistPoint.toSpec_z
  PairInput.toSpec_r TwistPoint.canonical_mk Line.toSpec_mk

set_option maxHeartbeats 4000000 in
theorem dblStep_spec {pi : PairInput} {t : TwistPoint} (hpi : pi.Canonical)
    (ht : t.Canonical) :
    (dblStep pi t).1.Canonical ∧ (dblStep pi t).2.Canonical ∧
      (dblStep pi t).1.toSpec = (Mirror.dblStep pi.toSpec t.toSpec).1 ∧
      (dblStep pi t).2.toSpec = (Mirror.dblStep pi.toSpec t.toSpec).2 := by
  obtain ⟨hx, hy, hz⟩ := ht
  have hzero := Fp2.zero_canonical
  unfold dblStep Mirror.dblStep
  rw [TwistPoint.toSpec_y, Fp2.isZero_eq hy]
  by_cases h : t.y.isZero = true
  · simp only [h, if_true]
    obtain ⟨l1, l2⟩ := PairInput.line_spec hpi (Fp2.neg_canonical hy) hzero Fp2.one_canonical
    refine ⟨⟨?_, hy, hz⟩, l1, ?_, ?_⟩
    · exact Fp2.canonical_hNeg (Fp2.double_canonical hx)
    · simp (config := {maxDischargeDepth := 40}) [hx, hy, hz]
    · rw [l2]; simp (config := {maxDischargeDepth := 40}) [hx, hy, hz, Fp2.toSpec_one]
  · simp only [h, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (config := {maxDischargeDepth := 40}) [hx, hy, hz, hpi, PairInput.line_canonical,
      PairInput.toSpec_line]

set_option maxHeartbeats 4000000 in
theorem addStep_spec {pi : PairInput} {t : TwistPoint} (hpi : pi.Canonical)
    (ht : t.Canonical) :
    (addStep pi t).1.Canonical ∧ (addStep pi t).2.Canonical ∧
      (addStep pi t).1.toSpec = (Mirror.addStep pi.toSpec t.toSpec).1 ∧
      (addStep pi t).2.toSpec = (Mirror.addStep pi.toSpec t.toSpec).2 := by
  obtain ⟨hx, hy, hz⟩ := ht
  obtain ⟨⟨hrx, hry, hrz⟩, hcx, hcy, hcz⟩ := hpi
  have hpi' : pi.Canonical := ⟨⟨hrx, hry, hrz⟩, hcx, hcy, hcz⟩
  have hzero := Fp2.zero_canonical
  have hdd : (pi.r.x * t.z.sqr - t.x * pi.r.z.sqr).Canonical := by simp (config := {maxDischargeDepth := 40}) [hx, hz, hrx, hrz]
  have hde : (pi.r.x * t.z.sqr - t.x * pi.r.z.sqr).toSpec
      = pi.r.x.toSpec * (t.z.toSpec * t.z.toSpec) - t.x.toSpec * (pi.r.z.toSpec * pi.r.z.toSpec) := by
    simp (config := {maxDischargeDepth := 40}) [hx, hz, hrx, hrz]
  unfold addStep Mirror.addStep
  simp only [PairInput.toSpec_r, TwistPoint.toSpec_x, TwistPoint.toSpec_y, TwistPoint.toSpec_z]
  rw [← hde, Fp2.isZero_eq hdd]
  by_cases h : (pi.r.x * t.z.sqr - t.x * pi.r.z.sqr).isZero = true
  · simp only [h, if_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (config := {maxDischargeDepth := 40}) [hx, hy, hz, hrx, hry, hrz, hpi', PairInput.line_canonical,
      PairInput.toSpec_line]
  · simp only [h, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (config := {maxDischargeDepth := 40}) [hx, hy, hz, hrx, hry, hrz, hpi', PairInput.line_canonical,
      PairInput.toSpec_line]

end simps

/-! ## Lists of pairs -/

/-- Every pair of the list is canonical. -/
def StepList.Canonical (l : List (PairInput × TwistPoint)) : Prop :=
  ∀ x ∈ l, x.1.Canonical ∧ x.2.Canonical

/-- A pair of the implementation as a pair of the mirror. -/
def StepList.pairToSpec (x : PairInput × TwistPoint) : Mirror.PairInput × Mirror.TwistPoint :=
  (x.1.toSpec, x.2.toSpec)

theorem StepList.canonical_cons {pi : PairInput} {t : TwistPoint}
    {rest : List (PairInput × TwistPoint)} :
    StepList.Canonical ((pi, t) :: rest) ↔
      (pi.Canonical ∧ t.Canonical) ∧ StepList.Canonical rest := by
  unfold StepList.Canonical
  simp

theorem mulLine_spec {f : Fp12} {l : Line} (hf : f.Canonical) (hl : l.Canonical) :
    (f.mulBy014 l.b0 l.b1 l.b4).Canonical ∧
      (f.mulBy014 l.b0 l.b1 l.b4).toSpec = f.toSpec * l.toSpec.toFp12 :=
  ⟨Fp12.mulBy014_canonical hf hl.1 hl.2.1 hl.2.2, Fp12.toSpec_mulBy014 hf hl.1 hl.2.1 hl.2.2⟩

open Lean Elab Term Meta in
/-- The value of the constant `c` with the constant `stepName` abstracted into a lambda
parameter. Used to restate `addAll` over an arbitrary step function without
re-elaborating its structural recursion, which keeps the term syntactically the same. -/
elab "abstractStep% " c:ident ", " stepName:ident : term => do
  let env ← getEnv
  let cName ← realizeGlobalConstNoOverloadWithInfo c
  let sName ← realizeGlobalConstNoOverloadWithInfo stepName
  let some (.defnInfo di) := env.find? cName | throwError "not a definition"
  let stepTy := (env.find? sName).get!.type
  withLocalDeclD `step stepTy fun st => do
    let v := di.value.replace fun e => if e.isConstOf sName then some st else none
    mkLambdaFVars #[st] v

/-- `dblAll` and `addAll` are one recursion over a step function. Proving
about this generic form keeps the kernel from unfolding the concrete step
(whose branch condition is a field product) when it checks the unfolding
lemmas: `addAll` with `addStep` abstracted, so `addAll = allG addStep` holds
by syntactic equality after unfolding. -/
def allG : (PairInput → TwistPoint → TwistPoint × Line) → Fp12 →
    List (PairInput × TwistPoint) → Fp12 × List (PairInput × TwistPoint) :=
  abstractStep% addAll, addStep

/-- The mirror's counterpart of `allG`. -/
def mAllG : (Mirror.PairInput → Mirror.TwistPoint → Mirror.TwistPoint × Mirror.Line) →
    EthLib.Cryptography.Bls.Fp12 → List (Mirror.PairInput × Mirror.TwistPoint) →
    EthLib.Cryptography.Bls.Fp12 × List (Mirror.PairInput × Mirror.TwistPoint) :=
  abstractStep% Mirror.addAll, Mirror.addStep

theorem dblAll_eq : dblAll = allG dblStep := by
  delta dblAll allG
  rfl
theorem addAll_eq : addAll = allG addStep := by
  delta addAll allG
  rfl
theorem mirror_dblAll_eq : Mirror.dblAll = mAllG Mirror.dblStep := by
  delta Mirror.dblAll mAllG
  rfl
theorem mirror_addAll_eq : Mirror.addAll = mAllG Mirror.addStep := by
  delta Mirror.addAll mAllG
  rfl

theorem allG_nil (step : PairInput → TwistPoint → TwistPoint × Line) (f : Fp12) :
    allG step f [] = (f, []) := rfl

theorem allG_cons (step : PairInput → TwistPoint → TwistPoint × Line) (f : Fp12)
    (pi : PairInput) (t : TwistPoint) (rest : List (PairInput × TwistPoint)) :
    allG step f ((pi, t) :: rest) =
      match step pi t with
      | (t', l) =>
        match allG step (f.mulBy014 l.b0 l.b1 l.b4) rest with
        | (f', rest') => (f', (pi, t') :: rest') := rfl

theorem mAllG_nil (step : Mirror.PairInput → Mirror.TwistPoint → Mirror.TwistPoint × Mirror.Line)
    (f : EthLib.Cryptography.Bls.Fp12) : mAllG step f [] = (f, []) := rfl

theorem mAllG_cons
    (step : Mirror.PairInput → Mirror.TwistPoint → Mirror.TwistPoint × Mirror.Line)
    (f : EthLib.Cryptography.Bls.Fp12) (pi : Mirror.PairInput) (t : Mirror.TwistPoint)
    (rest : List (Mirror.PairInput × Mirror.TwistPoint)) :
    mAllG step f ((pi, t) :: rest) =
      match step pi t with
      | (t', l) =>
        match mAllG step (f * l.toFp12) rest with
        | (f', rest') => (f', (pi, t') :: rest') := rfl

theorem allG_spec {step : PairInput → TwistPoint → TwistPoint × Line}
    {mstep : Mirror.PairInput → Mirror.TwistPoint → Mirror.TwistPoint × Mirror.Line}
    (hstep : ∀ {pi : PairInput} {t : TwistPoint}, pi.Canonical → t.Canonical →
      (step pi t).1.Canonical ∧ (step pi t).2.Canonical ∧
        (step pi t).1.toSpec = (mstep pi.toSpec t.toSpec).1 ∧
        (step pi t).2.toSpec = (mstep pi.toSpec t.toSpec).2) :
    ∀ (l : List (PairInput × TwistPoint)) {f : Fp12}, StepList.Canonical l →
    f.Canonical →
    (allG step f l).1.Canonical ∧ StepList.Canonical (allG step f l).2 ∧
      (allG step f l).1.toSpec = (mAllG mstep f.toSpec (l.map StepList.pairToSpec)).1 ∧
      (allG step f l).2.map StepList.pairToSpec =
        (mAllG mstep f.toSpec (l.map StepList.pairToSpec)).2
  | [], f, _, hf => by
    simp only [List.map_nil]
    rw [allG_nil, mAllG_nil]
    exact ⟨hf, fun x hx => by simp at hx, rfl, rfl⟩
  | (pi, t) :: rest, f, hl, hf => by
    obtain ⟨⟨hpi, ht⟩, hrest⟩ := StepList.canonical_cons.1 hl
    obtain ⟨c1, c2, e1, e2⟩ := hstep hpi ht
    rcases hd : step pi t with ⟨t', l⟩
    rcases hm : mstep pi.toSpec t.toSpec with ⟨mt, ml⟩
    rw [hd] at c1 c2 e1 e2
    rw [hm] at e1 e2
    simp only at c1 c2 e1 e2
    subst e1 e2
    obtain ⟨hm1, hm2⟩ := mulLine_spec hf c2
    obtain ⟨r1, r2, r3, r4⟩ := allG_spec hstep rest hrest hm1
    simp only [List.map_cons, StepList.pairToSpec]
    rw [allG_cons, hd, mAllG_cons, hm]
    dsimp only
    refine ⟨r1, StepList.canonical_cons.2 ⟨⟨hpi, c1⟩, r2⟩, ?_, ?_⟩
    · rw [← hm2]; exact r3
    · rw [← hm2, ← r4]; rfl

/-- `dblAll` computes the mirror's `dblAll`. -/
theorem dblAll_spec (l : List (PairInput × TwistPoint)) {f : Fp12} (hl : StepList.Canonical l)
    (hf : f.Canonical) :
    (dblAll f l).1.Canonical ∧ StepList.Canonical (dblAll f l).2 ∧
      (dblAll f l).1.toSpec = (Mirror.dblAll f.toSpec (l.map StepList.pairToSpec)).1 ∧
      (dblAll f l).2.map StepList.pairToSpec =
        (Mirror.dblAll f.toSpec (l.map StepList.pairToSpec)).2 := by
  rw [dblAll_eq, mirror_dblAll_eq]
  exact allG_spec dblStep_spec l hl hf

/-- `addAll` computes the mirror's `addAll`. -/
theorem addAll_spec (l : List (PairInput × TwistPoint)) {f : Fp12} (hl : StepList.Canonical l)
    (hf : f.Canonical) :
    (addAll f l).1.Canonical ∧ StepList.Canonical (addAll f l).2 ∧
      (addAll f l).1.toSpec = (Mirror.addAll f.toSpec (l.map StepList.pairToSpec)).1 ∧
      (addAll f l).2.map StepList.pairToSpec =
        (Mirror.addAll f.toSpec (l.map StepList.pairToSpec)).2 := by
  rw [addAll_eq, mirror_addAll_eq]
  exact allG_spec addStep_spec l hl hf

/-! ## Miller loop -/

theorem blsX_eq : blsX = EthLib.Cryptography.Bls.blsX := rfl

theorem blsXWord_toNat : blsXWord.toNat = blsX := by decide

/-- The word-level bit test of `blsX` is the mirror's. -/
theorem blsX_bit (n : Nat) (hn : n < 64) :
    ((blsXWord >>> n.toUInt64) &&& 1 != 0) = true ↔ (EthLib.Cryptography.Bls.blsX >>> n) &&& 1 = 1 := by
  rw [G1.bit_spec blsXWord n hn, blsXWord_toNat, blsX_eq, Nat.testBit, Nat.and_comm, bne_iff_ne, ne_eq, Nat.and_one_is_mod]
  omega

theorem millerSteps_spec : ∀ (n : Nat), n ≤ 64 → ∀ (st : List (PairInput × TwistPoint))
    {f : Fp12}, StepList.Canonical st → f.Canonical →
    (millerSteps n st f).Canonical ∧
      (millerSteps n st f).toSpec = Mirror.millerSteps n (st.map StepList.pairToSpec) f.toSpec
  | 0, _, st, f, _, hf => by
    rw [millerSteps, Mirror.millerSteps]
    exact ⟨hf, rfl⟩
  | n + 1, hn, st, f, hst, hf => by
    have hsq := Fp12.sqr_canonical hf
    obtain ⟨d1, d2, d3, d4⟩ := dblAll_spec st hst hsq
    rw [Fp12.toSpec_sqr hf] at d3 d4
    rcases hd : dblAll f.sqr st with ⟨f1, st1⟩
    rcases hm : Mirror.dblAll (f.toSpec * f.toSpec) (st.map StepList.pairToSpec) with ⟨mf, mst⟩
    rw [hd] at d1 d2 d3 d4
    rw [hm] at d3 d4
    simp only at d1 d2 d3 d4
    subst d3 d4
    have hb := blsX_bit n (by omega)
    rw [millerSteps, Mirror.millerSteps, hd, hm]
    dsimp only
    by_cases hbit : (blsXWord >>> n.toUInt64 &&& 1 != 0) = true
    · rw [if_pos hbit, if_pos (hb.1 hbit)]
      obtain ⟨a1, a2, a3, a4⟩ := addAll_spec st1 d2 d1
      rcases ha : addAll f1 st1 with ⟨f2, st2⟩
      rcases hma : Mirror.addAll f1.toSpec (st1.map StepList.pairToSpec) with ⟨mf2, mst2⟩
      rw [ha] at a1 a2 a3 a4
      rw [hma] at a3 a4
      simp only at a1 a2 a3 a4
      subst a3 a4
      exact millerSteps_spec n (by omega) st2 a2 a1
    · rw [if_neg hbit, if_neg (fun h => hbit (hb.2 h))]
      exact millerSteps_spec n (by omega) st1 d2 d1

theorem millerLoop_spec {pis : List PairInput} (h : ∀ pi ∈ pis, pi.Canonical) :
    (millerLoop pis).Canonical ∧
      (millerLoop pis).toSpec = Mirror.millerLoop (pis.map PairInput.toSpec) := by
  have hlog : blsX.log2 ≤ 64 := by decide
  have hst : StepList.Canonical (pis.map fun pi => (pi, pi.r)) := by
    intro x hx
    obtain ⟨pi, hpi, rfl⟩ := List.mem_map.1 hx
    exact ⟨h pi hpi, (h pi hpi).1⟩
  obtain ⟨c, e⟩ := millerSteps_spec _ hlog _ hst Fp12.one_canonical
  refine ⟨c, ?_⟩
  unfold millerLoop Mirror.millerLoop
  rw [e, blsX_eq, Fp12.toSpec_one]
  congr 1
  rw [List.map_map, List.map_map]
  rfl

theorem PairInput.ofPoints_spec {p : G1} {q : G2} (hp : p.Canonical) (hq : q.Canonical) :
    (PairInput.ofPoints p q).Canonical ∧
      (PairInput.ofPoints p q).toSpec = Mirror.PairInput.ofPoints p.toSpec q.toSpec := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  have h1 := Fp2.one_canonical
  have h2 := Fp.one_canonical
  have b1 : p.z.beq Fp.one = (G1.toSpec p).z.beq EthLib.Cryptography.Bls.Fp.one := by
    rw [G1.beq_eq hpz h2, Fp.val_one]; rfl
  have mz1 : (p.z.sqr * p.z).Canonical := Fp.mul_canonical _ hpz
  have mx1 : (p.x * p.z).Canonical := Fp.mul_canonical _ hpz
  have vz1 : (p.z.sqr * p.z).val = (G1.toSpec p).z * (G1.toSpec p).z * (G1.toSpec p).z := by
    exact (Fp.val_mul _ hpz).trans (by rw [Fp.val_sqr hpz]; rfl)
  have vx1 : (p.x * p.z).val = (G1.toSpec p).x * (G1.toSpec p).z := by
    exact Fp.val_mul _ hpz
  unfold PairInput.ofPoints Mirror.PairInput.ofPoints
  rw [b1]
  by_cases hb1 : (G1.toSpec p).z.beq EthLib.Cryptography.Bls.Fp.one = true <;>
  simp only [hb1, if_true, if_false, Bool.false_eq_true] <;>
  refine ⟨?_, ?_⟩ <;>
  simp only [PairInput.Canonical, TwistPoint.Canonical, PairInput.toSpec, TwistPoint.toSpec,
    hpx, hpy, hpz, hqx, hqy, hqz, h2, mz1, mx1, vz1, vx1, and_self,
    Fp.one_canonical, Fp.val_one] <;>
  rfl

/-! ## Final exponentiation -/

theorem word_bit (k : UInt64) (n : Nat) (hn : n < 64) :
    ((k >>> n.toUInt64) &&& 1 != 0) = true ↔ (k.toNat >>> n) &&& 1 = 1 := by
  rw [G1.bit_spec k n hn, Nat.testBit, Nat.and_comm, bne_iff_ne, ne_eq, Nat.and_one_is_mod]
  omega

theorem cycPowMsb_spec {g : Fp12} (hg : g.Canonical) (k : UInt64) :
    ∀ (n : Nat), n ≤ 64 → ∀ {acc : Fp12}, acc.Canonical →
      (cycPowMsb g k n acc).Canonical ∧
        (cycPowMsb g k n acc).toSpec = Mirror.cycPowMsb g.toSpec k.toNat n acc.toSpec
  | 0, _, acc, hacc => by
    rw [cycPowMsb, Mirror.cycPowMsb]
    exact ⟨hacc, rfl⟩
  | n + 1, hn, acc, hacc => by
    have hc := Fp12.cycSqr_canonical hacc
    have hs := Fp12.toSpec_cycSqr hacc
    have hb := word_bit k n (by omega)
    rw [cycPowMsb, Mirror.cycPowMsb, ← hs]
    by_cases hbit : (k >>> n.toUInt64 &&& 1 != 0) = true
    · rw [if_pos hbit, if_pos (hb.1 hbit)]
      have hm := Fp12.mul_canonical hc hg
      have e := Fp12.toSpec_mul hc hg
      obtain ⟨c, e'⟩ := cycPowMsb_spec hg k n (by omega) hm
      rw [e] at e'
      exact ⟨c, e'⟩
    · rw [if_neg hbit, if_neg (fun h => hbit (hb.2 h))]
      exact cycPowMsb_spec hg k n (by omega) hc

theorem cycPowAbsX_spec {g : Fp12} (hg : g.Canonical) :
    (cycPowAbsX g).Canonical ∧
      (cycPowAbsX g).toSpec = Mirror.cycPowAbsX g.toSpec := by
  have := cycPowMsb_spec hg blsXWord 63 (by omega) hg
  rw [blsXWord_toNat] at this
  exact this

theorem cycPowAbsX_canonical {g : Fp12} (hg : g.Canonical) : (cycPowAbsX g).Canonical :=
  (cycPowAbsX_spec hg).1

theorem toSpec_cycPowAbsX {g : Fp12} (hg : g.Canonical) :
    (cycPowAbsX g).toSpec = Mirror.cycPowAbsX g.toSpec := (cycPowAbsX_spec hg).2

section fin

attribute [local simp] Fp12.toSpec_hMul Fp12.canonical_hMul Fp12.conj_canonical Fp12.toSpec_conj
  Fp12.inverse_canonical Fp12.toSpec_inverse Fp12.frobenius1_canonical Fp12.toSpec_frobenius1
  Fp12.frobenius2_canonical Fp12.toSpec_frobenius2 cycPowAbsX_canonical toSpec_cycPowAbsX
  Fp12.cycSqr_canonical Fp12.toSpec_cycSqr

/-- The final exponentiation computes the mirror's. -/
theorem finalExpCube_spec {f : Fp12} (hf : f.Canonical) :
    (finalExpCube f).Canonical ∧
      (finalExpCube f).toSpec = Mirror.finalExpCube f.toSpec := by
  unfold finalExpCube Mirror.finalExpCube
  refine ⟨?_, ?_⟩ <;> simp (config := {maxDischargeDepth := 40}) [hf]

end fin

/-! ## The pairing check -/

theorem filterMap_pairs (op : G1 → G2 → PairInput)
    (mop : EthLib.Cryptography.Bls.G1 → EthLib.Cryptography.Bls.G2 → Mirror.PairInput)
    (hop : ∀ {p : G1} {q : G2}, p.Canonical → q.Canonical →
      (op p q).Canonical ∧ (op p q).toSpec = mop p.toSpec q.toSpec) :
    ∀ (l : List (G1 × G2)), (∀ pq ∈ l, pq.1.Canonical ∧ pq.2.Canonical) →
    (∀ pi ∈ l.filterMap (fun (pq : G1 × G2) =>
        if pq.1.isInfinity || pq.2.isInfinity then none
        else some (op pq.1 pq.2)), pi.Canonical) ∧
    (l.map fun pq => (G1.toSpec pq.1, G2.toSpec pq.2)).filterMap
        (fun (pq : EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2) =>
          if pq.1.isInfinity || pq.2.isInfinity then none
          else some (mop pq.1 pq.2)) =
      (l.filterMap (fun (pq : G1 × G2) =>
        if pq.1.isInfinity || pq.2.isInfinity then none
        else some (op pq.1 pq.2))).map PairInput.toSpec
  | [], _ => ⟨fun pi hpi => by simp at hpi, rfl⟩
  | (p, q) :: rest, h => by
    have hp := (h (p, q) (by simp)).1
    have hq := (h (p, q) (by simp)).2
    obtain ⟨ih1, ih2⟩ := filterMap_pairs op mop hop rest (fun x hx => h x (by simp [hx]))
    have hi : p.isInfinity = (G1.toSpec p).isInfinity := G1.isInfinity_spec hp
    have hj : q.isInfinity = (G2.toSpec q).isInfinity := by
      show q.z.isZero = (G2.toSpec q).z.isZero
      exact (Fp2.isZero_eq hq.2.2).symm
    obtain ⟨o1, o2⟩ := hop hp hq
    have hinf' : (p.isInfinity || q.isInfinity) =
        ((G1.toSpec p).isInfinity || (G2.toSpec q).isInfinity) := by rw [hi, hj]
    rw [List.map_cons]
    by_cases hinf : (p.isInfinity || q.isInfinity) = true
    · have hinf2 : ((G1.toSpec p).isInfinity || (G2.toSpec q).isInfinity) = true := by
        rw [← hinf']; exact hinf
      rw [List.filterMap_cons_none (by simp only [hinf, if_true]),
        List.filterMap_cons_none (by simp only [hinf2, if_true])]
      exact ⟨ih1, ih2⟩
    · have hinf2 : ¬ ((G1.toSpec p).isInfinity || (G2.toSpec q).isInfinity) = true := by
        rw [← hinf']; exact hinf
      rw [List.filterMap_cons_some (b := op p q) (by simp only [hinf, if_false, Bool.false_eq_true]),
        List.filterMap_cons_some (b := mop (G1.toSpec p) (G2.toSpec q))
          (by simp only [hinf2, if_false, Bool.false_eq_true]), List.map_cons, o2, ih2]
      refine ⟨?_, rfl⟩
      intro pi hpi
      rcases List.mem_cons.1 hpi with rfl | hm
      · exact o1
      · exact ih1 pi hm

/-- The implementation's `pairingCheck` is the mirror's on canonical points. -/
theorem pairingCheck_spec (pairs : Array (G1 × G2))
    (h : ∀ pq ∈ pairs, pq.1.Canonical ∧ pq.2.Canonical) :
    pairingCheck pairs =
      Mirror.pairingCheck (pairs.map fun pq => (G1.toSpec pq.1, G2.toSpec pq.2)) := by
  have hl : ∀ pq ∈ pairs.toList, pq.1.Canonical ∧ pq.2.Canonical :=
    fun pq hpq => h pq (Array.mem_toList_iff.1 hpq)
  obtain ⟨c, e⟩ := filterMap_pairs PairInput.ofPoints Mirror.PairInput.ofPoints
    (fun hp hq => PairInput.ofPoints_spec hp hq) pairs.toList hl
  unfold pairingCheck Mirror.pairingCheck
  rw [Array.toList_map]
  simp only []
  rw [e]
  obtain ⟨m1, m2⟩ := millerLoop_spec c
  have hc := Fp12.conj_canonical m1
  obtain ⟨f1, f2⟩ := finalExpCube_spec hc
  rw [← Fp12.isOne_eq f1, f2, Fp12.toSpec_conj m1, m2]

end EthLibImpl.Cryptography.Bls
