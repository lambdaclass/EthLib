import EthLibImpl.Cryptography.Bls.Signatures
import EthLibImpl.Cryptography.Proofs.Bls.CompressG1
import EthLibImpl.Cryptography.Proofs.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.SigMath

/-!
# Proofs: the implementation's signature layer is the mirror's

`EthLibImpl.Cryptography.Bls.Signatures` equals its mirror
(`Mirror.Signatures`), hence, with `SigMath`, the spec. The only part that
touches G2, hashing and pairing is `coreVerifyPoint`; its correspondence is
the hypothesis `CoreVerifyHyp`. Everything else (key validation, the
aggregation loops, the compressed aggregate key) is proven here.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls.Signatures

open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Bls (BlsError)

/-- `coreVerifyPoint` of the implementation, read through `G1.toSpec`. -/
def CoreVerifyHyp : Prop :=
  ∀ (pk : G1) (msg sig : ByteArray), G1.Canonical pk →
    coreVerifyPoint pk msg sig = Mirror.Signatures.coreVerifyPoint (G1.toSpec pk) msg sig

/-! ## 1. Key validation -/

/-- The implementation's `inSubgroup` is the mirror's endomorphism test on a valid point. -/
theorem inSubgroup_mirror {p : G1} (hp : G1.Canonical p)
    (hv : EthLib.Cryptography.Bls.G1.Valid (G1.toSpec p)) :
    G1.inSubgroup p = Mirror.Signatures.g1InSubgroup (G1.toSpec p) := by
  rw [G1.inSubgroup_spec hp hv, Mirror.Signatures.g1InSubgroup_eq hv]

/-- `validatedPubkey` computes the mirror's, and its results are canonical. -/
theorem validatedPubkey_spec (b : ByteArray) :
    (validatedPubkey b).map G1.toSpec = Mirror.Signatures.validatedPubkey b ∧
      ∀ p, validatedPubkey b = .ok p → G1.Canonical p := by
  obtain ⟨hm, hc⟩ := G1.uncompress_spec b
  cases hu : G1.uncompress b with
  | error e =>
    have hs : EthLib.Cryptography.Bls.G1.uncompress b = .error e := by rw [← hm, hu]; rfl
    refine ⟨?_, ?_⟩
    · simp only [validatedPubkey, Mirror.Signatures.validatedPubkey, hu, hs]
      rfl
    · intro p hp
      simp only [validatedPubkey, hu] at hp
      cases hp
  | ok q =>
    have hqc := hc q hu
    have hs : EthLib.Cryptography.Bls.G1.uncompress b = .ok (G1.toSpec q) := by
      rw [← hm, hu]; rfl
    have hv := (EthLib.Cryptography.Bls.G1.uncompress_valid b _ hs).1
    have hinf := G1.isInfinity_spec hqc
    have hsub := inSubgroup_mirror hqc hv
    have hb : ∀ {α : Type} (f : G1 → Except BlsError α), (Except.ok q >>= f) = f q :=
      fun _ => rfl
    have hb' : ∀ {α : Type} (f : EthLib.Cryptography.Bls.G1 → Except BlsError α),
        (Except.ok (G1.toSpec q) >>= f) = f (G1.toSpec q) := fun _ => rfl
    refine ⟨?_, ?_⟩
    · simp only [validatedPubkey, Mirror.Signatures.validatedPubkey, hu, hs, hb, hb']
      by_cases h1 : q.isInfinity = true
      · have h1' : (G1.toSpec q).isInfinity = true := hinf ▸ h1
        simp only [h1, h1', if_true]
        rfl
      · have h1' : ¬ (G1.toSpec q).isInfinity = true := hinf ▸ h1
        rw [hsub]
        by_cases h2 : Mirror.Signatures.g1InSubgroup (G1.toSpec q) = true
        · simp only [h1, h1', h2]; rfl
        · simp only [h1, h1', h2]; rfl
    · intro p hp
      simp only [validatedPubkey, hu, hb] at hp
      by_cases h1 : q.isInfinity = true
      · simp only [h1, if_true] at hp; cases hp
      · by_cases h2 : G1.inSubgroup q = true
        · simp only [h1, h2] at hp
          cases hp
          exact hqc
        · simp only [h1, h2] at hp; cases hp

/-! ## 2. Loop simulation -/

/-- Related results of `Except` computations: same error, or related values. -/
def ExceptRel {ε β β' : Type} (inv : β → β' → Prop) : Except ε β → Except ε β' → Prop
  | .error e, .error e' => e = e'
  | .ok b, .ok b' => inv b b'
  | _, _ => False

theorem forIn_except_sim {ε α β β' : Type} (inv : β → β' → Prop) (l : List α)
    (f : α → β → Except ε (ForInStep β)) (f' : α → β' → Except ε (ForInStep β'))
    (hstep : ∀ a ∈ l, ∀ b b', inv b b' →
      ExceptRel (fun x x' => ∃ y y', x = .yield y ∧ x' = .yield y' ∧ inv y y') (f a b) (f' a b')) :
    ∀ (init : β) (init' : β'), inv init init' →
      ExceptRel inv (forIn l init f) (forIn l init' f') := by
  induction l with
  | nil => intro init init' h; exact h
  | cons a l ih =>
    intro init init' h
    rw [List.forIn_cons, List.forIn_cons]
    have hs := hstep a List.mem_cons_self init init' h
    cases h1 : f a init with
    | error e =>
      cases h2 : f' a init' with
      | error e' => rw [h1, h2] at hs; simp only [bind, Except.bind]; exact hs
      | ok y' => rw [h1, h2] at hs; exact hs.elim
    | ok y =>
      cases h2 : f' a init' with
      | error e' => rw [h1, h2] at hs; exact hs.elim
      | ok y' =>
        rw [h1, h2] at hs
        obtain ⟨x, x', rfl, rfl, hxx⟩ := hs
        simp only [bind, Except.bind]
        exact ih (fun a ha => hstep a (List.mem_cons_of_mem _ ha)) x x' hxx

theorem forIn_except_range_sim {ε β β' : Type} (inv : β → β' → Prop) (n : Nat)
    (f : Nat → β → Except ε (ForInStep β)) (f' : Nat → β' → Except ε (ForInStep β'))
    (hstep : ∀ i, i < n → ∀ b b', inv b b' →
      ExceptRel (fun x x' => ∃ y y', x = .yield y ∧ x' = .yield y' ∧ inv y y') (f i b) (f' i b'))
    (init : β) (init' : β') (h0 : inv init init') :
    ExceptRel inv (forIn [:n] init f) (forIn [:n] init' f') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_except_sim inv _ f f' ?_ init init' h0
  intro a ha
  rw [List.mem_range'_1] at ha
  exact hstep a (by simpa using ha.2)

/-- `Id` loops whose steps may stop early: related states stay related, and a stop on one
side is a stop on the other. -/
def StepRel {β β' : Type} (inv : β → β' → Prop) : ForInStep β → ForInStep β' → Prop
  | .done b, .done b' => inv b b'
  | .yield b, .yield b' => inv b b'
  | _, _ => False

theorem forIn_id_sim {α β β' : Type} (inv : β → β' → Prop) (l : List α)
    (f : α → β → Id (ForInStep β)) (f' : α → β' → Id (ForInStep β'))
    (hstep : ∀ a b b', inv b b' → StepRel inv (f a b).run (f' a b').run) :
    ∀ (init : β) (init' : β'), inv init init' →
      inv (forIn (m := Id) l init f).run (forIn (m := Id) l init' f').run := by
  induction l with
  | nil => intro init init' h; exact h
  | cons a l ih =>
    intro init init' h
    rw [List.forIn_cons, List.forIn_cons]
    have hs := hstep a init init' h
    show inv (match (f a init).run with
        | ForInStep.done b => pure b
        | ForInStep.yield b => forIn l b f).run
      (match (f' a init').run with
        | ForInStep.done b => pure b
        | ForInStep.yield b => forIn l b f').run
    revert hs
    cases (f a init).run <;> cases (f' a init').run <;> intro hs
    · exact hs
    · exact hs.elim
    · exact hs.elim
    · exact ih _ _ hs

/-! ## 3. `ethAggregatePubkeys` -/

/-- The implementation's `ethAggregatePubkeys` loop body. -/
def stepAI (pks : Array ByteArray) (i : Nat) (agg : G1) : Except BlsError (ForInStep G1) :=
  if pks[i]!.size ≠ 48 then throw (.badPubkeySize pks[i]!.size)
  else match validatedPubkey pks[i]! with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => pure (.yield (G1.add agg p))

theorem ethAggregatePubkeys_unfold (pks : Array ByteArray) :
    ethAggregatePubkeys pks =
      if pks.isEmpty = true then throw .emptyPubkeyList
      else (forIn [:pks.size] G1.zero (stepAI pks)) >>= fun agg => pure (G1.compress agg) :=
  rfl

/-- Related accumulators: canonical, and equal to the mirror's through `toSpec`. -/
def AggRel (g : G1) (g' : EthLib.Cryptography.Bls.G1) : Prop :=
  G1.Canonical g ∧ G1.toSpec g = g'

theorem stepAI_rel (pks : Array ByteArray) (i : Nat) (g : G1)
    (g' : EthLib.Cryptography.Bls.G1) (h : AggRel g g') :
    ExceptRel (fun x x' => ∃ y y', x = .yield y ∧ x' = .yield y' ∧ AggRel y y')
      (stepAI pks i g) (Mirror.Signatures.stepAM pks i g') := by
  unfold stepAI Mirror.Signatures.stepAM
  by_cases hsz : pks[i]!.size ≠ 48
  · rw [if_pos hsz, if_pos hsz]; rfl
  · rw [if_neg hsz, if_neg hsz]
    obtain ⟨hm, hc⟩ := validatedPubkey_spec pks[i]!
    cases hv : validatedPubkey pks[i]! with
    | error e =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pks[i]! = .error e := hm.symm
      simp only [hm']
      rfl
    | ok p =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pks[i]! = .ok (G1.toSpec p) := hm.symm
      simp only [hm']
      have hpc := hc p hv
      obtain ⟨hac, has⟩ := G1.add_spec h.1 hpc
      refine ⟨_, _, rfl, rfl, hac, ?_⟩
      rw [has, h.2]

/-- **`ethAggregatePubkeys` of the implementation is the mirror's.** -/
theorem ethAggregatePubkeys_eq_mirror (pks : Array ByteArray) :
    ethAggregatePubkeys pks = Mirror.Signatures.ethAggregatePubkeys pks := by
  rw [ethAggregatePubkeys_unfold, Mirror.Signatures.ethAggregatePubkeys_unfold]
  by_cases he : pks.isEmpty = true
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    have hl := forIn_except_range_sim AggRel pks.size (stepAI pks) (Mirror.Signatures.stepAM pks)
      (fun i _ b b' hb => stepAI_rel pks i b b' hb) G1.zero EthLib.Cryptography.Bls.G1.zero
      ⟨G1.zero_spec.1, G1.zero_spec.2⟩
    generalize forIn [:pks.size] G1.zero (stepAI pks) = r at hl
    generalize forIn [:pks.size] EthLib.Cryptography.Bls.G1.zero (Mirror.Signatures.stepAM pks) = r'
      at hl
    cases r with
    | error e =>
      cases r' with
      | error e' => cases hl; rfl
      | ok y' => exact hl.elim
    | ok y =>
      cases r' with
      | error e' => exact hl.elim
      | ok y' =>
        obtain ⟨hc, hs⟩ := hl
        simp only [bind, Except.bind, pure, Except.pure]
        rw [G1.compress_spec hc, hs]

/-- **End to end:** `ethAggregatePubkeys` of the implementation is the spec's. -/
theorem ethAggregatePubkeys_eq_spec (pks : Array ByteArray) :
    ethAggregatePubkeys pks = EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks := by
  rw [ethAggregatePubkeys_eq_mirror, Mirror.Signatures.ethAggregatePubkeys_eq]

/-! ## 4. `fastAggregateVerify` -/

/-- The implementation's `fastAggregateVerify` loop body. -/
def stepI (pk : ByteArray) (r : MProd (Option Bool) G1) :
    Id (ForInStep (MProd (Option Bool) G1)) :=
  if pk.size ≠ 48 then pure (.done ⟨some false, r.snd⟩)
  else match validatedPubkey pk with
    | .error _ => pure (.done ⟨some false, r.snd⟩)
    | .ok p => pure (.yield ⟨none, G1.add r.snd p⟩)

theorem fastAggregateVerify_unfold (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig =
      if pks.isEmpty = true then false
      else
        let r := (forIn pks ⟨none, G1.zero⟩ stepI).run
        match r.fst with
        | none => coreVerifyPoint r.snd msg sig
        | some a => a := rfl

/-- Related loop states: same early-exit flag, related accumulators. -/
def RRel (r : MProd (Option Bool) G1) (r' : MProd (Option Bool) EthLib.Cryptography.Bls.G1) :
    Prop := r.fst = r'.fst ∧ AggRel r.snd r'.snd

theorem stepI_rel (pk : ByteArray) (r : MProd (Option Bool) G1)
    (r' : MProd (Option Bool) EthLib.Cryptography.Bls.G1) (h : RRel r r') :
    StepRel RRel (stepI pk r).run (Mirror.Signatures.stepM pk r').run := by
  unfold stepI Mirror.Signatures.stepM
  by_cases hsz : pk.size ≠ 48
  · rw [if_pos hsz, if_pos hsz]
    exact ⟨rfl, h.2⟩
  · rw [if_neg hsz, if_neg hsz]
    obtain ⟨hm, hc⟩ := validatedPubkey_spec pk
    cases hv : validatedPubkey pk with
    | error e =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pk = .error e := hm.symm
      simp only [hm']
      exact ⟨rfl, h.2⟩
    | ok p =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pk = .ok (G1.toSpec p) := hm.symm
      simp only [hm']
      have hpc := hc p hv
      obtain ⟨hac, has⟩ := G1.add_spec h.2.1 hpc
      refine ⟨rfl, hac, ?_⟩
      show G1.toSpec (G1.add r.snd p) = _
      rw [has, h.2.2]

/-- **`fastAggregateVerify` of the implementation is the mirror's**, given `coreVerifyPoint`. -/
theorem fastAggregateVerify_eq (hcv : CoreVerifyHyp) (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig = Mirror.Signatures.fastAggregateVerify pks msg sig := by
  rw [fastAggregateVerify_unfold, Mirror.Signatures.fastAggregateVerify_unfold]
  by_cases he : pks.isEmpty = true
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    have hl := forIn_id_sim RRel pks.toList stepI Mirror.Signatures.stepM stepI_rel
      (⟨none, G1.zero⟩ : MProd (Option Bool) G1)
      (⟨none, EthLib.Cryptography.Bls.G1.zero⟩ : MProd (Option Bool) EthLib.Cryptography.Bls.G1)
      ⟨rfl, G1.zero_spec.1, G1.zero_spec.2⟩
    simp only [Array.forIn_toList] at hl
    simp only
    generalize (forIn pks ⟨none, G1.zero⟩ stepI).run = r at hl ⊢
    generalize (forIn pks ⟨none, EthLib.Cryptography.Bls.G1.zero⟩ Mirror.Signatures.stepM).run = r'
      at hl ⊢
    obtain ⟨o, g⟩ := r
    obtain ⟨o', g'⟩ := r'
    obtain ⟨h1, hc, hs⟩ := hl
    simp only at h1 hc hs
    subst h1
    cases o with
    | none => simp only; rw [hcv g msg sig hc, hs]
    | some a => rfl

/-- The two encodings of the G2 point at infinity are the same bytes. -/
theorem g2_infinity_eq :
    G2_POINT_AT_INFINITY = EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY := rfl

/-- **`ethFastAggregateVerify` of the implementation is the mirror's.** -/
theorem ethFastAggregateVerify_eq_mirror (hcv : CoreVerifyHyp)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig = Mirror.Signatures.ethFastAggregateVerify pks msg sig := by
  unfold ethFastAggregateVerify Mirror.Signatures.ethFastAggregateVerify
  rw [fastAggregateVerify_eq hcv, g2_infinity_eq]

/-- **End to end:** `ethFastAggregateVerify` of the implementation is the spec's, given the
`coreVerifyPoint`, pairing and hash-to-curve layers. -/
theorem ethFastAggregateVerify_eq_spec (hcv : CoreVerifyHyp)
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.Signatures.HashRel msg dst)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig
      = EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig := by
  rw [ethFastAggregateVerify_eq_mirror hcv, Mirror.Signatures.ethFastAggregateVerify_eq hpair hhash]

end EthLibImpl.Cryptography.Bls.Signatures
