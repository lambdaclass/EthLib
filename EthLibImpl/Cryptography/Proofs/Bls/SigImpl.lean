import EthLibImpl.Cryptography.Bls.Signatures
import EthLibImpl.Cryptography.Bls.Exports
import EthLib.Cryptography.Exports.Bls
import EthLibImpl.Cryptography.Proofs.Bls.CompressG1
import EthLibImpl.Cryptography.Proofs.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.SigMath

/-!
# Proofs: the implementation's signature layer is the mirror's, and its exports the spec's

`EthLibImpl.Cryptography.Bls.Signatures` equals its mirror
(`Mirror.Signatures`), hence, with `SigMath`, the spec. The only part that
touches G2, hashing and pairing is `coreVerifyPoint`; its correspondence is
the hypothesis `CoreVerifyHyp`. Everything else (key validation, the
aggregation loops, the compressed aggregate key) is proven here.

The spec's signature functions take typed keys and signatures, and its exports
(`EthLib.Cryptography.Exports.Bls`) read the bytes into those types first. The
implementation takes bytes of any size. Sections 5 and 6 relate the two:

* `ethAggregatePubkeys_eq_spec` and `ethFastAggregateVerify_eq_spec`: the
  implementation's functions, behind its own size check where it has one,
  against the spec's reading of the bytes followed by its typed function.
* `ethAggregatePubkeysExport_eq_spec` and `ethFastAggregateVerifyExport_eq_spec`:
  the implementation's exports (`EthLibImpl.Cryptography.Bls.Exports`) are the
  spec's, as functions of their byte inputs.
-/

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls.Signatures

open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Bls (BlsError)
open EthLib.Base (packBytes)

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
    have hv := (SpecG1.uncompress_valid b _ hs).1
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
        simp only [h1, h1', ite_true]
        rfl
      · have h1' : ¬ (G1.toSpec q).isInfinity = true := hinf ▸ h1
        rw [hsub]
        by_cases h2 : Mirror.Signatures.g1InSubgroup (G1.toSpec q) = true
        · simp only [h1, h1', h2]; rfl
        · simp only [h1, h1', h2]; rfl
    · intro p hp
      simp only [validatedPubkey, hu, hb] at hp
      by_cases h1 : q.isInfinity = true
      · simp only [h1, ite_true] at hp; cases hp
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

/-- Two folds whose steps keep related states related end in related results. -/
theorem foldlM_sim {ε α β β' : Type} (inv : β → β' → Prop) (f : β → α → Except ε β)
    (f' : β' → α → Except ε β')
    (hstep : ∀ a b b', inv b b' → ExceptRel inv (f b a) (f' b' a)) :
    ∀ (l : List α) (b : β) (b' : β'), inv b b' → ExceptRel inv (l.foldlM f b) (l.foldlM f' b')
  | [], _, _, h => h
  | a :: l, b, b', h => by
    rw [List.foldlM_cons, List.foldlM_cons]
    have hs := hstep a b b' h
    cases h1 : f b a with
    | error e =>
      cases h2 : f' b' a with
      | error e' => rw [h1, h2] at hs; exact hs
      | ok y' => rw [h1, h2] at hs; exact hs.elim
    | ok y =>
      cases h2 : f' b' a with
      | error e' => rw [h1, h2] at hs; exact hs.elim
      | ok y' =>
        rw [h1, h2] at hs
        exact foldlM_sim inv f f' hstep l y y' hs

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
  · rw [ite_eq_left hsz, ite_eq_left hsz]; rfl
  · rw [ite_eq_right hsz, ite_eq_right hsz]
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
  · rw [ite_eq_left he, ite_eq_left he]
  · rw [ite_eq_right he, ite_eq_right he]
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

/-! ## 4. `fastAggregateVerify`

As in `SigMath`: the implementation's `fastAggregateVerify` is an instance of a copy of it with
key validation and the final check abstract (`fastAggregateVerifyPI`), so the kernel never
compares a reduced loop result with an unreduced `coreVerifyPoint`. -/

/-- The implementation's `fastAggregateVerify`, with key validation and the final check
abstract. -/
def fastAggregateVerifyPI (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (pubkeys : Array ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 then return false
    match V pk with
    | .error _ => return false
    | .ok p => agg := G1.add agg p
  return C agg

theorem fastAggregateVerify_eq_PI (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig
      = fastAggregateVerifyPI validatedPubkey (coreVerifyPoint · msg sig) pks :=
  rfl

/-- The loop body of `fastAggregateVerifyPI`. -/
def stepI (V : ByteArray → Except BlsError G1) (pk : ByteArray) (r : Option Bool × G1) :
    Id (ForInStep (Option Bool × G1)) :=
  if pk.size ≠ 48 then pure (.done (some false, r.2))
  else match V pk with
    | .error _ => pure (.done (some false, r.2))
    | .ok p => pure (.yield (none, G1.add r.2 p))

theorem fastAggregateVerifyPI_unfold (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (pks : Array ByteArray) :
    fastAggregateVerifyPI V C pks =
      if pks.isEmpty = true then false
      else Mirror.Signatures.finishMP C (forIn pks (none, G1.zero) (stepI V)).run := by
  unfold fastAggregateVerifyPI
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
    rfl
  · rw [ite_eq_right he, ite_eq_right he]
    dsimp only
    change Id.run ((forIn pks ((none : Option Bool), (G1.zero : G1)) (stepI V)) >>= _) = _
    generalize forIn (m := Id) pks (none, G1.zero) (stepI V) = X
    rcases X with ⟨_ | b, g⟩ <;> rfl

theorem finishMP_forIn_impl (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (l : List ByteArray) (acc : G1) :
    Mirror.Signatures.finishMP C (forIn l (none, acc) (stepI V)).run =
      match l.foldlM (Mirror.Signatures.stepFP V G1.add) acc with
      | .ok agg => C agg
      | .error _ => false := by
  induction l generalizing acc with
  | nil => rfl
  | cons pk l ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    unfold stepI Mirror.Signatures.stepFP
    by_cases hsz : pk.size ≠ 48
    · rw [ite_eq_left hsz, ite_eq_left hsz]
      rfl
    · rw [ite_eq_right hsz, ite_eq_right hsz]
      cases V pk with
      | error e => rfl
      | ok p => exact ih (G1.add acc p)

/-- The implementation's `fastAggregateVerify`, as a fold over the keys. -/
theorem fastAggregateVerify_fold (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig =
      if pks.isEmpty = true then false
      else match pks.toList.foldlM (Mirror.Signatures.stepFP validatedPubkey G1.add) G1.zero with
        | .ok agg => coreVerifyPoint agg msg sig
        | .error _ => false := by
  rw [fastAggregateVerify_eq_PI, fastAggregateVerifyPI_unfold, ← Array.forIn_toList,
    finishMP_forIn_impl]

theorem stepFP_rel (pk : ByteArray) (g : G1) (g' : EthLib.Cryptography.Bls.G1)
    (h : AggRel g g') :
    ExceptRel AggRel (Mirror.Signatures.stepFP validatedPubkey G1.add g pk)
      (Mirror.Signatures.stepFP Mirror.Signatures.validatedPubkey
        EthLib.Cryptography.Bls.G1.add g' pk) := by
  unfold Mirror.Signatures.stepFP
  by_cases hsz : pk.size ≠ 48
  · rw [ite_eq_left hsz, ite_eq_left hsz]
    exact rfl
  · rw [ite_eq_right hsz, ite_eq_right hsz]
    obtain ⟨hm, hc⟩ := validatedPubkey_spec pk
    cases hv : validatedPubkey pk with
    | error e =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pk = .error e := hm.symm
      rw [hm']
      exact rfl
    | ok p =>
      rw [hv] at hm
      have hm' : Mirror.Signatures.validatedPubkey pk = .ok (G1.toSpec p) := hm.symm
      rw [hm']
      obtain ⟨hac, has⟩ := G1.add_spec h.1 (hc p hv)
      show AggRel (G1.add g p) (EthLib.Cryptography.Bls.G1.add g' (G1.toSpec p))
      exact ⟨hac, by rw [has, h.2]⟩

/-- **`fastAggregateVerify` of the implementation is the mirror's**, given `coreVerifyPoint`. -/
theorem fastAggregateVerify_eq (hcv : CoreVerifyHyp) (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig = Mirror.Signatures.fastAggregateVerify pks msg sig := by
  rw [fastAggregateVerify_fold, Mirror.Signatures.fastAggregateVerify_fold]
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
  · rw [ite_eq_right he, ite_eq_right he]
    have hl := foldlM_sim AggRel _ _ (fun pk g g' h => stepFP_rel pk g g' h) pks.toList G1.zero
      EthLib.Cryptography.Bls.G1.zero ⟨G1.zero_spec.1, G1.zero_spec.2⟩
    generalize pks.toList.foldlM (Mirror.Signatures.stepFP validatedPubkey G1.add) G1.zero = r
      at hl ⊢
    generalize pks.toList.foldlM (Mirror.Signatures.stepFP Mirror.Signatures.validatedPubkey
      EthLib.Cryptography.Bls.G1.add) EthLib.Cryptography.Bls.G1.zero = r' at hl ⊢
    cases r with
    | error e =>
      cases r' with
      | error e' => rfl
      | ok y' => exact hl.elim
    | ok y =>
      cases r' with
      | error e' => exact hl.elim
      | ok y' =>
        obtain ⟨hc, hs⟩ := hl
        show coreVerifyPoint y msg sig = Mirror.Signatures.coreVerifyPoint y' msg sig
        rw [hcv y msg sig hc, hs]

/-- The two encodings of the G2 point at infinity are the same bytes. -/
theorem g2_infinity_eq :
    G2_POINT_AT_INFINITY = EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY := by
  decide

/-- **`ethFastAggregateVerify` of the implementation is the mirror's.** -/
theorem ethFastAggregateVerify_eq_mirror (hcv : CoreVerifyHyp)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig = Mirror.Signatures.ethFastAggregateVerify pks msg sig := by
  unfold ethFastAggregateVerify Mirror.Signatures.ethFastAggregateVerify
  rw [fastAggregateVerify_eq hcv, g2_infinity_eq]

/-! ## 5. Reading keys and signatures

The spec's exports read each key and the signature into its typed form
(`readPubkey`, `exactBytes?`); the implementation checks the sizes itself. -/

/-- Bytes read at their exact size are the bytes of the vector read. -/
theorem packBytes_of_exactBytes? {n : Nat} {b : ByteArray} {v : Vector UInt8 n}
    (h : EthLib.Cryptography.Bls.Exports.exactBytes? n b = some v) : packBytes v = b := by
  unfold EthLib.Cryptography.Bls.Exports.exactBytes? at h
  split at h
  · cases h
    rfl
  · cases h

/-- Bytes that are not read at a size have another size. -/
theorem size_of_exactBytes?_none {n : Nat} {b : ByteArray}
    (h : EthLib.Cryptography.Bls.Exports.exactBytes? n b = none) : b.size ≠ n := by
  unfold EthLib.Cryptography.Bls.Exports.exactBytes? at h
  split at h
  · cases h
  · assumption

/-- Keys all read at 48 bytes are the bytes of the keys read. -/
theorem list_mapM_exactBytes?_some {l : List ByteArray} {p : List EthLib.Cryptography.Bls.BLSPubkey}
    (h : l.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) = some p) :
    p.map packBytes = l := by
  induction l generalizing p with
  | nil =>
    cases h
    rfl
  | cons a l ih =>
    rw [List.mapM_cons] at h
    cases ha : EthLib.Cryptography.Bls.Exports.exactBytes? 48 a with
    | none =>
      rw [ha] at h
      cases h
    | some v =>
      rw [ha] at h
      cases hl : l.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) with
      | none =>
        rw [hl] at h
        cases h
      | some vs =>
        rw [hl] at h
        cases h
        rw [List.map_cons, packBytes_of_exactBytes? ha, ih hl]

/-- A key list that does not read at 48 bytes has a key of another size. -/
theorem list_mapM_exactBytes?_none {l : List ByteArray}
    (h : l.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) = none) :
    ∃ pk ∈ l, pk.size ≠ 48 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rw [List.mapM_cons] at h
    cases ha : EthLib.Cryptography.Bls.Exports.exactBytes? 48 a with
    | none => exact ⟨a, List.mem_cons_self, size_of_exactBytes?_none ha⟩
    | some v =>
      rw [ha] at h
      cases hl : l.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) with
      | none =>
        obtain ⟨pk, hpk, hs⟩ := ih hl
        exact ⟨pk, List.mem_cons_of_mem _ hpk, hs⟩
      | some vs =>
        rw [hl] at h
        cases h

theorem mapM_exactBytes?_some {pks : Array ByteArray} {p : Array EthLib.Cryptography.Bls.BLSPubkey}
    (h : pks.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) = some p) :
    p.map packBytes = pks := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : pks.toList.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) with
  | none =>
    rw [hl] at h
    cases h
  | some vs =>
    rw [hl] at h
    cases h
    apply Array.ext'
    rw [Array.toList_map, List.toList_toArray, list_mapM_exactBytes?_some hl]

theorem mapM_exactBytes?_none {pks : Array ByteArray}
    (h : pks.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) = none) :
    ∃ pk ∈ pks, pk.size ≠ 48 := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : pks.toList.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) with
  | none =>
    obtain ⟨pk, hpk, hs⟩ := list_mapM_exactBytes?_none hl
    exact ⟨pk, Array.mem_toList_iff.mp hpk, hs⟩
  | some vs =>
    rw [hl] at h
    cases h

/-- The implementation's size check of one key. -/
def sizeCheck (pk : ByteArray) : Except BlsError Unit :=
  if pk.size = 48 then pure () else throw (.badPubkeySize pk.size)

theorem checkPubkeySizes_eq (pks : Array ByteArray) :
    Exports.checkPubkeySizes pks = pks.toList.foldlM (fun _ => sizeCheck) () := by
  unfold Exports.checkPubkeySizes Array.forM
  rw [← Array.foldlM_toList]
  rfl

/-- Reading a key is the size check, then the bytes as a vector. -/
theorem readPubkey_eq (pk : ByteArray) :
    EthLib.Cryptography.Bls.Exports.readPubkey pk =
      if h : pk.size = 48 then .ok ⟨pk.data, h⟩ else .error (.badPubkeySize pk.size) := by
  unfold EthLib.Cryptography.Bls.Exports.readPubkey EthLib.Cryptography.Bls.Exports.exactBytes?
  by_cases h : pk.size = 48
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]

theorem list_foldlM_sizeCheck (l : List ByteArray) :
    l.foldlM (fun _ => sizeCheck) () =
      Except.map (fun _ => ()) (l.mapM EthLib.Cryptography.Bls.Exports.readPubkey) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldlM_cons, List.mapM_cons, readPubkey_eq]
    unfold sizeCheck
    by_cases h : a.size = 48
    · rw [ite_eq_left h, dite_eq_left h]
      show l.foldlM (fun _ => sizeCheck) () =
        Except.map (fun _ => ()) (l.mapM EthLib.Cryptography.Bls.Exports.readPubkey >>= fun bs =>
          pure (⟨a.data, h⟩ :: bs))
      rw [ih]
      cases l.mapM EthLib.Cryptography.Bls.Exports.readPubkey <;> rfl
    · rw [ite_eq_right h, dite_eq_right h]
      rfl

/-- The implementation's size check fails exactly where the spec's reading of the keys does,
with the same error. -/
theorem checkPubkeySizes_eq_map (pks : Array ByteArray) :
    Exports.checkPubkeySizes pks =
      Except.map (fun _ => ()) (pks.mapM EthLib.Cryptography.Bls.Exports.readPubkey) := by
  rw [checkPubkeySizes_eq, list_foldlM_sizeCheck, Array.mapM_eq_mapM_toList]
  cases pks.toList.mapM EthLib.Cryptography.Bls.Exports.readPubkey <;> rfl

theorem list_mapM_readPubkey_ok {l : List ByteArray} {p : List EthLib.Cryptography.Bls.BLSPubkey}
    (h : l.mapM EthLib.Cryptography.Bls.Exports.readPubkey = .ok p) : p.map packBytes = l := by
  induction l generalizing p with
  | nil =>
    cases h
    rfl
  | cons a l ih =>
    rw [List.mapM_cons, readPubkey_eq] at h
    by_cases ha : a.size = 48
    · rw [dite_eq_left ha] at h
      cases hl : l.mapM EthLib.Cryptography.Bls.Exports.readPubkey with
      | error e =>
        rw [hl] at h
        cases h
      | ok vs =>
        rw [hl] at h
        cases h
        rw [List.map_cons, ih hl]
        rfl
    · rw [dite_eq_right ha] at h
      cases h

/-- Keys that read are the bytes of the keys read. -/
theorem mapM_readPubkey_ok {pks : Array ByteArray} {p : Array EthLib.Cryptography.Bls.BLSPubkey}
    (h : pks.mapM EthLib.Cryptography.Bls.Exports.readPubkey = .ok p) : p.map packBytes = pks := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : pks.toList.mapM EthLib.Cryptography.Bls.Exports.readPubkey with
  | error e =>
    rw [hl] at h
    cases h
  | ok vs =>
    rw [hl] at h
    cases h
    apply Array.ext'
    rw [Array.toList_map, List.toList_toArray, list_mapM_readPubkey_ok hl]

/-! ## 6. End to end -/

/-- **`ethAggregatePubkeys`.** The implementation's size check followed by its
`ethAggregatePubkeys` is the spec's reading of the keys followed by its typed
`ethAggregatePubkeys`, errors included. -/
theorem ethAggregatePubkeys_eq_spec (pks : Array ByteArray) :
    (Exports.checkPubkeySizes pks >>= fun _ => ethAggregatePubkeys pks) =
      (pks.mapM EthLib.Cryptography.Bls.Exports.readPubkey >>= fun p =>
        (EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys p).map packBytes) := by
  rw [checkPubkeySizes_eq_map]
  cases hm : pks.mapM EthLib.Cryptography.Bls.Exports.readPubkey with
  | error e => rfl
  | ok p =>
    have hp : p.map packBytes = pks := mapM_readPubkey_ok hm
    show ethAggregatePubkeys pks =
      (EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys p).map packBytes
    rw [← hp, ethAggregatePubkeys_eq_mirror, Mirror.Signatures.ethAggregatePubkeys_eq]

/-- **`ethFastAggregateVerify`.** The implementation's `ethFastAggregateVerify` is the
spec's typed one on keys of 48 bytes and a signature of 96, and `false` otherwise (where the
spec's export answers `0`), given the `coreVerifyPoint`, pairing and hash-to-curve layers. -/
theorem ethFastAggregateVerify_eq_spec (hcv : CoreVerifyHyp)
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.Signatures.HashRel msg dst)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig =
      match pks.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48),
        EthLib.Cryptography.Bls.Exports.exactBytes? 96 sig with
      | some p, some s => EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify p msg s
      | _, _ => false := by
  rw [ethFastAggregateVerify_eq_mirror hcv]
  cases hp : pks.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) with
  | none =>
    exact Mirror.Signatures.ethFastAggregateVerify_of_size (Or.inl (mapM_exactBytes?_none hp)) msg
  | some p =>
    cases hs : EthLib.Cryptography.Bls.Exports.exactBytes? 96 sig with
    | none =>
      exact Mirror.Signatures.ethFastAggregateVerify_of_size
        (Or.inr (size_of_exactBytes?_none hs)) msg
    | some s =>
      rw [← mapM_exactBytes?_some hp, ← packBytes_of_exactBytes? hs]
      exact Mirror.Signatures.ethFastAggregateVerify_eq hpair hhash p msg s

/-- A computation whose result is mapped, under the implementation's `runBls`, is the spec's
export shape: the first step and the second each under the spec's `runBls`, then the map. -/
theorem runBls_bind_map {α β γ : Type} (x : Except BlsError α) (g : α → Except BlsError β)
    (h : β → γ) :
    Exports.runBls (x >>= fun a => (g a).map h) =
      (EthLib.Cryptography.Bls.Exports.runBls x >>= fun a => do
        let b ← EthLib.Cryptography.Bls.Exports.runBls (g a)
        pure (h b)) := by
  cases x with
  | error e => rfl
  | ok a =>
    show Exports.runBls ((g a).map h) =
      (EthLib.Cryptography.Bls.Exports.runBls (g a) >>= fun b => pure (h b))
    cases g a <;> rfl

/-- **`eth_aggregate_pubkeys`.** The implementation's export is the spec's. -/
theorem ethAggregatePubkeysExport_eq_spec (pks : Array ByteArray) :
    Exports.ethAggregatePubkeysExport pks
      = EthLib.Cryptography.Bls.Exports.ethAggregatePubkeysExport pks := by
  unfold Exports.ethAggregatePubkeysExport EthLib.Cryptography.Bls.Exports.ethAggregatePubkeysExport
  rw [show (do Exports.checkPubkeySizes pks; ethAggregatePubkeys pks
      : Except BlsError ByteArray) = (Exports.checkPubkeySizes pks >>= fun _ => ethAggregatePubkeys pks)
      from rfl, ethAggregatePubkeys_eq_spec]
  exact runBls_bind_map _ _ _

/-- **`eth_fast_aggregate_verify`.** The implementation's export is the spec's, given the
`coreVerifyPoint`, pairing and hash-to-curve layers. -/
theorem ethFastAggregateVerifyExport_eq_spec (hcv : CoreVerifyHyp)
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.Signatures.HashRel msg dst)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    Exports.ethFastAggregateVerifyExport pks msg sig
      = EthLib.Cryptography.Bls.Exports.ethFastAggregateVerifyExport pks msg sig := by
  unfold Exports.ethFastAggregateVerifyExport
    EthLib.Cryptography.Bls.Exports.ethFastAggregateVerifyExport
    EthLib.Cryptography.Bls.Exports.checkSized
  rw [ethFastAggregateVerify_eq_spec hcv hpair hhash]
  cases pks.mapM (EthLib.Cryptography.Bls.Exports.exactBytes? 48) <;>
    cases EthLib.Cryptography.Bls.Exports.exactBytes? 96 sig <;> rfl

end EthLibImpl.Cryptography.Bls.Signatures
