import EthLibImpl.Cryptography.Proofs.Bls.MirrorSig
import EthLibImpl.Cryptography.Proofs.Bls.G2Subgroup
import EthLibImpl.Cryptography.Proofs.Bls.G1Endo
import EthLibImpl.Cryptography.Proofs.Bls.G2Proj
import EthLib.Cryptography.Proofs.Bls.KeyValidate
import EthLib.Cryptography.Proofs.Bls.PairingCongr

/-!
# Proofs: the implementation's signature functions return the spec's

`EthLibImpl.Cryptography.Bls.Mirror.Signatures` restates the
implementation's signature layer over spec types (see `MirrorSig`). Its
functions take keys and signatures as bytes of any size; the spec's
`EthLib.Cryptography.Bls.Signatures` takes them typed (`BLSPubkey`,
`BLSSignature`), and its exports check the sizes. This file proves:

* `ethAggregatePubkeys_eq`: on keys of the right size (`pks.map packBytes`),
  the mirror's `ethAggregatePubkeys` is the spec's, errors included.
* `ethFastAggregateVerify_eq`: on a key list and a signature of the right
  sizes, the mirror's `ethFastAggregateVerify` is the spec's, given that the
  mirrored pairing check and hash-to-curve agree with the spec's (hypotheses
  `hpair` and `hhash`, proven in their own files).
* `ethFastAggregateVerify_of_size`: on a key or a signature of another size,
  the mirror's `ethFastAggregateVerify` is `false`, as the spec's export is.

The steps:

1. `g1InSubgroup_eq`: the implementation's endomorphism subgroup test is the
   spec's `G1.inSubgroup` on valid points (`SpecG1.inSubgroup_eq_endo`), so
   `validatedPubkey_eq`: the mirror's key validation is the spec's
   `G1.keyValidatePoint`.
2. `coreVerify_compress`: the spec verifies the *compressed* aggregate key,
   which it decodes back into another Jacobian triple; the mirror verifies the
   aggregate point directly. They agree when the aggregate is a valid point of
   the `r`-torsion subgroup (`G1.uncompress_compress`,
   `G1.keyValidatePoint_eq_ok_iff`), since the pairing check reads its points
   only through their group elements (`pairingCheck_congr_two_g1` here,
   `pairingCheck_congr_two_g2` in `G2Proj`).
3. The aggregation loops: each mirror loop is the spec's
   `zipIdx.foldlM addPubkeyPoint` (by induction on the key list), and every
   accumulator that fold produces is a sum of subgroup points, which 2 needs.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.Signatures

open EthLib.Cryptography.Bls
open EthLib.Base (packBytes)

/-! ## Bytes of typed keys and signatures -/

/-- The bytes of a vector built from a byte array are that byte array. -/
theorem bytes_of_vector {n : Nat} (b : ByteArray) (h : b.data.size = n) :
    packBytes (⟨b.data, h⟩ : Vector UInt8 n) = b :=
  rfl

/-- The bytes of the public key of a point are its compression. -/
theorem packBytes_pointToPubkey (p : G1) :
    packBytes (EthLib.Cryptography.Bls.Signatures.pointToPubkey p) = G1.compress p := by
  unfold EthLib.Cryptography.Bls.Signatures.pointToPubkey
  exact bytes_of_vector _ _

/-- A typed key has 48 bytes. -/
theorem size_packBytes {n : Nat} (v : Vector UInt8 n) : (packBytes v).size = n :=
  v.size_toArray

/-! ## 1. Subgroup test and key validation -/

/-- The endomorphism subgroup test is the spec's `G1.inSubgroup` on valid points. -/
theorem g1InSubgroup_eq {p : G1} (h : G1.Valid p) : g1InSubgroup p = G1.inSubgroup p := by
  rw [g1InSubgroup, SpecG1.inSubgroup_eq_endo h]

/-- Key validation's control flow, with its two tests abstract (so the kernel never unfolds
them). -/
def keyValidatePointP {α : Type} (isInf inSub : α → Bool) (u : Except BlsError α) :
    Except BlsError α := do
  let p ← u
  if isInf p then throw .pointAtInfinity
  if !inSub p then throw .notInSubgroup
  return p

theorem validatedPubkey_eq_P (b : ByteArray) :
    validatedPubkey b = keyValidatePointP G1.isInfinity g1InSubgroup (G1.uncompress b) :=
  rfl

theorem keyValidatePoint_eq_P (b : ByteArray) :
    G1.keyValidatePoint b = keyValidatePointP G1.isInfinity G1.inSubgroup (G1.uncompress b) :=
  rfl

theorem keyValidatePointP_congr {α : Type} (isInf inSub inSub' : α → Bool)
    (u : Except BlsError α) (h : ∀ p, u = .ok p → inSub p = inSub' p) :
    keyValidatePointP isInf inSub u = keyValidatePointP isInf inSub' u := by
  cases u with
  | error e => rfl
  | ok p =>
    have hp := h p rfl
    simp only [keyValidatePointP, bind, Except.bind, hp]

/-- The mirror's one-pass key validation is the spec's `keyValidatePoint`. -/
theorem validatedPubkey_eq (b : ByteArray) : validatedPubkey b = G1.keyValidatePoint b := by
  rw [validatedPubkey_eq_P, keyValidatePoint_eq_P]
  exact keyValidatePointP_congr _ _ _ _ fun p hu => g1InSubgroup_eq (G1.uncompress_valid hu)

/-! ## 2. Verifying the compressed aggregate -/

/-- The hash-to-curve hypothesis: the mirror's `hashToG2` and the spec's fail with the same
error, or return triples for the same point (`G2.ProjEq`, equal up to Jacobian scaling).
`Mirror.HashToCurve.hashToG2_rel` proves it. -/
def HashRel (msg dst : ByteArray) : Prop :=
  (∃ e, EthLib.Cryptography.Bls.HashToCurve.hashToG2 (F := Fp) msg dst = .error e ∧
      Mirror.HashToCurve.hashToG2 msg dst = .error e) ∨
    ∃ P Q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 (F := Fp) msg dst = .ok P ∧
      Mirror.HashToCurve.hashToG2 msg dst = .ok Q ∧ G2.ProjEq P Q

/-- `pairingCheck` on two pairs reads the second `G1` point only through its group element. -/
theorem pairingCheck_congr_two_g1 (a : G1 × G2) {p p' : G1} (h : G2) (hp : G1.Valid p)
    (hp' : G1.Valid p') (he : G1.toPoint p = G1.toPoint p') :
    EthLib.Cryptography.Bls.pairingCheck #[a, (p, h)]
      = EthLib.Cryptography.Bls.pairingCheck #[a, (p', h)] := by
  have hf : pairFactor (p, h) = pairFactor (p', h) := by
    unfold pairFactor
    dsimp only
    rw [(G1.toAffine_congr hp hp' he).1, (G1.toAffine_congr hp hp' he).2]
  rw [pairingCheck_eq_finalExp_prod, pairingCheck_eq_finalExp_prod]
  simp only [List.filterMap_cons, List.filterMap_nil, hf]

/-- The accumulator invariant: a valid point of the `r`-torsion subgroup. -/
def Good (g : G1) : Prop := G1.Valid g ∧ Fr.modulus • G1.toPoint g = 0

theorem good_zero : Good G1.zero := by
  refine ⟨G1.valid_zero, ?_⟩
  rw [G1.toPoint_zero, nsmul_zero]

theorem good_add {a b : G1} (ha : Good a) (hb : Good b) : Good (G1.add a b) := by
  refine ⟨G1.valid_add ha.1 hb.1, ?_⟩
  rw [G1.toPoint_add ha.1 hb.1, nsmul_add, ha.2, hb.2, add_zero]

/-- The spec verifies the compressed aggregate key, which it decodes into
another triple for the same group element; the mirror verifies the
aggregate point itself. They agree on a valid point of the `r`-torsion
subgroup. -/
theorem coreVerify_compress {agg : G1} (hg : Good agg)
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, HashRel msg dst)
    (msg : ByteArray) (sig : BLSSignature) :
    EthLib.Cryptography.Bls.Signatures.coreVerify (G1.compress agg) msg (packBytes sig)
        EthLib.Cryptography.Bls.Signatures.DST
      = coreVerifyPoint agg msg (packBytes sig) := by
  have hsz : (packBytes sig).size = 96 := size_packBytes sig
  obtain ⟨q, hq, hqp⟩ := G1.uncompress_compress hg.1
  have hqv := G1.uncompress_valid hq
  unfold EthLib.Cryptography.Bls.Signatures.coreVerify coreVerifyPoint
  by_cases hinf : agg.isInfinity = true
  · -- The compressed point at infinity fails key validation.
    have hk : ∀ P, G1.keyValidatePoint (G1.compress agg) ≠ .ok P := by
      intro P hP
      obtain ⟨hu, -, hne, -⟩ := G1.keyValidatePoint_eq_ok_iff.mp hP
      rw [hq] at hu
      cases hu
      exact hne (hqp.trans ((G1.isInfinity_eq_true_iff_toPoint_eq_zero hg.1).mp hinf))
    rw [ite_eq_left hinf]
    cases hkv : G1.keyValidatePoint (G1.compress agg) with
    | ok P => exact absurd hkv (hk P)
    | error e =>
      cases hU : G2.uncompress (packBytes sig) with
      | error e' => rfl
      | ok r =>
        dsimp only
        exact Bool.and_false _
  · have hne : G1.toPoint q ≠ 0 := fun h0 =>
      hinf ((G1.isInfinity_eq_true_iff_toPoint_eq_zero hg.1).mpr (hqp.symm.trans h0))
    have hk : G1.keyValidatePoint (G1.compress agg) = .ok q :=
      G1.keyValidatePoint_eq_ok_iff.mpr ⟨hq, hqv, hne, by rw [hqp]; exact hg.2⟩
    rw [ite_eq_right hinf, ite_eq_right (fun h => h hsz), hk]
    cases hU : G2.uncompress (packBytes sig) with
    | error e => rfl
    | ok r =>
      have hsub : Mirror.G2.inSubgroup r = EthLib.Cryptography.Bls.Signatures.signatureSubgroupCheck r :=
        Mirror.G2.inSubgroup_eq (G2.valid_of_uncompress hU)
      rcases hhash msg EthLib.Cryptography.Bls.Signatures.DST with
        ⟨e, hs, hm⟩ | ⟨P, Q, hs, hm, hp⟩
      · rw [hs, hm]
        dsimp only
        rw [hsub, Bool.and_false]
        cases EthLib.Cryptography.Bls.Signatures.signatureSubgroupCheck r <;> rfl
      · rw [hs, hm]
        dsimp only
        rw [hsub]
        have hneg : G1.toPoint (G1.neg q) = G1.toPoint (G1.neg agg) := by
          rw [G1.toPoint_neg hqv, G1.toPoint_neg hg.1, hqp]
        rw [hpair, pairingCheck_congr_two_g1 _ P (G1.valid_neg hqv) (G1.valid_neg hg.1) hneg,
          pairingCheck_congr_two_g2 _ _ hp]
        cases EthLib.Cryptography.Bls.Signatures.signatureSubgroupCheck r
        · rfl
        · rw [Bool.true_and, ite_eq_right (show ¬ ((!true) = true) from Bool.false_ne_true)]


/-! ## 3. The aggregation loops

The mirror's two loops, once their `do` sugar is unfolded, run the step functions
below (`*_unfold` are `rfl`). On keys of the right size, each loop is the spec's
`zipIdx.foldlM addPubkeyPoint`. -/

/-- The spec's `aggregatePubkeyPoint`, unfolded. -/
theorem aggregatePubkeyPoint_unfold (pks : Array BLSPubkey) :
    EthLib.Cryptography.Bls.Signatures.aggregatePubkeyPoint pks =
      if pks.isEmpty = true then throw .emptyPubkeyList
      else pks.zipIdx.foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint G1.zero :=
  rfl

theorem isEmpty_map {α β : Type} (f : α → β) (xs : Array α) : (xs.map f).isEmpty = xs.isEmpty := by
  unfold Array.isEmpty
  rw [Array.size_map]

/-- Adding a typed key is validating its bytes. -/
theorem addPubkeyPoint_eq (agg : G1) (pk : BLSPubkey) (i : Nat) :
    EthLib.Cryptography.Bls.Signatures.addPubkeyPoint agg (pk, i) =
      match G1.keyValidatePoint (packBytes pk) with
      | .error _ => .error (.invalidPubkey (some i))
      | .ok p => .ok (G1.add agg p) := by
  unfold EthLib.Cryptography.Bls.Signatures.addPubkeyPoint
  dsimp only
  cases G1.keyValidatePoint (packBytes pk) <;> rfl

/-- Every accumulator of the spec's key fold is a valid point of the `r`-torsion subgroup. -/
theorem foldlM_addPubkeyPoint_good (l : List (BLSPubkey × Nat)) {acc agg : G1} (hacc : Good acc)
    (h : l.foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint acc = .ok agg) : Good agg := by
  induction l generalizing acc with
  | nil =>
    cases h
    exact hacc
  | cons e l ih =>
    obtain ⟨pk, i⟩ := e
    rw [List.foldlM_cons, addPubkeyPoint_eq] at h
    cases hk : G1.keyValidatePoint (packBytes pk) with
    | error e =>
      rw [hk] at h
      cases h
    | ok p =>
      rw [hk] at h
      obtain ⟨-, hv, -, hr⟩ := G1.keyValidatePoint_eq_ok_iff.mp hk
      exact ih (good_add hacc ⟨hv, hr⟩) h

/-! ### `ethAggregatePubkeys` -/

/-- The mirror's `ethAggregatePubkeys` loop body. -/
def stepAM (pks : Array ByteArray) (i : Nat) (agg : G1) : Except BlsError (ForInStep G1) :=
  if pks[i]!.size ≠ 48 then throw (.badPubkeySize pks[i]!.size)
  else match validatedPubkey pks[i]! with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => pure (.yield (G1.add agg p))

theorem ethAggregatePubkeys_unfold (pks : Array ByteArray) :
    ethAggregatePubkeys pks =
      if pks.isEmpty = true then throw .emptyPubkeyList
      else (forIn [:pks.size] G1.zero (stepAM pks)) >>= fun agg => pure (G1.compress agg) :=
  rfl

/-- On keys of the right size, the mirror's range loop is the spec's key fold. -/
theorem forIn_stepAM (P : Array ByteArray) (l : List BLSPubkey) (s : Nat) (acc : G1)
    (hP : ∀ j (hj : j < l.length), P[s + j]! = packBytes l[j]) :
    forIn (List.range' s l.length) acc (stepAM P)
      = (l.zipIdx s).foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint acc := by
  induction l generalizing s acc with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range'_succ, List.zipIdx_cons, List.forIn_cons, List.foldlM_cons,
      addPubkeyPoint_eq]
    have ha : P[s]! = packBytes a := hP 0 (Nat.succ_pos _)
    have hstep : stepAM P s acc =
        match G1.keyValidatePoint (packBytes a) with
        | .error _ => .error (.invalidPubkey (some s))
        | .ok p => .ok (.yield (G1.add acc p)) := by
      unfold stepAM
      rw [ha, ite_eq_right (fun h => h (size_packBytes a)), validatedPubkey_eq]
      cases G1.keyValidatePoint (packBytes a) <;> rfl
    rw [hstep]
    cases G1.keyValidatePoint (packBytes a) with
    | error e => rfl
    | ok p =>
      refine ih (s + 1) (G1.add acc p) (fun j hj => ?_)
      have := hP (j + 1) (Nat.succ_lt_succ hj)
      rw [show s + (j + 1) = s + 1 + j by omega] at this
      exact this

/-- **Main theorem (`eth_aggregate_pubkeys`).** On keys of the right size, the mirror's
`ethAggregatePubkeys` returns the bytes of the spec's result, errors included. -/
theorem ethAggregatePubkeys_eq (pks : Array BLSPubkey) :
    ethAggregatePubkeys (pks.map packBytes)
      = (EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks).map packBytes := by
  rw [ethAggregatePubkeys_unfold]
  unfold EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys
  rw [aggregatePubkeyPoint_unfold, isEmpty_map]
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
    rfl
  · rw [ite_eq_right he, ite_eq_right he, Array.size_map, Std.Legacy.Range.forIn_eq_forIn_range']
    have hsz : ([:pks.size] : Std.Legacy.Range).size = pks.toList.length := by
      simp [Std.Legacy.Range.size]
    rw [hsz, show ([:pks.size] : Std.Legacy.Range).start = 0 from rfl,
      show ([:pks.size] : Std.Legacy.Range).step = 1 from rfl,
      forIn_stepAM _ pks.toList 0 G1.zero (fun j hj => ?_), ← Array.toList_zipIdx,
      Array.foldlM_toList]
    · cases pks.zipIdx.foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint G1.zero with
      | error e => rfl
      | ok agg =>
        show Except.ok (G1.compress agg) = Except.ok (packBytes _)
        rw [packBytes_pointToPubkey]
    · have hj' : j < pks.size := hj
      rw [Nat.zero_add, getElem!_pos (pks.map packBytes) j (by rw [Array.size_map]; exact hj'),
        Array.getElem_map, Array.getElem_toList]

/-! ### `fastAggregateVerify`

`fastAggregateVerifyP` is the mirror's `fastAggregateVerify` with its key validation `V` and
its final verification `C` as parameters, written with the same `do` code, so the mirror's is
an instance of it by `rfl` (the loop's `match` reuses the mirror's matcher, which is why the
point type stays `G1`; `SigImpl` has the same for the implementation's points). Every other
lemma is stated over these parameters: with `C` a variable, the kernel never has to compare a
reduced loop result against an unreduced `coreVerifyPoint` (which makes it unfold
`coreVerifyPoint`, a deep recursion through the Montgomery field). -/

/-- The mirror's `fastAggregateVerify`, with key validation and the final check abstract. -/
def fastAggregateVerifyP (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (pubkeys : Array ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 then return false
    match V pk with
    | .error _ => return false
    | .ok p => agg := G1.add agg p
  return C agg

theorem fastAggregateVerify_eq_P (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig
      = fastAggregateVerifyP validatedPubkey (coreVerifyPoint · msg sig) pks :=
  rfl

/-- The loop body of `fastAggregateVerifyP`. -/
def stepMP (V : ByteArray → Except BlsError G1) (pk : ByteArray) (r : Option Bool × G1) :
    Id (ForInStep (Option Bool × G1)) :=
  if pk.size ≠ 48 then pure (.done (some false, r.2))
  else match V pk with
    | .error _ => pure (.done (some false, r.2))
    | .ok p => pure (.yield (none, G1.add r.2 p))

/-- What a `fastAggregateVerify` loop does with its final state. -/
def finishMP {γ : Type} (C : γ → Bool) (r : Option Bool × γ) : Bool :=
  match r.1 with
  | some a => a
  | none => C r.2

theorem fastAggregateVerifyP_unfold (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (pks : Array ByteArray) :
    fastAggregateVerifyP V C pks =
      if pks.isEmpty = true then false
      else finishMP C (forIn pks (none, G1.zero) (stepMP V)).run := by
  unfold fastAggregateVerifyP
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
    rfl
  · rw [ite_eq_right he, ite_eq_right he]
    dsimp only
    -- The loop's final `match` is core's `Break.runK.match_1`, which the elaborator does not
    -- unfold on a variable: destructure the loop's result first.
    change Id.run ((forIn pks ((none : Option Bool), (G1.zero : G1)) (stepMP V)) >>= _) = _
    generalize forIn (m := Id) pks (none, G1.zero) (stepMP V) = X
    rcases X with ⟨_ | b, g⟩ <;> rfl

/-- A `fastAggregateVerify` loop as a fold that stops at the first key that fails. -/
def stepFP {γ : Type} (V : ByteArray → Except BlsError γ) (add : γ → γ → γ) (agg : γ)
    (pk : ByteArray) : Except Unit γ :=
  if pk.size ≠ 48 then .error ()
  else match V pk with
    | .error _ => .error ()
    | .ok p => .ok (add agg p)

theorem finishMP_forIn (V : ByteArray → Except BlsError G1) (C : G1 → Bool)
    (l : List ByteArray) (acc : G1) :
    finishMP C (forIn l (none, acc) (stepMP V)).run =
      match l.foldlM (stepFP V G1.add) acc with
      | .ok agg => C agg
      | .error _ => false := by
  induction l generalizing acc with
  | nil => rfl
  | cons pk l ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    unfold stepMP stepFP
    by_cases hsz : pk.size ≠ 48
    · rw [ite_eq_left hsz, ite_eq_left hsz]
      rfl
    · rw [ite_eq_right hsz, ite_eq_right hsz]
      cases V pk with
      | error e => rfl
      | ok p => exact ih (G1.add acc p)

/-- The mirror's `fastAggregateVerify`, as a fold over the keys. -/
theorem fastAggregateVerify_fold (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig =
      if pks.isEmpty = true then false
      else match pks.toList.foldlM (stepFP validatedPubkey G1.add) G1.zero with
        | .ok agg => coreVerifyPoint agg msg sig
        | .error _ => false := by
  rw [fastAggregateVerify_eq_P, fastAggregateVerifyP_unfold, ← Array.forIn_toList,
    finishMP_forIn]

/-- On keys of the right size, the mirror's fold fails exactly when the spec's does. -/
theorem foldlM_stepF_map (l : List BLSPubkey) (s : Nat) (acc : G1) :
    (l.map packBytes).foldlM (stepFP validatedPubkey G1.add) acc
      = ((l.zipIdx s).foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint acc).mapError
          fun _ => () := by
  induction l generalizing s acc with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.zipIdx_cons, List.foldlM_cons, List.foldlM_cons, addPubkeyPoint_eq]
    unfold stepFP
    rw [ite_eq_right (fun h => h (size_packBytes a)), validatedPubkey_eq]
    cases G1.keyValidatePoint (packBytes a) with
    | error e => rfl
    | ok p => exact ih (s + 1) (G1.add acc p)

/-- A key of another size makes the mirror's fold fail. -/
theorem foldlM_stepF_size {l : List ByteArray} (h : ∃ pk ∈ l, pk.size ≠ 48) (acc : G1) :
    ∃ e, l.foldlM (stepFP validatedPubkey G1.add) acc = .error e := by
  induction l generalizing acc with
  | nil => simp at h
  | cons pk l ih =>
    rw [List.foldlM_cons]
    unfold stepFP
    by_cases hsz : pk.size ≠ 48
    · rw [ite_eq_left hsz]
      exact ⟨(), rfl⟩
    · rw [ite_eq_right hsz]
      have hl : ∃ pk ∈ l, pk.size ≠ 48 := by
        obtain ⟨x, hx, hxs⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hxs hsz
        · exact ⟨x, hx, hxs⟩
      cases validatedPubkey pk with
      | error e => exact ⟨(), rfl⟩
      | ok p => exact ih hl (G1.add acc p)

/-- **Main theorem (FastAggregateVerify).** On keys and a signature of the right sizes, the
mirrored implementation returns the spec's answer, given the pairing and hash-to-curve
layers. -/
theorem fastAggregateVerify_eq
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, HashRel msg dst)
    (pks : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) :
    fastAggregateVerify (pks.map packBytes) msg (packBytes sig)
      = EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg sig := by
  rw [fastAggregateVerify_fold]
  unfold EthLib.Cryptography.Bls.Signatures.fastAggregateVerify
    EthLib.Cryptography.Bls.Signatures.verify
  rw [aggregatePubkeyPoint_unfold, isEmpty_map]
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
    rfl
  · rw [ite_eq_right he, ite_eq_right he, Array.toList_map, foldlM_stepF_map _ 0,
      ← Array.toList_zipIdx, Array.foldlM_toList]
    cases h : pks.zipIdx.foldlM EthLib.Cryptography.Bls.Signatures.addPubkeyPoint G1.zero with
    | error e => rfl
    | ok agg =>
      have hg : Good agg := by
        rw [← Array.foldlM_toList] at h
        exact foldlM_addPubkeyPoint_good _ good_zero h
      show coreVerifyPoint agg msg (packBytes sig)
        = EthLib.Cryptography.Bls.Signatures.coreVerify
            (packBytes (EthLib.Cryptography.Bls.Signatures.pointToPubkey agg)) msg (packBytes sig)
            EthLib.Cryptography.Bls.Signatures.DST
      rw [packBytes_pointToPubkey]
      exact (coreVerify_compress hg hpair hhash msg sig).symm

/-- The signature of the point at infinity, as bytes, is the encoding of the point at
infinity. -/
theorem packBytes_eq_infinity_iff (sig : BLSSignature) :
    packBytes sig = EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY
      ↔ sig = EthLib.Cryptography.Bls.Signatures.infinitySignature := by
  rw [← Vector.toArray_inj]
  constructor
  · intro h
    show sig.toArray = EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY.data
    rw [← h]
    rfl
  · intro h
    show (⟨sig.toArray⟩ : ByteArray) = _
    rw [h]
    rfl

/-- **Main theorem (`eth_fast_aggregate_verify`).** On keys and a signature of the right
sizes, the mirror's `ethFastAggregateVerify` is the spec's. -/
theorem ethFastAggregateVerify_eq
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, HashRel msg dst)
    (pks : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) :
    ethFastAggregateVerify (pks.map packBytes) msg (packBytes sig)
      = EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig := by
  unfold ethFastAggregateVerify EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify
  rw [isEmpty_map]
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he, ite_eq_left he]
    exact decide_eq_decide.mpr (packBytes_eq_infinity_iff sig)
  · rw [ite_eq_right he, ite_eq_right he, fastAggregateVerify_eq hpair hhash]

/-- The encoding of the `G2` point at infinity has 96 bytes. -/
theorem size_G2_POINT_AT_INFINITY :
    EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY.size = 96 := by
  simp [EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY, G2.infinityBytes,
    ByteArray.size]

/-- **Wrong sizes.** On a key of another size than 48 bytes, or a signature of another size
than 96, the mirror's `ethFastAggregateVerify` is `false`. -/
theorem ethFastAggregateVerify_of_size {pks : Array ByteArray} {sig : ByteArray}
    (h : (∃ pk ∈ pks, pk.size ≠ 48) ∨ sig.size ≠ 96) (msg : ByteArray) :
    ethFastAggregateVerify pks msg sig = false := by
  unfold ethFastAggregateVerify
  by_cases he : pks.isEmpty = true
  · rw [ite_eq_left he]
    have hs : sig.size ≠ 96 := by
      rcases h with ⟨pk, hpk, -⟩ | hs
      · rw [Array.isEmpty_iff.mp he] at hpk
        simp at hpk
      · exact hs
    exact decide_eq_false fun heq => hs (heq ▸ size_G2_POINT_AT_INFINITY)
  · rw [ite_eq_right he, fastAggregateVerify_fold, ite_eq_right he]
    rcases h with ⟨pk, hpk, hs⟩ | hs
    · obtain ⟨e, he'⟩ := foldlM_stepF_size ⟨pk, Array.mem_toList_iff.mpr hpk, hs⟩ G1.zero
      rw [he']
    · cases pks.toList.foldlM (stepFP validatedPubkey G1.add) G1.zero with
      | error e => rfl
      | ok agg =>
        show coreVerifyPoint agg msg sig = false
        unfold coreVerifyPoint
        by_cases hinf : agg.isInfinity = true
        · rw [ite_eq_left hinf]
        · rw [ite_eq_right hinf, ite_eq_left hs]

end EthLibImpl.Cryptography.Bls.Mirror.Signatures
