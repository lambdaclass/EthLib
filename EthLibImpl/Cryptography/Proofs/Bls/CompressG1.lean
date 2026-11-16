import EthLibImpl.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.G1Endo
import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Group
import EthLib.Cryptography.Proofs.IdLoops
import EthLib.Base.Proofs.Bytes

/-!
# Proofs: `G1` compression in the implementation computes the spec's

`compress`, `uncompress`, `inSubgroup` and `keyValidate` of `EthLibImpl.Cryptography.Bls.G1`
(namespace `G1` of `Bls/Compress.lean`) against the spec's.
-/

set_option linter.unusedSimpArgs false

namespace EthLib.Cryptography.Bls

/-- The implementation's `tailAllZero` (a loop over the tail bytes) is the spec's. -/
theorem tailAllZero_impl_eq (b : ByteArray) (n : Nat) :
    EthLibImpl.Cryptography.Bls.tailAllZero b n = tailAllZero b n := by
  -- The loop clears its flag at the first nonzero byte, so it ends in `all`.
  have step : ∀ (l : List Nat) (ok : Bool),
      l.foldl (fun ok i => if b.get! i ≠ 0 then false else ok) ok =
        (ok && l.all fun i => b.get! i == 0) := by
    intro l
    induction l with
    | nil => intro ok; simp
    | cons i l ih =>
      intro ok
      rw [List.foldl_cons, ih, List.all_cons]
      by_cases h : b.get! i = 0 <;> simp [h]
  have hbody : (fun (i : Nat) (s : Bool) =>
      (if b.get! i ≠ 0 then pure (ForInStep.yield false) else pure (ForInStep.yield s) :
        Id (ForInStep Bool))) =
      fun i s => ForInStep.yield (if b.get! i ≠ 0 then false else s) := by
    funext i s
    split <;> rfl
  unfold EthLibImpl.Cryptography.Bls.tailAllZero
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hbody, EthLib.Cryptography.IdLoops.forIn_list_yield,
    step, Bool.true_and, tailAllZero, Nat.all_eq_finRange_all, Bool.eq_iff_iff]
  show ((List.range' n ((b.size - n + 1 - 1) / 1) 1).all fun i => b.get! i == 0) = true ↔ _
  rw [List.all_eq_true, List.all_eq_true]
  simp only [Nat.add_sub_cancel, Nat.div_one, List.mem_range'_1, List.mem_finRange, true_implies,
    beq_iff_eq]
  constructor
  · intro h ⟨i, hi⟩
    show b[n + i] = 0
    rw [EthLib.Base.byteArray_getElem_eq_get!]
    exact h (n + i) ⟨by omega, by omega⟩
  · intro h i hi
    have := h ⟨i - n, by omega⟩
    simp only at this
    rw [EthLib.Base.byteArray_getElem_eq_get!] at this
    simpa [show n + (i - n) = i by omega] using this

/-- The spec's `uncompress` with `fromBytesBE` and `sqrt` as parameters (see `uncompressP`):
the spec's text, so only its matcher and its bound proofs differ from the spec's. -/
def specUncompressP (fb : ByteArray → Except BlsError Fp)
    (sq : Fp → Except BlsError Fp)
    (bytes : ByteArray) : Except BlsError G1 :=
  if hSize : bytes.size ≠ 48 then .error .invalidG1Point
  else
    let head := bytes[0]'(by omega)
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG1Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG1Point
      else .ok G1.zero
    else
      let xBytes := bytes.set 0 (head &&& 0x1f) (by omega)
      match fb xBytes with
      | .error _ => .error .invalidG1Point
      | .ok x =>
        let rhs := x * x * x + Fp.ofNat 4
        match sq rhs with
        | .error _ => .error .invalidG1Point
        | .ok yPos =>
          let y := if Fp.signBit yPos = ySign then yPos else -yPos
          .ok ⟨x, y, Fp.one⟩

set_option linter.auxLemma false in
universe u in
/-- The spec's matcher and `specUncompressP`'s are the same function. -/
theorem _root_.EthLibImpl.Cryptography.Bls.SpecG1.uncompress_match_eq :
    @G1.uncompress.match_1.{u} = @specUncompressP.match_1.{u} := by
  funext motive d h1 h2
  cases d <;> rfl

set_option linter.auxLemma false in
/-- The spec's `uncompress` is `specUncompressP` at the spec's field routines.

The two bodies differ in their matcher and in the names of their bound proofs, which are
rewritten first: a kernel check of the two bodies as they stand runs for minutes. -/
theorem spec_uncompress_eq : G1.uncompress =
    specUncompressP Fp.fromBytesBE Fp.sqrt := by
  funext bytes
  have e1 : @G1.uncompress._proof_4 = @specUncompressP._proof_1 := rfl
  have e2 : @G1.uncompress._proof_6 = @specUncompressP._proof_2 := rfl
  rewrite [G1.uncompress, specUncompressP, EthLibImpl.Cryptography.Bls.SpecG1.uncompress_match_eq,
    e1, e2]
  rfl

open EthLib.Cryptography.Bls.Fp (toZMod toZMod_add toZMod_mul toZMod_neg toZMod_ofNat)

namespace G1

open WeierstrassCurve.Jacobian

/-- A point `(x, y, 1)` with `y² = x³ + 4` is a nonsingular curve point. -/
theorem valid_of_sq {x y : Fp}
    (h : toZMod y * toZMod y = toZMod (x * x * x + Fp.ofNat 4)) :
    Valid ⟨x, y, Fp.one⟩ :=
  valid_of_affine_eq (toZMod.injective (by rw [toZMod_mul]; exact h))

end G1

/-- Every point `specUncompressP` returns is the point at infinity or `(x, y, 1)` on the curve,
given that `sq` returns square roots. -/
theorem specUncompressP_valid (fb : ByteArray → Except BlsError Fp)
    (sq : Fp → Except BlsError Fp)
    (hsq : ∀ a c, sq a = .ok c → toZMod c * toZMod c = toZMod a) (b : ByteArray) (q : G1)
    (h : specUncompressP fb sq b = .ok q) :
    G1.Valid q ∧ (q = G1.zero ∨ q.z = Fp.one) := by
  unfold specUncompressP at h
  split at h
  · cases h
  dsimp only at h
  split_ifs at h
  · cases h; exact ⟨G1.valid_zero, Or.inl rfl⟩
  · split at h
    · cases h
    · rename_i x _
      split at h
      · cases h
      · rename_i yPos hs
        cases h
        have hy := hsq _ _ hs
        refine ⟨G1.valid_of_sq ?_, Or.inr rfl⟩
        split
        · exact hy
        · rw [toZMod_neg]; rw [← hy]; ring

end EthLib.Cryptography.Bls

namespace EthLibImpl.Cryptography.Bls.G1

open EthLib.Cryptography.Bls (BlsError)

theorem compress_spec {p : G1} (hp : Canonical p) :
    compress p = EthLib.Cryptography.Bls.G1.compress (toSpec p) := by
  unfold compress EthLib.Cryptography.Bls.G1.compress
  rw [isInfinity_spec hp]
  obtain ⟨h1, h2, h3⟩ := toAffine_spec hp
  generalize p.toAffine = pa at h3
  obtain ⟨x, y⟩ := pa
  rw [← h3]
  have hinf : infinityBytes = EthLib.Cryptography.Bls.G1.infinityBytes := rfl
  simp only [hinf, Fp.toBytesBE_eq_spec, Fp.signBit_eq_spec, EthLib.Base.byteArray_getElem_eq_get!,
    EthLib.Base.byteArray_set_eq_set!]


/-- `uncompress` with the two field routines that `match` on, `fromBytesBE` and `sqrt`, as
parameters. The kernel would otherwise evaluate them (a 381-bit exponentiation) while checking
the zeta-reductions the proof below needs. -/
def uncompressP (fb : ByteArray → Except BlsError Fp) (sq : Fp → Except BlsError Fp)
    (bytes : ByteArray) : Except BlsError G1 :=
  if bytes.size ≠ 48 then .error .invalidG1Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG1Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG1Point
      else .ok G1.zero
    else
      let xBytes := bytes.set! 0 (head &&& 0x1f)
      match fb xBytes with
      | .error _ => .error .invalidG1Point
      | .ok x =>
        let rhs := x.sqr * x + Fp.ofNat 4
        match sq rhs with
        | .error _ => .error .invalidG1Point
        | .ok yPos =>
          let y := if yPos.signBit = ySign then yPos else -yPos
          .ok ⟨x, y, Fp.one⟩

theorem spec_one_eq : (1 : EthLib.Cryptography.Bls.Fp) = EthLib.Cryptography.Bls.Fp.one := rfl

theorem uncompress_eq : uncompress = uncompressP Fp.fromBytesBE Fp.sqrt := rfl

theorem uncompressP_spec (fb sq : _) (fb' sq' : _)
    (hfb : ∀ b, (fb b).map Fp.val = fb' b ∧ ∀ c, fb b = .ok c → c.Canonical)
    (hsq : ∀ a : Fp, a.Canonical → (sq a).map Fp.val = sq' a.val ∧
      ∀ c, sq a = .ok c → c.Canonical) (b : ByteArray) :
    (uncompressP fb sq b).map toSpec = EthLib.Cryptography.Bls.specUncompressP fb' sq' b ∧
      ∀ q, uncompressP fb sq b = .ok q → Canonical q := by
  unfold uncompressP EthLib.Cryptography.Bls.specUncompressP
  rw [EthLib.Cryptography.Bls.tailAllZero_impl_eq]
  by_cases hsz : b.size ≠ 48
  · rw [if_pos hsz, dif_pos hsz]
    exact ⟨rfl, fun q h => nomatch h⟩
  rw [if_neg hsz, dif_neg hsz, EthLib.Base.byteArray_getElem_eq_get! b 0 (by omega)]
  dsimp only
  rw [EthLib.Base.byteArray_set_eq_set! b 0 _ (by omega)]
  split_ifs
  · exact ⟨rfl, fun q h => h.elim⟩
  · exact ⟨rfl, fun q h => h.elim⟩
  · refine ⟨?_, fun q h => ?_⟩
    · show Except.ok (toSpec zero) = _
      rw [toSpec_zero]
    · cases h; exact zero_canonical
  · obtain ⟨hfm, hfc⟩ := hfb (b.set! 0 (b.get! 0 &&& 31))
    generalize b.set! 0 (b.get! 0 &&& 31) = xb at hfm hfc ⊢
    rw [← hfm]
    rcases hr : fb xb with e | x
    · exact ⟨rfl, fun q h => nomatch h⟩
    · have hxc : x.Canonical := hfc x hr
      dsimp only [Except.map]
      have hsx : (x.sqr).Canonical := sqr_c hxc
      have hrc : (x.sqr * x + Fp.ofNat 4).Canonical := add_c (mul_c hxc) (Fp.ofNat_canonical _)
      have hrv : (x.sqr * x + Fp.ofNat 4).val =
          x.val * x.val * x.val + EthLib.Cryptography.Bls.Fp.ofNat 4 := by
        rw [add_v (mul_c hxc) (Fp.ofNat_canonical _), mul_v hxc, sqr_v hxc, Fp.val_ofNat]
      obtain ⟨hsm, hsc⟩ := hsq _ hrc
      rw [hrv] at hsm
      rw [← hsm]
      rcases hs : sq (x.sqr * x + Fp.ofNat 4) with e | yPos
      · exact ⟨rfl, fun q h => nomatch h⟩
      · have hyc : yPos.Canonical := hsc yPos hs
        dsimp only [Except.map]
        rw [Fp.signBit_eq_spec]
        refine ⟨?_, fun q h => ?_⟩
        · by_cases hc : (EthLib.Cryptography.Bls.Fp.signBit yPos.val = true) = (b.get! 0 &&& 32 ≠ 0)
          · simp only [hc, if_true]
            show Except.ok (⟨x.val, yPos.val, Fp.one.val⟩ : EthLib.Cryptography.Bls.G1) = _
            rw [Fp.val_one, spec_one_eq]
          · simp only [hc, if_false]
            show Except.ok (⟨x.val, (-yPos).val, Fp.one.val⟩ : EthLib.Cryptography.Bls.G1) = _
            rw [Fp.val_one, neg_v hyc, spec_one_eq]
        · cases h
          refine ⟨hxc, ?_, Fp.one_canonical⟩
          split
          · exact hyc
          · exact neg_c hyc


/-- `uncompress` computes the spec's, and its results are canonical. -/
theorem uncompress_spec (b : ByteArray) :
    (uncompress b).map toSpec = EthLib.Cryptography.Bls.G1.uncompress b ∧
      ∀ q, uncompress b = .ok q → Canonical q := by
  rw [uncompress_eq, EthLib.Cryptography.Bls.spec_uncompress_eq]
  exact uncompressP_spec Fp.fromBytesBE Fp.sqrt EthLib.Cryptography.Bls.Fp.fromBytesBE
    EthLib.Cryptography.Bls.Fp.sqrt
    (fun b => ⟨Fp.fromBytesBE_map_val b, fun c h => Fp.fromBytesBE_ok_canonical h⟩)
    (fun a ha => ⟨Fp.sqrt_map_val ha, fun c h => Fp.sqrt_ok_canonical ha h⟩) b

end EthLibImpl.Cryptography.Bls.G1

namespace EthLibImpl.Cryptography.Bls.SpecG1

open EthLib.Cryptography.Bls

/-- Every point the spec's `uncompress` returns is a valid curve point, and is either the
point at infinity or has `z = 1`. (Upstream's `G1.uncompress_valid` states the first half.) -/
theorem uncompress_valid (b : ByteArray) (q : EthLib.Cryptography.Bls.G1)
    (h : EthLib.Cryptography.Bls.G1.uncompress b = .ok q) :
    EthLib.Cryptography.Bls.G1.Valid q ∧
      (q = EthLib.Cryptography.Bls.G1.zero ∨ q.z = EthLib.Cryptography.Bls.Fp.one) := by
  rw [EthLib.Cryptography.Bls.spec_uncompress_eq] at h
  exact EthLib.Cryptography.Bls.specUncompressP_valid _ _ (fun a c h => by
    rw [← EthLib.Cryptography.Bls.Fp.toZMod_mul, EthLib.Cryptography.Bls.Fp.sqrt_ok h]) b q h

end EthLibImpl.Cryptography.Bls.SpecG1

namespace EthLibImpl.Cryptography.Bls.G1

/-- The endomorphism subgroup test computes the spec's subgroup check on valid points. -/
theorem inSubgroup_spec {p : G1} (hp : Canonical p)
    (hv : EthLib.Cryptography.Bls.G1.Valid (toSpec p)) :
    inSubgroup p = EthLib.Cryptography.Bls.G1.inSubgroup (toSpec p) := by
  rw [EthLibImpl.Cryptography.Bls.SpecG1.inSubgroup_eq_endo hv]
  unfold inSubgroup
  rw [isInfinity_spec hp]
  by_cases h : (toSpec p).isInfinity = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    obtain ⟨he, hes⟩ := endo_spec hp
    obtain ⟨h1, h1s⟩ := mulAbsX_spec hp
    obtain ⟨h2, h2s⟩ := mulAbsX_spec h1
    obtain ⟨h3, h3s⟩ := neg_spec h2
    rw [eqProj_spec he h3, hes, h3s, h2s, h1s]

/-- `keyValidate`'s control flow, with the point type and its two tests abstract (so the kernel
never unfolds them). -/
def keyValidateP {α : Type} (isInf inSub : α → Bool) (u : Except EthLib.Cryptography.Bls.BlsError α) :
    Except EthLib.Cryptography.Bls.BlsError Unit := do
  let p ← u
  if isInf p then throw .pointAtInfinity
  if !inSub p then throw .notInSubgroup

theorem keyValidateP_map {α β : Type} (f : α → β) (isInf inSub : α → Bool)
    (isInf' inSub' : β → Bool) (u : Except EthLib.Cryptography.Bls.BlsError α)
    (h : ∀ p, u = .ok p → isInf p = isInf' (f p) ∧ inSub p = inSub' (f p)) :
    keyValidateP isInf inSub u = keyValidateP isInf' inSub' (u.map f) := by
  cases u with
  | error e => rfl
  | ok p =>
    obtain ⟨h1, h2⟩ := h p rfl
    unfold keyValidateP
    simp only [Except.map, bind, Except.bind, h1, h2]

/-- The spec's `keyValidate` (through `keyValidatePoint`, which returns the point) has
`keyValidateP`'s control flow. -/
theorem keyValidateP_eq_point {α : Type} (isInf inSub : α → Bool)
    (u : Except EthLib.Cryptography.Bls.BlsError α) :
    keyValidateP isInf inSub u =
      ((do
        let p ← u
        if isInf p then throw .pointAtInfinity
        if !inSub p then throw .notInSubgroup
        return p : Except EthLib.Cryptography.Bls.BlsError α) >>= fun _ => pure ()) := by
  cases u with
  | error e => rfl
  | ok p =>
    unfold keyValidateP
    by_cases h1 : isInf p = true <;> by_cases h2 : inSub p = true <;>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
        ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true]

theorem keyValidate_spec (b : ByteArray) :
    keyValidate b = EthLib.Cryptography.Bls.G1.keyValidate b := by
  obtain ⟨hm, hc⟩ := uncompress_spec b
  have e1 : keyValidate b = keyValidateP G1.isInfinity inSubgroup (uncompress b) := rfl
  have e2 : EthLib.Cryptography.Bls.G1.keyValidate b =
      keyValidateP EthLib.Cryptography.Bls.G1.isInfinity EthLib.Cryptography.Bls.G1.inSubgroup
        (EthLib.Cryptography.Bls.G1.uncompress b) := by
    rw [keyValidateP_eq_point]; rfl
  rw [e1, e2, ← hm]
  refine keyValidateP_map toSpec _ _ _ _ _ (fun p hu => ?_)
  have hpc := hc p hu
  have hs : EthLib.Cryptography.Bls.G1.uncompress b = .ok (toSpec p) := by rw [← hm, hu]; rfl
  exact ⟨isInfinity_spec hpc,
    inSubgroup_spec hpc (EthLib.Cryptography.Bls.G1.uncompress_valid hs)⟩

end EthLibImpl.Cryptography.Bls.G1
