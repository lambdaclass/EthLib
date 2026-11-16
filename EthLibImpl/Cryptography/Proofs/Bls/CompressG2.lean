import EthLibImpl.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.G2
import EthLibImpl.Cryptography.Proofs.Bls.CompressG1
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.G2Subgroup

/-!
# Proofs: `G2` compression in the implementation computes the spec's

`fp2ToBytes`, `compress`, `uncompress` and `inSubgroup` of `EthLibImpl.Cryptography.Bls.G2`
(namespace `G2` of `Bls/Compress.lean`). `uncompress` uses `Fp2.sqrt`, which may return the
other root than the spec's, and both then fix the sign with `Fp2.signBit`, so the results agree
(`signBit_normalize`). `inSubgroup` is compared with the spec-level mirror
`Mirror.G2.inSubgroup` (`inSubgroup_spec`), and through `Mirror.G2.inSubgroup_eq` (`G2Subgroup`)
with the spec's `ψ` test on valid points (`inSubgroup_spec_of_valid`).
-/

set_option linter.unusedSimpArgs false

namespace EthLib.Cryptography.Bls

/-- The spec's `G2.uncompress` with `fromBytesBE` and `Fp2.sqrt` as parameters: the spec's text,
so only its matchers and its bound proofs differ from the spec's. -/
def specUncompressP2 (fb : ByteArray → Except BlsError Fp)
    (sq : Fp2 → Except BlsError Fp2) (bytes : ByteArray) : Except BlsError G2 :=
  if hSize : bytes.size ≠ 96 then .error .invalidG2Point
  else
    let head := bytes[0]'(by omega)
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG2Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG2Point
      else .ok G2.zero
    else
      let cleared := bytes.set 0 (head &&& 0x1f) (by omega)
      let c1Bytes := cleared.extract 0 48
      let c0Bytes := cleared.extract 48 96
      match fb c1Bytes, fb c0Bytes with
      | .ok c1, .ok c0 =>
        let x : Fp2 := ⟨c0, c1⟩
        let rhs := x * x * x + G2.bTwist
        match sq rhs with
        | .error _ => .error .invalidG2Point
        | .ok yPos =>
          let yNeg := -yPos
          let y := if Fp2.signBit yPos = ySign then yPos else yNeg
          .ok ⟨x, y, Fp2.one⟩
      | _, _ => .error .invalidG2Point

set_option linter.auxLemma false in
universe u in
/-- The spec's matcher on the two decoded halves and `specUncompressP2`'s are the same
function. -/
theorem _root_.EthLibImpl.Cryptography.Bls.SpecG2.uncompress_match_3_eq :
    @G2.uncompress.match_3.{u} = @specUncompressP2.match_3.{u} := by
  funext motive d1 d0 h1 h2
  cases d1 <;> cases d0 <;> rfl

set_option linter.auxLemma false in
universe u in
/-- The spec's matcher on the square root and `specUncompressP2`'s are the same function. -/
theorem _root_.EthLibImpl.Cryptography.Bls.SpecG2.uncompress_match_1_eq :
    @G2.uncompress.match_1.{u} = @specUncompressP2.match_1.{u} := by
  funext motive d h1 h2
  cases d <;> rfl

set_option linter.auxLemma false in
/-- The spec's `G2.uncompress` is `specUncompressP2` at the spec's field routines.

The two bodies differ in their matchers and in the names of their bound proofs, which are
rewritten first, as for `G1` (`spec_uncompress_eq` in `CompressG1`). -/
theorem spec_uncompress2_eq : G2.uncompress = specUncompressP2 Fp.fromBytesBE Fp2.sqrt := by
  funext bytes
  have e1 : @G2.uncompress._proof_7 = @specUncompressP2._proof_1 := rfl
  have e2 : @G2.uncompress._proof_9 = @specUncompressP2._proof_2 := rfl
  rewrite [G2.uncompress, specUncompressP2, EthLibImpl.Cryptography.Bls.SpecG2.uncompress_match_3_eq,
    EthLibImpl.Cryptography.Bls.SpecG2.uncompress_match_1_eq, e1, e2]
  rfl

open scoped EthLib.Cryptography.Bls.Fp2 in
/-- `signBit_normalize` with the flag as an arbitrary decidable proposition. -/
theorem signBit_normalize_prop {y z a : Fp2} (hy : y * y = a) (hz : z * z = a) (P : Prop)
    [Decidable P] :
    (if (Fp2.signBit y = true) = P then y else -y) =
      (if (Fp2.signBit z = true) = P then z else -z) := by
  rcases Fp2.mul_self_eq_mul_self_iff'.mp (hy.trans hz.symm) with h | h
  · rw [h]
  · rw [h]
    by_cases hz0 : z = 0
    · simp [hz0]
    · rw [Fp2.signBit_neg hz0, neg_neg]
      cases Fp2.signBit z <;> by_cases hP : P <;> simp [hP]

open scoped EthLib.Cryptography.Bls.Fp2 in
/-- Two square-root routines that fail on the same inputs and otherwise return square roots
give the same `specUncompressP2`: the sign selection picks the same root of either. -/
theorem specUncompressP2_congr (fb : ByteArray → Except BlsError Fp)
    (sq1 sq2 : Fp2 → Except BlsError Fp2)
    (h : ∀ a, (∃ e1 e2, sq1 a = .error e1 ∧ sq2 a = .error e2) ∨
      ∃ y z, sq1 a = .ok y ∧ sq2 a = .ok z ∧ y * y = a ∧ z * z = a)
    (b : ByteArray) : specUncompressP2 fb sq1 b = specUncompressP2 fb sq2 b := by
  unfold specUncompressP2
  split
  · rfl
  extract_lets head isC isI yS cleared c1Bytes c0Bytes
  split_ifs
  · rfl
  · rfl
  · rfl
  generalize fb c1Bytes = d1
  generalize fb c0Bytes = d0
  cases d1 <;> cases d0
  · rfl
  · rfl
  · rfl
  rename_i c1 c0
  dsimp only
  generalize (⟨c0, c1⟩ : Fp2) * ⟨c0, c1⟩ * ⟨c0, c1⟩ + G2.bTwist = a
  rcases h a with ⟨e1, e2, h1, h2⟩ | ⟨y, z, h1, h2, hy, hz⟩
  · rw [h1, h2]
  · rw [h1, h2]
    dsimp only
    rw [signBit_normalize_prop hy hz]

/-- Swapping the square root for `sqrtAlt` does not change `uncompress`. -/
theorem specUncompressP2_alt (fb : ByteArray → Except BlsError Fp) (b : ByteArray) :
    specUncompressP2 fb Fp2.sqrtAlt b = specUncompressP2 fb Fp2.sqrt b := by
  refine specUncompressP2_congr fb _ _ (fun a => ?_) b
  have hi := Fp2.sqrtAlt_isOk a
  rcases h1 : Fp2.sqrtAlt a with e | y <;> rcases h2 : Fp2.sqrt a with e' | z
  · exact Or.inl ⟨e, e', rfl, rfl⟩
  · rw [h1, h2] at hi; simp [Except.isOk, Except.toBool] at hi
  · rw [h1, h2] at hi; simp [Except.isOk, Except.toBool] at hi
  · exact Or.inr ⟨y, z, rfl, rfl, Fp2.sqrtAlt_ok h1, Fp2.sqrt_ok h2⟩

namespace G2

/-- The implementation's `fp2ToBytes` is the spec's. -/
theorem fp2ToBytes_impl_eq (x : EthLibImpl.Cryptography.Bls.Fp2) :
    EthLibImpl.Cryptography.Bls.G2.fp2ToBytes x = fp2ToBytes x.toSpec := by
  show x.c1.toBytesBE ++ x.c0.toBytesBE = (x.c1.val).toBytesBE ++ (x.c0.val).toBytesBE
  rw [EthLibImpl.Cryptography.Bls.Fp.toBytesBE_eq_spec,
    EthLibImpl.Cryptography.Bls.Fp.toBytesBE_eq_spec]

end G2

end EthLib.Cryptography.Bls

namespace EthLibImpl.Cryptography.Bls.G2

open EthLib.Cryptography.Bls (BlsError)

theorem compress_spec {p : G2} (hp : Canonical p) :
    compress p = EthLib.Cryptography.Bls.G2.compress (toSpec p) := by
  unfold compress EthLib.Cryptography.Bls.G2.compress
  rw [isInfinity_spec hp]
  obtain ⟨h1, h2, h3⟩ := toAffine_spec hp
  generalize p.toAffine = pa at h1 h2 h3
  obtain ⟨x, y⟩ := pa
  rw [← h3]
  have hinf : infinityBytes = EthLib.Cryptography.Bls.G2.infinityBytes := rfl
  simp only [hinf, EthLib.Cryptography.Bls.G2.fp2ToBytes_impl_eq, Fp2.signBit_spec (y := y) h2,
    EthLib.Base.byteArray_getElem_eq_get!, EthLib.Base.byteArray_set_eq_set!]

/-- `uncompress` with the two routines that `match` on, `fromBytesBE` and `Fp2.sqrt`, as
parameters (the kernel would otherwise evaluate them while checking zeta-reductions). -/
def uncompressP (fb : ByteArray → Except BlsError Fp) (sq : Fp2 → Except BlsError Fp2)
    (bytes : ByteArray) : Except BlsError G2 :=
  if bytes.size ≠ 96 then .error .invalidG2Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG2Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG2Point
      else .ok G2.zero
    else
      let cleared := bytes.set! 0 (head &&& 0x1f)
      let c1Bytes := cleared.extract 0 48
      let c0Bytes := cleared.extract 48 96
      match fb c1Bytes, fb c0Bytes with
      | .ok c1, .ok c0 =>
        let x : Fp2 := Fp2.mk c0 c1
        let rhs := x.sqr * x + bTwist
        match sq rhs with
        | .error _ => .error .invalidG2Point
        | .ok yPos =>
          let y := if Fp2.signBit yPos = ySign then yPos else -yPos
          .ok ⟨x, y, Fp2.one⟩
      | _, _ => .error .invalidG2Point

theorem uncompress_eq : uncompress = uncompressP Fp.fromBytesBE Fp2.sqrt := by
  funext b
  unfold uncompress uncompressP
  rfl

theorem uncompressP_spec (fb : ByteArray → Except BlsError Fp) (sq : Fp2 → Except BlsError Fp2)
    (fb' : ByteArray → Except BlsError EthLib.Cryptography.Bls.Fp)
    (sq' : EthLib.Cryptography.Bls.Fp2 → Except BlsError EthLib.Cryptography.Bls.Fp2)
    (hfb : ∀ b, (fb b).map Fp.val = fb' b ∧ ∀ c, fb b = .ok c → c.Canonical)
    (hsq : ∀ a : Fp2, a.Canonical → (sq a).map Fp2.toSpec = sq' a.toSpec ∧
      ∀ c, sq a = .ok c → c.Canonical) (b : ByteArray) :
    (uncompressP fb sq b).map toSpec = EthLib.Cryptography.Bls.specUncompressP2 fb' sq' b ∧
      ∀ q, uncompressP fb sq b = .ok q → Canonical q := by
  unfold uncompressP EthLib.Cryptography.Bls.specUncompressP2
  rw [EthLib.Cryptography.Bls.tailAllZero_impl_eq]
  by_cases hsz : b.size ≠ 96
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
  · obtain ⟨hf1, hc1⟩ := hfb ((b.set! 0 (b.get! 0 &&& 31)).extract 0 48)
    obtain ⟨hf0, hc0⟩ := hfb ((b.set! 0 (b.get! 0 &&& 31)).extract 48 96)
    generalize (b.set! 0 (b.get! 0 &&& 31)).extract 0 48 = xb1 at hf1 hc1 ⊢
    generalize (b.set! 0 (b.get! 0 &&& 31)).extract 48 96 = xb0 at hf0 hc0 ⊢
    rw [← hf1, ← hf0]
    rcases hr1 : fb xb1 with e1 | c1 <;> rcases hr0 : fb xb0 with e0 | c0
    · exact ⟨rfl, fun q h => nomatch h⟩
    · exact ⟨rfl, fun q h => nomatch h⟩
    · exact ⟨rfl, fun q h => nomatch h⟩
    · have hc1' : c1.Canonical := hc1 c1 hr1
      have hc0' : c0.Canonical := hc0 c0 hr0
      dsimp only [Except.map]
      have hxc : (Fp2.mk c0 c1).Canonical := Fp2.canonical_mk hc0' hc1'
      have hsx : ((Fp2.mk c0 c1).sqr).Canonical := sqr_c hxc
      have hrc : ((Fp2.mk c0 c1).sqr * Fp2.mk c0 c1 + bTwist).Canonical :=
        add_c (mul_c hsx hxc) bTwist_spec.1
      have hrv : ((Fp2.mk c0 c1).sqr * Fp2.mk c0 c1 + bTwist).toSpec =
          (⟨c0.val, c1.val⟩ : EthLib.Cryptography.Bls.Fp2) * ⟨c0.val, c1.val⟩ *
            ⟨c0.val, c1.val⟩ + EthLib.Cryptography.Bls.G2.bTwist := by
        rw [add_v (mul_c hsx hxc) bTwist_spec.1, mul_v hsx hxc, sqr_v hxc, bTwist_spec.2,
          Fp2.toSpec_mk]
      obtain ⟨hsm, hsc⟩ := hsq _ hrc
      rw [hrv] at hsm
      rw [← hsm]
      rcases hs : sq ((Fp2.mk c0 c1).sqr * Fp2.mk c0 c1 + bTwist) with e | yPos
      · exact ⟨rfl, fun q h => nomatch h⟩
      · have hyc : yPos.Canonical := hsc yPos hs
        dsimp only [Except.map]
        rw [Fp2.signBit_spec hyc]
        refine ⟨?_, fun q h => ?_⟩
        · by_cases hc : (EthLib.Cryptography.Bls.Fp2.signBit yPos.toSpec = true) =
              (b.get! 0 &&& 32 ≠ 0)
          · simp only [hc, if_true]
            show Except.ok (⟨(Fp2.mk c0 c1).toSpec, yPos.toSpec, Fp2.one.toSpec⟩ :
              EthLib.Cryptography.Bls.G2) = _
            rw [Fp2.toSpec_one, Fp2.toSpec_mk]
          · simp only [hc, if_false]
            show Except.ok (⟨(Fp2.mk c0 c1).toSpec, (-yPos).toSpec, Fp2.one.toSpec⟩ :
              EthLib.Cryptography.Bls.G2) = _
            rw [Fp2.toSpec_one, Fp2.toSpec_mk, neg_v hyc]
        · cases h
          refine ⟨hxc, ?_, Fp2.one_canonical⟩
          split
          · exact hyc
          · exact neg_c hyc

end EthLibImpl.Cryptography.Bls.G2

namespace EthLibImpl.Cryptography.Bls.G2

/-- `uncompress` computes the spec's, and its results are canonical. -/
theorem uncompress_spec (b : ByteArray) :
    (uncompress b).map toSpec = EthLib.Cryptography.Bls.G2.uncompress b ∧
      ∀ q, uncompress b = .ok q → Canonical q := by
  rw [uncompress_eq, EthLib.Cryptography.Bls.spec_uncompress2_eq,
    ← EthLib.Cryptography.Bls.specUncompressP2_alt]
  exact uncompressP_spec Fp.fromBytesBE Fp2.sqrt EthLib.Cryptography.Bls.Fp.fromBytesBE
    EthLib.Cryptography.Bls.Fp2.sqrtAlt
    (fun b => ⟨Fp.fromBytesBE_map_val b, fun c h => Fp.fromBytesBE_ok_canonical h⟩)
    (fun a ha => Fp2.sqrt_spec ha) b

theorem canonical_psiC1 : psiC1.Canonical :=
  Fp2.canonical_mk Fp.zero_canonical (Fp.ofNat_canonical _)

theorem canonical_psiC2 : psiC2.Canonical :=
  Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _)

open scoped EthLib.Cryptography.Bls.Fp in
theorem toSpec_psiC1 : Fp2.toSpec psiC1 = Mirror.G2.c1 := by
  simp only [psiC1, Mirror.G2.c1, Fp2.toSpec_mk, Fp.val_zero, Fp.val_ofNat,
    EthLib.Cryptography.Bls.Fp.ofNat_eq_natCast 0, Nat.cast_zero,
    EthLib.Cryptography.Bls.Fp.zero_def]

theorem toSpec_psiC2 : Fp2.toSpec psiC2 = Mirror.G2.c2 := by
  simp only [psiC2, Mirror.G2.c2, Fp2.toSpec_mk, Fp.val_ofNat]

/-- `psiJ` computes the mirror's. -/
theorem psiJ_spec {p : G2} (hp : Canonical p) :
    Canonical (psiJ p) ∧ toSpec (psiJ p) = Mirror.G2.psiJ (toSpec p) := by
  obtain ⟨hx, hy, hz⟩ := hp
  have e : psiJ p = ⟨psiC1 * p.x.conj, psiC2 * p.y.conj, p.z.conj⟩ := rfl
  rw [e]
  refine ⟨canonical_mk.mpr ⟨Fp2.canonical_hMul canonical_psiC1 (Fp2.conj_canonical hx),
    Fp2.canonical_hMul canonical_psiC2 (Fp2.conj_canonical hy), Fp2.conj_canonical hz⟩, ?_⟩
  simp only [Mirror.G2.psiJ, toSpec_mk, toSpec_x, toSpec_y, toSpec_z,
    Fp2.toSpec_hMul canonical_psiC1 (Fp2.conj_canonical hx),
    Fp2.toSpec_hMul canonical_psiC2 (Fp2.conj_canonical hy), Fp2.toSpec_conj hx,
    Fp2.toSpec_conj hy, Fp2.toSpec_conj hz, toSpec_psiC1, toSpec_psiC2]

/-- The implementation's subgroup test computes the mirror's. -/
theorem inSubgroup_spec {p : G2} (hp : Canonical p) :
    inSubgroup p = Mirror.G2.inSubgroup (toSpec p) := by
  unfold inSubgroup Mirror.G2.inSubgroup
  rw [isInfinity_spec hp]
  by_cases h : (toSpec p).isInfinity = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    obtain ⟨h1, h1s⟩ := mulAbsX_spec hp
    obtain ⟨h2, h2s⟩ := neg_spec h1
    obtain ⟨h3, h3s⟩ := psiJ_spec hp
    rw [eqProj_spec h3 h2, h3s, h2s, h1s]

/-- The implementation's subgroup test computes the spec's `ψ` test on points of the twist. -/
theorem inSubgroup_spec_of_valid {p : G2} (hp : Canonical p)
    (hv : EthLib.Cryptography.Bls.G2.Valid (toSpec p)) :
    inSubgroup p = EthLib.Cryptography.Bls.G2.inSubgroup (toSpec p) := by
  rw [inSubgroup_spec hp, Mirror.G2.inSubgroup_eq hv]

end EthLibImpl.Cryptography.Bls.G2
