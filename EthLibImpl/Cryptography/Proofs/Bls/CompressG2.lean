import EthLibImpl.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.G2
import EthLibImpl.Cryptography.Proofs.Bls.CompressG1
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2

/-!
# Proofs: `G2` compression in the implementation computes the spec's

`fp2ToBytes`, `compress`, `uncompress` and `inSubgroup` of `EthLibImpl.Cryptography.Bls.G2`
(namespace `G2` of `Bls/Compress.lean`). `uncompress` uses `Fp2.sqrt`, which may return the
other root than the spec's, and both then fix the sign with `Fp2.signBit`, so the results agree
(`signBit_normalize`). `inSubgroup` is compared with the spec-level mirror
`Mirror.G2.inSubgroup` (equal to the spec's on valid points by `Mirror.G2.inSubgroup_eq`, in `G2Subgroup`).
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLib.Cryptography.Bls

open private tailAllZero fp2ToBytes from EthLib.Cryptography.Bls.Compress

/-- The spec's `G2.uncompress` with `fromBytesBE` and `Fp2.sqrt` as parameters. -/
def specUncompressP2 (fb : ByteArray → Except BlsError Fp)
    (sq : Fp2 → Except BlsError Fp2) (bytes : ByteArray) : Except BlsError G2 :=
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
        let x : Fp2 := ⟨c0, c1⟩
        let rhs := x * x * x + G2.bTwist
        match sq rhs with
        | .error _ => .error .invalidG2Point
        | .ok yPos =>
          let yNeg := -yPos
          let y := if Fp2.signBit yPos = ySign then yPos else yNeg
          .ok ⟨x, y, Fp2.one⟩
      | _, _ => .error .invalidG2Point

theorem spec_uncompress2_eq : G2.uncompress = specUncompressP2 Fp.fromBytesBE Fp2.sqrt := by
  funext b
  unfold G2.uncompress specUncompressP2
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
/-- Swapping the square root for `sqrtAlt` does not change `uncompress`. -/
theorem specUncompressP2_alt (fb : ByteArray → Except BlsError Fp) (b : ByteArray) :
    specUncompressP2 fb Fp2.sqrtAlt b = specUncompressP2 fb Fp2.sqrt b := by
  unfold specUncompressP2
  dsimp only
  split_ifs
  · rfl
  · rfl
  · rfl
  · rfl
  rcases hc1 : fb ((b.set! 0 (b.get! 0 &&& 31)).extract 0 48) with e1 | c1 <;>
    rcases hc0 : fb ((b.set! 0 (b.get! 0 &&& 31)).extract 48 96) with e0 | c0 <;> try rfl
  dsimp only
  generalize (⟨c0, c1⟩ : Fp2) * ⟨c0, c1⟩ * ⟨c0, c1⟩ + G2.bTwist = rhs
  have hi := Fp2.sqrtAlt_isOk rhs
  rcases h1 : Fp2.sqrt rhs with e | y
  · rcases h2 : Fp2.sqrtAlt rhs with e' | z
    · rfl
    · rw [h1, h2] at hi; simp [Except.isOk, Except.toBool] at hi
  · rcases h2 : Fp2.sqrtAlt rhs with e' | z
    · rw [h1, h2] at hi; simp [Except.isOk, Except.toBool] at hi
    · dsimp only
      rw [signBit_normalize_prop (Fp2.sqrtAlt_ok h2) (Fp2.sqrt_ok h1)]

namespace G2

/-- The implementation's `fp2ToBytes` is the spec's (a private definition there). -/
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
  simp only [hinf, EthLib.Cryptography.Bls.G2.fp2ToBytes_impl_eq, Fp2.signBit_spec (y := y) h2]

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
  dsimp only
  split_ifs
  · exact ⟨rfl, fun q h => h.elim⟩
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

theorem toSpec_psiC1 : Fp2.toSpec psiC1 = Mirror.G2.c1 := by
  simp only [psiC1, Mirror.G2.c1, Fp2.toSpec_mk, Fp.val_zero, Fp.val_ofNat]
  rfl

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

end EthLibImpl.Cryptography.Bls.G2
