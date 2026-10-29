import EthLibImpl.Cryptography.Proofs.Bls.Fp12
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing
import EthLibImpl.Cryptography.Bls.Pairing

/-!
# Proofs: compressed squarings and batched decompression compute their mirrors

For canonical inputs, `csqrN` and `decompress6` of `EthLibImpl.Cryptography.Bls.Pairing`
return the image under `toSpec` of what `Mirror.csqrN` and `Mirror.decompress6` compute.

The mirror decompresses each element on its own, with the spec's `inverse 0 = 0`. The
implementation shares one inversion among the six (Montgomery's trick): with
`E_k = if d_k = 0 then 1 else d_k` and `i = (E₀E₁E₂E₃E₄E₅)⁻¹`, the partial products
`i·E₄E₅·E₂E₃·E₁` and its five siblings are the `E_k⁻¹` (`batch6_inv`), and a zero
denominator selects `0`, which is the spec's `n·inverse 0`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls

theorem csqrN_spec {x : Fp12.C4} (hx : x.Canonical) :
    ∀ n, (csqrN x n).Canonical ∧ (csqrN x n).toSpec = Mirror.csqrN x.toSpec n := by
  intro n
  induction n generalizing x with
  | zero => exact ⟨hx, rfl⟩
  | succ n ih =>
    rw [csqrN, Mirror.csqrN, ← Fp12.toSpec_csqr hx]
    exact ih (Fp12.csqr_canonical hx)

section batch

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2

local notation "S2" => EthLib.Cryptography.Bls.Fp2

private theorem spec_isZero_iff {a : S2} : a.isZero = true ↔ a = 0 := by
  rw [EthLib.Cryptography.Bls.Fp2.isZero, Bool.and_eq_true, EthLib.Cryptography.Bls.Fp2.ext_iff]
  have h : ∀ x : EthLib.Cryptography.Bls.Fp, EthLib.Cryptography.Bls.Fp.isZero x = true ↔ x = 0 :=
    fun x => by
      rw [EthLib.Cryptography.Bls.Fp.isZero, beq_iff_eq]
      exact ZMod.val_eq_zero (n := EthLib.Cryptography.Bls.Fp.modulus) x
  exact and_congr (h _) (h _)

/-- The value a zero denominator is replaced by. -/
private def E (a : S2) : S2 := if a.isZero then 1 else a

private theorem E_ne_zero (a : S2) : E a ≠ 0 := by
  unfold E
  by_cases h : a.isZero = true
  · rw [if_pos h]; exact one_ne_zero
  · rw [if_neg h]; exact fun h0 => h (spec_isZero_iff.mpr h0)

private theorem sel_one {a : Fp2} (ha : a.Canonical) :
    (if a.isZero then Fp2.one else a).Canonical ∧
      (if a.isZero then Fp2.one else a).toSpec = E a.toSpec := by
  unfold E
  by_cases h : a.isZero = true
  · rw [if_pos h, if_pos (by rw [Fp2.isZero_eq ha]; exact h)]
    exact ⟨Fp2.one_canonical, Fp2.toSpec_one⟩
  · rw [if_neg h, if_neg (by rw [Fp2.isZero_eq ha]; exact h)]
    exact ⟨ha, rfl⟩

/-- One decompression slot: a zero denominator gives `0`, otherwise the numerator times
the cofactor product, which is `E(d)⁻¹`. -/
private theorem slot_spec {n d t : Fp2} (hn : n.Canonical) (hd : d.Canonical)
    (ht : t.Canonical) (hv : t.toSpec = (E d.toSpec)⁻¹) :
    (if d.isZero then Fp2.zero else n * t).Canonical ∧
      (if d.isZero then Fp2.zero else n * t).toSpec = n.toSpec * d.toSpec.inverse := by
  by_cases hz : d.isZero = true
  · rw [if_pos hz]
    have h0 : d.toSpec = 0 := spec_isZero_iff.mp (by rw [Fp2.isZero_eq hd]; exact hz)
    refine ⟨Fp2.zero_canonical, ?_⟩
    rw [Fp2.toSpec_zero, h0, EthLib.Cryptography.Bls.Fp2.inverse_eq_inv, inv_zero, mul_zero]
    rfl
  · rw [if_neg hz]
    have hs : ¬ d.toSpec.isZero = true := by rw [Fp2.isZero_eq hd]; exact hz
    refine ⟨Fp2.canonical_hMul hn ht, ?_⟩
    rw [Fp2.toSpec_hMul hn ht, hv, EthLib.Cryptography.Bls.Fp2.inverse_eq_inv]
    unfold E
    rw [if_neg hs]

theorem batch6_inv {e0 e1 e2 e3 e4 e5 : S2} (h0 : e0 ≠ 0) (h1 : e1 ≠ 0) (h2 : e2 ≠ 0)
    (h3 : e3 ≠ 0) (h4 : e4 ≠ 0) (h5 : e5 ≠ 0) :
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * (e4 * e5) * (e2 * e3) * e1 = e0⁻¹ ∧
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * (e4 * e5) * (e2 * e3) * e0 = e1⁻¹ ∧
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * (e4 * e5) * (e0 * e1) * e3 = e2⁻¹ ∧
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * (e4 * e5) * (e0 * e1) * e2 = e3⁻¹ ∧
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * ((e0 * e1) * (e2 * e3)) * e5 = e4⁻¹ ∧
    ((e0 * e1) * (e2 * e3) * (e4 * e5))⁻¹ * ((e0 * e1) * (e2 * e3)) * e4 = e5⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

set_option maxHeartbeats 4000000 in
theorem decompress6_spec {x0 x1 x2 x3 x4 x5 : Fp12.C4} (h0 : x0.Canonical) (h1 : x1.Canonical)
    (h2 : x2.Canonical) (h3 : x3.Canonical) (h4 : x4.Canonical) (h5 : x5.Canonical) :
    let r := decompress6 x0 x1 x2 x3 x4 x5
    r.1.Canonical ∧ r.2.1.Canonical ∧ r.2.2.1.Canonical ∧ r.2.2.2.1.Canonical ∧
      r.2.2.2.2.1.Canonical ∧ r.2.2.2.2.2.Canonical ∧
      (r.1.toSpec, r.2.1.toSpec, r.2.2.1.toSpec, r.2.2.2.1.toSpec, r.2.2.2.2.1.toSpec,
        r.2.2.2.2.2.toSpec) =
        Mirror.decompress6 x0.toSpec x1.toSpec x2.toSpec x3.toSpec x4.toSpec x5.toSpec := by
  intro r
  obtain ⟨cn0, cd0, v0⟩ := Fp12.g4Frac_spec h0
  obtain ⟨cn1, cd1, v1⟩ := Fp12.g4Frac_spec h1
  obtain ⟨cn2, cd2, v2⟩ := Fp12.g4Frac_spec h2
  obtain ⟨cn3, cd3, v3⟩ := Fp12.g4Frac_spec h3
  obtain ⟨cn4, cd4, v4⟩ := Fp12.g4Frac_spec h4
  obtain ⟨cn5, cd5, v5⟩ := Fp12.g4Frac_spec h5
  simp only [r, decompress6, Mirror.decompress6, Mirror.decompress]
  rw [← v0, ← v1, ← v2, ← v3, ← v4, ← v5]
  generalize Fp12.g4Frac x0 = P0 at cn0 cd0 ⊢
  generalize Fp12.g4Frac x1 = P1 at cn1 cd1 ⊢
  generalize Fp12.g4Frac x2 = P2 at cn2 cd2 ⊢
  generalize Fp12.g4Frac x3 = P3 at cn3 cd3 ⊢
  generalize Fp12.g4Frac x4 = P4 at cn4 cd4 ⊢
  generalize Fp12.g4Frac x5 = P5 at cn5 cd5 ⊢
  obtain ⟨n0, d0⟩ := P0
  obtain ⟨n1, d1⟩ := P1
  obtain ⟨n2, d2⟩ := P2
  obtain ⟨n3, d3⟩ := P3
  obtain ⟨n4, d4⟩ := P4
  obtain ⟨n5, d5⟩ := P5
  dsimp only at cn0 cd0 cn1 cd1 cn2 cd2 cn3 cd3 cn4 cd4 cn5 cd5 ⊢
  obtain ⟨c0, s0⟩ := sel_one cd0
  obtain ⟨c1, s1⟩ := sel_one cd1
  obtain ⟨c2, s2⟩ := sel_one cd2
  obtain ⟨c3, s3⟩ := sel_one cd3
  obtain ⟨c4, s4⟩ := sel_one cd4
  obtain ⟨c5, s5⟩ := sel_one cd5
  generalize (if d0.isZero = true then Fp2.one else d0) = e0 at c0 s0 ⊢
  generalize (if d1.isZero = true then Fp2.one else d1) = e1 at c1 s1 ⊢
  generalize (if d2.isZero = true then Fp2.one else d2) = e2 at c2 s2 ⊢
  generalize (if d3.isZero = true then Fp2.one else d3) = e3 at c3 s3 ⊢
  generalize (if d4.isZero = true then Fp2.one else d4) = e4 at c4 s4 ⊢
  generalize (if d5.isZero = true then Fp2.one else d5) = e5 at c5 s5 ⊢
  have B := batch6_inv (e0 := e0.toSpec) (e1 := e1.toSpec) (e2 := e2.toSpec) (e3 := e3.toSpec)
    (e4 := e4.toSpec) (e5 := e5.toSpec) (by rw [s0]; exact E_ne_zero _)
    (by rw [s1]; exact E_ne_zero _) (by rw [s2]; exact E_ne_zero _)
    (by rw [s3]; exact E_ne_zero _) (by rw [s4]; exact E_ne_zero _)
    (by rw [s5]; exact E_ne_zero _)
  have mulv : ∀ {a b : Fp2}, a.Canonical → b.Canonical →
      (a * b).Canonical ∧ (a * b).toSpec = a.toSpec * b.toSpec :=
    fun ha hb => ⟨Fp2.canonical_hMul ha hb, Fp2.toSpec_hMul ha hb⟩
  obtain ⟨cp01, vp01⟩ := mulv c0 c1
  obtain ⟨cp23, vp23⟩ := mulv c2 c3
  obtain ⟨cp45, vp45⟩ := mulv c4 c5
  obtain ⟨cp0123, vp0123⟩ := mulv cp01 cp23
  obtain ⟨cpall, vpall⟩ := mulv cp0123 cp45
  have ci := Fp2.inverse_canonical cpall
  have vi := Fp2.toSpec_inverse cpall
  rw [vpall, vp0123, vp01, vp23, vp45, EthLib.Cryptography.Bls.Fp2.inverse_eq_inv] at vi
  obtain ⟨ci0123, vi0123⟩ := mulv ci cp45
  obtain ⟨ci45, vi45⟩ := mulv ci cp0123
  obtain ⟨ci01, vi01⟩ := mulv ci0123 cp23
  obtain ⟨ci23, vi23⟩ := mulv ci0123 cp01
  obtain ⟨ct0, vt0⟩ := mulv ci01 c1
  obtain ⟨ct1, vt1⟩ := mulv ci01 c0
  obtain ⟨ct2, vt2⟩ := mulv ci23 c3
  obtain ⟨ct3, vt3⟩ := mulv ci23 c2
  obtain ⟨ct4, vt4⟩ := mulv ci45 c5
  obtain ⟨ct5, vt5⟩ := mulv ci45 c4
  obtain ⟨B0, B1, B2, B3, B4, B5⟩ := B
  obtain ⟨sc0, sv0⟩ := slot_spec cn0 cd0 ct0
    (by rw [vt0, vi01, vi0123, vp23, vp45, vi, B0, s0])
  obtain ⟨sc1, sv1⟩ := slot_spec cn1 cd1 ct1
    (by rw [vt1, vi01, vi0123, vp23, vp45, vi, B1, s1])
  obtain ⟨sc2, sv2⟩ := slot_spec cn2 cd2 ct2
    (by rw [vt2, vi23, vi0123, vp01, vp45, vi, B2, s2])
  obtain ⟨sc3, sv3⟩ := slot_spec cn3 cd3 ct3
    (by rw [vt3, vi23, vi0123, vp01, vp45, vi, B3, s3])
  obtain ⟨sc4, sv4⟩ := slot_spec cn4 cd4 ct4
    (by rw [vt4, vi45, vp0123, vp01, vp23, vi, B4, s4])
  obtain ⟨sc5, sv5⟩ := slot_spec cn5 cd5 ct5
    (by rw [vt5, vi45, vp0123, vp01, vp23, vi, B5, s5])
  refine ⟨Fp12.rebuild_canonical h0 sc0, Fp12.rebuild_canonical h1 sc1,
    Fp12.rebuild_canonical h2 sc2, Fp12.rebuild_canonical h3 sc3,
    Fp12.rebuild_canonical h4 sc4, Fp12.rebuild_canonical h5 sc5, ?_⟩
  rw [Fp12.toSpec_rebuild h0 sc0, Fp12.toSpec_rebuild h1 sc1, Fp12.toSpec_rebuild h2 sc2,
    Fp12.toSpec_rebuild h3 sc3, Fp12.toSpec_rebuild h4 sc4, Fp12.toSpec_rebuild h5 sc5,
    sv0, sv1, sv2, sv3, sv4, sv5]

end batch

end EthLibImpl.Cryptography.Bls
