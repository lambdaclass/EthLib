import EthLib.Cryptography.Proofs.Bls.G2Subgroup
import EthLibImpl.Cryptography.Proofs.Bls.G2Check
import EthLibImpl.Cryptography.Proofs.Bls.G2Psi
import EthLibImpl.Cryptography.Proofs.Bls.G2Order

/-!
# Proofs: the implementation's `G2` subgroup check

The implementation decides `G2` subgroup membership with `ψ(Q) = [x]Q`
(Scott's test; mirrored over spec types as
`EthLibImpl.Cryptography.Bls.Mirror.G2.inSubgroup`). The spec's
`G2.inSubgroup` is the same test, written with the spec's `psi` (which
normalizes to affine coordinates first), `projectiveEq` and `mulNat · blsX`,
and the spec proves that it decides `[r]Q = O`
(`G2.inSubgroup_iff_modulus_smul_eq_zero`).

* `psi_generator`: `ψ` acts on the generator as `[x]` (the spec's
  `TwistFrobenius.hom_generator`).
* `rTorsion_iff_psi`: on the curve, `[r]Q = O` iff `ψ(Q) = [x]Q`.
* `inSubgroup_eq`: on curve points the implementation's test is the spec's.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2 (Valid toPoint curve generator valid_neg valid_mulNat
  toPoint_neg toPoint_mulNat projectiveEq_eq_true_iff_toPoint_eq)

/-- `[x]R = -[|x|]R` for the BLS parameter `x = -|x|`. -/
private theorem zsmul_x (R : curve.toAffine.Point) :
    (-15132376222941642752 : ℤ) • R = -(blsX • R) := by
  rw [neg_zsmul, show (15132376222941642752 : ℤ) = ((blsX : ℕ) : ℤ) from rfl, natCast_zsmul]

/-- `ψ` acts on the generator as `[x]`, `x = -|x|`. -/
theorem psi_generator :
    TwistFrobenius.hom (toPoint generator) = (-15132376222941642752 : ℤ) • toPoint generator := by
  rw [zsmul_x]
  exact TwistFrobenius.hom_generator

/-- On the curve, `[r]Q = O` iff `ψ(Q) = [x]Q`. -/
theorem rTorsion_iff_psi (Q : curve.toAffine.Point) :
    Fr.modulus • Q = 0 ↔ TwistFrobenius.hom Q = (-15132376222941642752 : ℤ) • Q := by
  rw [zsmul_x]
  refine ⟨fun h => ?_, EthLib.Cryptography.Bls.G2.modulus_smul_eq_zero_of_hom⟩
  obtain ⟨n, -, hn⟩ := EthLib.Cryptography.Bls.G2.exists_nsmul_generator_of_modulus_smul_eq_zero h
  rw [hn]
  exact TwistFrobenius.hom_generator_nsmul n

/-- The subgroup test of the implementation is the spec's, on curve points. -/
theorem inSubgroup_eq {P : G2} (h : Valid P) :
    inSubgroup P = EthLib.Cryptography.Bls.G2.inSubgroup P := by
  by_cases hinf : P.isInfinity = true
  · rw [inSubgroup, EthLib.Cryptography.Bls.G2.inSubgroup, ite_eq_left hinf, ite_eq_left hinf]
  · rw [inSubgroup, EthLib.Cryptography.Bls.G2.inSubgroup, ite_eq_right hinf,
      ite_eq_right hinf]
    have hm := valid_mulAbsX h
    have hv := valid_mulNat h blsX
    rw [Bool.eq_iff_iff, eqProj_iff (valid_psiJ h) (valid_neg hm),
      projectiveEq_eq_true_iff_toPoint_eq (HashToCurve.psi_valid h) (valid_neg hv),
      toPoint_psiJ h, TwistFrobenius.toPoint_psi h, toPoint_neg hm, toPoint_neg hv,
      toPoint_mulAbsX h, toPoint_mulNat h]
    rfl

end EthLibImpl.Cryptography.Bls.Mirror.G2
