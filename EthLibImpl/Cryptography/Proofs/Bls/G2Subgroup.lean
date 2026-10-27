import EthLibImpl.Cryptography.Proofs.Bls.G2Check
import EthLibImpl.Cryptography.Proofs.Bls.G2Psi
import EthLibImpl.Cryptography.Proofs.Bls.G2Order
import EthLibImpl.Cryptography.Proofs.Bls.EigenTorsion

/-!
# Proofs: the implementation's `G2` subgroup check

The implementation decides `G2` subgroup membership with `ψ(Q) = [x]Q`
(Scott's test; mirrored over spec types as
`EthLibImpl.Cryptography.Bls.Mirror.G2.inSubgroup`), where the spec's
`G2.inSubgroup` tests `[r]Q = O`.

* `psiJ_generator`: `ψ` acts on the generator as `[x]`, a kernel computation.
* `r_smul_generator`: `[r]g₂ = 0`, a kernel computation.
* `inSubgroup_eq`: on curve points the two tests agree, by the eigenspace
  characterisation `rTorsion_iff_eigen_phi12` of the `r`-torsion.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2
open scoped EthLib.Cryptography.Bls.Fp2
open WeierstrassCurve.Jacobian

set_option maxRecDepth 8000

private theorem generator_curve :
    generator.y * generator.y = generator.x * generator.x * generator.x + bTwist := by
  decide

theorem valid_generator : Valid generator := valid_affine generator_curve

private theorem generator_z_ne : generator.isInfinity = false := by decide

theorem toPoint_generator_ne_zero : toPoint generator ≠ 0 := fun h =>
  absurd ((isInfinity_iff valid_generator).mpr h) (by rw [generator_z_ne]; decide)

private theorem eqProj_psiJ_generator :
    eqProj (psiJ generator) (neg (mulAbsX generator)) = true := by
  decide +kernel

/-- `ψ` acts on the generator as `[x]`, `x = -|x|`. -/
theorem psi_generator :
    psi (toPoint generator) = (-15132376222941642752 : ℤ) • toPoint generator := by
  have hv := valid_generator
  have h := (eqProj_iff (valid_psiJ hv) (valid_neg (valid_mulAbsX hv))).mp
    eqProj_psiJ_generator
  rw [toPoint_psiJ hv, toPoint_neg (valid_mulAbsX hv), toPoint_mulAbsX hv] at h
  rw [h, ← natCast_zsmul, ← neg_zsmul]
  rfl

private theorem mulMsb_generator_isInfinity :
    (mulMsb generator Fr.modulus 254 generator).isInfinity = true := by
  decide +kernel

/-- `[r]g₂ = 0`. -/
theorem r_smul_generator : Fr.modulus • toPoint generator = 0 := by
  have hv := valid_generator
  have h := (isInfinity_iff (valid_mulMsb hv hv Fr.modulus 254)).mp
    mulMsb_generator_isInfinity
  rw [toPoint_mulMsb hv hv, ← add_nsmul] at h
  have e : 2 ^ 254 + Fr.modulus % 2 ^ 254 = Fr.modulus := by decide +kernel
  rw [e] at h
  exact h

/-- On the curve, `[r]Q = O` iff `ψ(Q) = [x]Q`. -/
theorem rTorsion_iff_psi (Q : curve.toAffine.Point) :
    Fr.modulus • Q = 0 ↔ psiHom Q = (-15132376222941642752 : ℤ) • Q := by
  haveI : Fact (Nat.Prime q) := ⟨q_prime⟩
  have hqr : q ≠ Fr.modulus := by decide +kernel
  refine rTorsion_iff_eigen_phi12 (r := Fr.modulus) (q := q) (x := -15132376222941642752)
    (l2 := 52435875175126190475982595682112313518914282969839895044348538607396160864257)
    (l3 := 15132376222941642752)
    (l4 := 3465144826073652318776269530687742778255120092542420320256)
    psiHom psi_four hqr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ card_point_lt_rrq
    toPoint_generator_ne_zero r_smul_generator psi_generator
    toPoint_P1_ne_zero q_smul_P1 Q
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ⟨-17478625058375396825327531894037437839638094323279965014787890327873034169003,
      -17478625058375396824172483618679553733455667416434933948062845614753339321002,
      by norm_num [Fr.modulus]⟩
  · exact ⟨1732572413036826159388134765343871389127560046271210160128, 1,
      by norm_num [Fr.modulus]⟩
  · exact ⟨3465144826073652318776269530687742778270252468765361963008,
      228988810152649578064853576960394133505, by norm_num [Fr.modulus]⟩

/-- The subgroup test of the implementation decides the spec's `[r]Q = O`. -/
theorem inSubgroup_eq {P : G2} (h : Valid P) :
    inSubgroup P = EthLib.Cryptography.Bls.G2.inSubgroup P := by
  by_cases hinf : P.isInfinity = true
  · rw [inSubgroup, EthLib.Cryptography.Bls.G2.inSubgroup, if_pos hinf, if_pos hinf]
  · rw [inSubgroup, EthLib.Cryptography.Bls.G2.inSubgroup, if_neg hinf, if_neg hinf]
    have hm := valid_mulAbsX h
    rw [Bool.eq_iff_iff, eqProj_iff (valid_psiJ h) (valid_neg hm),
      isInfinity_iff (valid_mulNat h _), toPoint_mulNat h, toPoint_psiJ h,
      toPoint_neg hm, toPoint_mulAbsX h, rTorsion_iff_psi, psiHom_apply, ← natCast_zsmul,
      ← neg_zsmul]
    rfl

end EthLibImpl.Cryptography.Bls.Mirror.G2
