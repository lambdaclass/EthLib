import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.CofactorPrimes
import EthLib.Cryptography.Proofs.Bls.CofactorCardinality
import EthLib.Cryptography.Proofs.Bls.CofactorCertificateHelpers
import EthLibImpl.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: the order of the twist curve and a point of order `q`

Three facts about `E'(Fp2)` (the spec's `G2` curve):

* `card_point_lt_rrq`: the curve has fewer than `r² · q` points. The spec's
  `G2.card_point_le` bounds it by `2p² + 1` (a point is determined by `x` and
  the sign of `y`).
* `q_prime`: the 448-bit prime `q`, the largest prime factor of the `G2`
  cofactor, is prime. This is the spec's `CofactorPrimes.largePrime_prime`
  (a Pratt tree of Lucas certificates).
* `P1_order`: an explicit point `P1` of order `q`, i.e. `toPoint P1 ≠ 0` and
  `q • toPoint P1 = 0`. The kernel runs the spec's fuelled ladder
  `G2.mulNatAux` in the model of `Fp` (`CofactorCertificate.nsmul_zero_cert`).

The spec's own subgroup check needs none of this any more: it is the `ψ` test,
and `EthLib.Cryptography.Proofs.Bls.G2SubgroupSpan` pins down the whole group
(`G2.card_point_eq_candidate`).
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2 (Valid toPoint curve valid_of_affine_equation
  isInfinity_eq_true_iff_toPoint_eq_zero)

set_option maxRecDepth 8000

/-! ## `q` is prime -/

/-- The largest prime factor of the `G2` cofactor (448 bits). -/
abbrev q : Nat :=
  402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-- `q` is prime, by the spec's Pratt tree of Lucas certificates. -/
theorem q_prime : Nat.Prime q := CofactorPrimes.largePrime_prime

/-! ## The order of the curve -/

/-- The twist curve has fewer than `r² · q` points. -/
theorem card_point_lt_rrq : Nat.card curve.toAffine.Point < Fr.modulus * Fr.modulus * q := by
  have h := EthLib.Cryptography.Bls.G2.card_point_le
  have hlt : 2 * Fp.modulus ^ 2 + 1 < Fr.modulus * Fr.modulus * q := by decide
  omega

/-! ## A point of order `q` -/

/-- A point of order `q` on the twist, in affine coordinates. -/
def P1 : G2 :=
  ⟨⟨Fp.ofNat 0xffd5c7041594275710810912f235d186a22fbb5433a8e60b514da2bcb92a91ab996b90fee5916ff94feeb24500f5717,
    Fp.ofNat 0x754ea28f6cdfe1c0852776f2806261cd6d0ee0b5a41856e67850e23f8b9f2ae2c2a714a83d44264b9690444ad2dd925⟩,
   ⟨Fp.ofNat 0x195a84dedaff659d2b408c0afbc06f860cac7f6f974e6dea31394c600236c4bcfb34e597e8312b5e2b93dc85cff852ce,
    Fp.ofNat 0xb34aaa1ac510f29f9f993112f20698e9d669d6a48fe7e2937d86d6680e641fcbb27902586329e5f0cb3941e6aa58cd9⟩,
   Fp2.one⟩

/-- `P1` is a valid curve point. -/
theorem valid_P1 : Valid P1 :=
  valid_of_affine_equation (by decide_eq_at_model [EthLib.Cryptography.Bls.G2.map_bTwist])

/-- `P1` is not the point at infinity. -/
theorem toPoint_P1_ne_zero : toPoint P1 ≠ 0 := by
  intro hz
  have h := (isInfinity_eq_true_iff_toPoint_eq_zero valid_P1).mpr hz
  exact Bool.noConfusion h

/-- `[q]P1 = 0`: the kernel runs the ladder in the model of `Fp`. -/
theorem q_smul_P1 : q • toPoint P1 = 0 :=
  CofactorCertificate.nsmul_zero_cert P1 valid_P1 _ 449 (by decide +kernel)
    (by decide_g2_at_model [P1])

end EthLibImpl.Cryptography.Bls.Mirror.G2
