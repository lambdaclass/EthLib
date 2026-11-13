import EthLib.Cryptography.Proofs.Bls.G2Group
import EthLib.Cryptography.Proofs.Bls.G2Equiv
import EthLib.Cryptography.Proofs.Bls.G2Validity

/-!
# Proofs: the `G2` group structure

The spec proves that its `G2` (Jacobian points of `y² = x³ + 4(1 + i)` over
`Fp2`) is the elliptic-curve group: `EthLib.Cryptography.Proofs.Bls.G2Group`
defines `curve`, `rep`, `Valid` and `toPoint` and proves that `zero`, `neg`,
`double`, `add`, `mulNat` and `mul` are the group law (`toPoint_zero`,
`toPoint_neg`, `toPoint_double`, `toPoint_add`, `toPoint_mulNat`,
`toPoint_mul`, with the `valid_*` preservation lemmas), and
`EthLib.Cryptography.Proofs.Bls.G2Equiv` that `projectiveEq` decides equality
of the denoted points. The implementation's proofs use those directly; this
file only adds a short name for the infinity test.
-/

namespace EthLib.Cryptography.Bls.G2

/-- A valid triple is the point at infinity exactly when it denotes `0`. -/
theorem isInfinity_iff {P : G2} (hP : Valid P) : P.isInfinity = true ↔ toPoint P = 0 :=
  isInfinity_eq_true_iff_toPoint_eq_zero hP

end EthLib.Cryptography.Bls.G2
