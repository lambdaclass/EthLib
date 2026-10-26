import EthLibImpl.Cryptography.Proofs.Bls.Fp2
import EthLibImpl.Cryptography.Bls.G2

/-!
# The implementation's G2 points as spec points

`Canonical` and `toSpec` for `EthLibImpl.Cryptography.Bls.G2`, shared by the
G2, hash-to-curve and pairing proofs.
-/

namespace EthLibImpl.Cryptography.Bls.G2

/-- Every coordinate is canonical. -/
def Canonical (p : G2) : Prop := p.x.Canonical ∧ p.y.Canonical ∧ p.z.Canonical

/-- The spec point with the same coordinates. -/
def toSpec (p : G2) : EthLib.Cryptography.Bls.G2 := ⟨p.x.toSpec, p.y.toSpec, p.z.toSpec⟩

end EthLibImpl.Cryptography.Bls.G2
