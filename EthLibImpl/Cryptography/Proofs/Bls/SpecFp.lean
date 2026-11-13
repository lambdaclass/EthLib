import EthLib.Cryptography.Proofs.Bls.FpZMod

/-!
# Proofs: the spec's `Fp` through `ZMod p`

The spec's `Fp` is held in Montgomery form, and proofs reach it only through
its ring isomorphism `Fp.toZMod : Fp ≃+* ZMod p` (`Proofs.Bls.FpZMod`). The
spec's lemmas there cover the ring operations and `ofNat`; these add the two
more that the implementation's proofs use.
-/

namespace EthLibImpl.Cryptography.Bls.SpecFp

/-! ## The spec field through `ZMod p`

The spec's `Fp.toZMod` lemmas cover the ring operations and `ofNat`; these
add the two that the implementation's proofs also use. -/

open scoped EthLib.Cryptography.Bls.Fp

local notation "S" => EthLib.Cryptography.Bls.Fp

/-- Monoid power (on the spec's scoped field instance) commutes with `toZMod`. -/
theorem toZMod_pow (x : S) (n : Nat) :
    EthLib.Cryptography.Bls.Fp.toZMod (x ^ n) = EthLib.Cryptography.Bls.Fp.toZMod x ^ n :=
  map_pow EthLib.Cryptography.Bls.Fp.toZMod x n

/-- `ZMod.val` after `toZMod` is the spec's `val`. -/
theorem val_toZMod (x : S) : (EthLib.Cryptography.Bls.Fp.toZMod x).val = x.val :=
  (EthLib.Cryptography.Bls.Fp.val_eq x).symm

end EthLibImpl.Cryptography.Bls.SpecFp
