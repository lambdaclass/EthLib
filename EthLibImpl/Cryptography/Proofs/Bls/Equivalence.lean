import EthLibImpl.Cryptography.Bls.Exports
import EthLib.Cryptography.Bls.Exports
import EthLibImpl.Cryptography.Proofs.Bls.SigImpl
import EthLibImpl.Cryptography.Proofs.Bls.CompressG2
import EthLibImpl.Cryptography.Proofs.Bls.HashImpl
import EthLibImpl.Cryptography.Proofs.Bls.PairingImpl
import EthLibImpl.Cryptography.Proofs.Bls.MillerLoop

/-!
# End-to-end equivalence with EthLib

The implementation's exported functions return the spec's results on every
input. The chain is implementation → mirror (structural, `*Impl.lean`) →
spec (mathematical, `SigMath`, `HashMath`, `MillerLoop`, `FinalExp`).
-/

namespace EthLibImpl.Cryptography.Bls.Signatures

open EthLibImpl.Cryptography.Bls

/-- `coreVerifyPoint` of the implementation equals the mirror's for a
canonical public key: the G2 decompression, subgroup check, hash and
pairing each map to their mirror.

The subgroup checks and pairing checks are generalized to variables before
any case split: otherwise the kernel, checking the definitional steps of
the split, reduces them on symbolic points ("deep recursion"). -/
theorem coreVerifyHyp : CoreVerifyHyp := by
  intro pk msg sig hpk
  obtain ⟨hu, hcu⟩ := G2.uncompress_spec sig
  obtain ⟨hh, hch⟩ := HashToCurve.hashToG2_spec msg DST
  have hsub : ∀ q, G2.Canonical q → G2.inSubgroup q = Mirror.G2.inSubgroup (G2.toSpec q) :=
    fun _ hq => G2.inSubgroup_spec hq
  have hpc : ∀ q h, G2.Canonical q → G2.Canonical h →
      pairingCheck #[(G1.generator, q), (G1.neg pk, h)]
        = Mirror.pairingCheck #[(EthLib.Cryptography.Bls.G1.generator, G2.toSpec q),
            (EthLib.Cryptography.Bls.G1.neg (G1.toSpec pk), G2.toSpec h)] := by
    intro q h hq hh'
    obtain ⟨hgc, hgs⟩ := G1.generator_spec
    obtain ⟨hnc, hns⟩ := G1.neg_spec hpk
    rw [pairingCheck_spec _ (by
      intro pq hmem
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨hgc, hq⟩
      · exact ⟨hnc, hh'⟩)]
    simp only [List.map_toArray, List.map_cons, List.map_nil, hgs, hns]
  have hD : DST = EthLib.Cryptography.Bls.Signatures.DST := rfl
  unfold coreVerifyPoint Mirror.Signatures.coreVerifyPoint
  rw [G1.isInfinity_spec hpk, ← hu, ← hD, ← hh]
  generalize G2.uncompress sig = U at hcu ⊢
  generalize HashToCurve.hashToG2 msg DST = H at hch ⊢
  generalize G2.inSubgroup = f at hsub ⊢
  generalize Mirror.G2.inSubgroup = g at hsub ⊢
  generalize pairingCheck = pc at hpc ⊢
  generalize Mirror.pairingCheck = mpc at hpc ⊢
  by_cases hinf : (G1.toSpec pk).isInfinity = true
  · simp only [hinf, if_true]
  simp only [hinf, Bool.false_eq_true, if_false]
  by_cases hs : sig.size = 96
  swap
  · simp only [ne_eq, hs, not_false_eq_true, if_true]
  simp only [hs, ne_eq, not_true_eq_false, if_false]
  -- `show` rather than `simp`: the kernel cannot check simp's match
  -- reduction here without deep recursion.
  cases U with
  | error e => show false = false; rfl
  | ok q =>
    have hq := hcu q rfl
    show (if (!f q) = true then false else _) = (if (!g (G2.toSpec q)) = true then false else _)
    rw [hsub q hq]
    cases g (G2.toSpec q)
    · have ht : (!false) = true := rfl
      rw [if_pos ht, if_pos ht]
    have hf : ¬ (!true) = true := Bool.false_ne_true
    rw [if_neg hf, if_neg hf]
    cases H with
    | error e => show false = false; rfl
    | ok h =>
      show pc #[(G1.generator, q), (G1.neg pk, h)]
        = mpc #[(EthLib.Cryptography.Bls.G1.generator, G2.toSpec q),
            (EthLib.Cryptography.Bls.G1.neg (G1.toSpec pk), G2.toSpec h)]
      exact hpc q h hq (hch h rfl)

/-- **`eth_fast_aggregate_verify`.** The implementation returns EthLib's
result on every input. -/
theorem ethFastAggregateVerify_eq_ethlib (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig
      = EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig :=
  ethFastAggregateVerify_eq_spec coreVerifyHyp Mirror.pairingCheck_eq
    Mirror.HashToCurve.hashToG2_eq pks msg sig

/-- **`eth_aggregate_pubkeys`.** The implementation returns EthLib's result
on every input, errors included. -/
theorem ethAggregatePubkeys_eq_ethlib (pks : Array ByteArray) :
    ethAggregatePubkeys pks = EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks :=
  ethAggregatePubkeys_eq_spec pks

end EthLibImpl.Cryptography.Bls.Signatures

namespace EthLibImpl.Cryptography.Bls.Exports

/-- The exported `eth_bls_impl_aggregate_pubkeys` is EthLib's
`eth_bls_aggregate_pubkeys`. -/
theorem ethAggregatePubkeysExport_eq :
    ethAggregatePubkeysExport = EthLib.Cryptography.Bls.Exports.ethAggregatePubkeysExport := by
  funext pks
  unfold ethAggregatePubkeysExport EthLib.Cryptography.Bls.Exports.ethAggregatePubkeysExport
  rw [Signatures.ethAggregatePubkeys_eq_ethlib]

/-- The exported `eth_bls_impl_fast_aggregate_verify` is EthLib's
`eth_bls_fast_aggregate_verify`. -/
theorem ethFastAggregateVerifyExport_eq :
    ethFastAggregateVerifyExport
      = EthLib.Cryptography.Bls.Exports.ethFastAggregateVerifyExport := by
  funext pks msg sig
  unfold ethFastAggregateVerifyExport EthLib.Cryptography.Bls.Exports.ethFastAggregateVerifyExport
  rw [Signatures.ethFastAggregateVerify_eq_ethlib]

end EthLibImpl.Cryptography.Bls.Exports

namespace EthLibImpl.Cryptography.Bls

/-- The implementation's pairing check equals EthLib's for canonical
inputs (every point the implementation constructs is canonical). -/
theorem pairingCheck_eq_ethlib (pairs : Array (G1 × G2))
    (h : ∀ pq ∈ pairs, pq.1.Canonical ∧ pq.2.Canonical) :
    pairingCheck pairs
      = EthLib.Cryptography.Bls.pairingCheck
          (pairs.map fun pq => (G1.toSpec pq.1, G2.toSpec pq.2)) := by
  rw [pairingCheck_spec pairs h, Mirror.pairingCheck_eq]

end EthLibImpl.Cryptography.Bls
