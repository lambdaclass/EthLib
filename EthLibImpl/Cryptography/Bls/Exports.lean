import EthLibImpl.Cryptography.Bls.Signatures
import EthLib.Cryptography.Bls.Errors

/-!
# `Bls.Exports`

C-ABI exports, same shapes as the spec's (`eth_bls_*`), under an
`eth_bls_impl_` prefix so both can be linked into one binary.
-/

namespace EthLibImpl.Cryptography.Bls.Exports

open EthLibImpl.Cryptography.Bls.Signatures

@[export eth_bls_impl_aggregate_pubkeys]
def ethAggregatePubkeysExport
    (pubkeys : @& Array ByteArray) : IO ByteArray :=
  EthLib.Cryptography.Bls.runBls (ethAggregatePubkeys pubkeys)

@[export eth_bls_impl_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : @& Array ByteArray) (msg : @& ByteArray) (sig : @& ByteArray)
    : IO UInt8 := do
  return if ethFastAggregateVerify pubkeys msg sig then 1 else 0

end EthLibImpl.Cryptography.Bls.Exports
