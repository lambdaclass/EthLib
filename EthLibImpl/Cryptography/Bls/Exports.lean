import EthLibImpl.Cryptography.Bls.Signatures
import EthLib.Cryptography.Bls.Errors

/-!
# `Bls.Exports`

C-ABI exports, same shapes as the spec's (`eth_bls_*`), under an
`eth_bls_impl_` prefix so both can be linked into one binary.

An operation returns its value, or the code and the message of its error,
as the spec's exports do. The result type and `runBls` are restated here
rather than imported, so that this library stays clear of the spec's export
library (and of Mathlib); `Equivalence` proves them the spec's.
-/

namespace EthLibImpl.Cryptography.Bls.Exports

open EthLib.Cryptography.Bls (BlsError)
open EthLibImpl.Cryptography.Bls.Signatures

/-- A value, or the code and the message of an error (the spec's `EthLib.Exports.Result`). -/
abbrev Result (α : Type) := Except (UInt32 × String) α

/-- Run a fallible BLS computation, with its error as a code and a message. -/
def runBls {α : Type} (act : Except BlsError α) : Result α :=
  act.mapError fun e => (e.code, e.message)

/-- Every public key must be 48 bytes long, or the first that is not is the error.

The spec's export reads every key before it sums any, so a key of the wrong
size is reported before an earlier key that fails validation. -/
def checkPubkeySizes (pubkeys : Array ByteArray) : Except BlsError Unit :=
  pubkeys.forM fun pk => if pk.size = 48 then pure () else throw (.badPubkeySize pk.size)

@[export eth_bls_impl_aggregate_pubkeys]
def ethAggregatePubkeysExport (pubkeys : Array ByteArray) : Result ByteArray :=
  runBls do
    checkPubkeySizes pubkeys
    ethAggregatePubkeys pubkeys

@[export eth_bls_impl_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : Array ByteArray) (msg : ByteArray) (sig : ByteArray) : Result UInt8 :=
  return if ethFastAggregateVerify pubkeys msg sig then 1 else 0

end EthLibImpl.Cryptography.Bls.Exports
