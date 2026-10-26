import EthLib.Cryptography.Bls.Signatures
import EthLib.Cryptography.Bls.Pairing
import EthLib.Cryptography.Bls.HashToCurve

/-! Benchmarks EthLib's BLS on test vectors produced by blst
(`blstbench gen`). Usage: `blsbench VECTORS [OP...]`; with no OP it checks
correctness and runs every benchmark. -/

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Signatures

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexVal cs[2*i]! * 16 + hexVal cs[2*i+1]!))
  return out

structure Vectors where
  msg : ByteArray
  pubkeys : Array ByteArray
  aggs : Array (Nat × ByteArray)

def loadVectors (path : String) : IO Vectors := do
  let mut v : Vectors := ⟨.empty, #[], #[]⟩
  for line in (← IO.FS.lines path) do
    match line.splitOn " " with
    | ["msg", h] => v := { v with msg := unhex h }
    | ["pk", h] => v := { v with pubkeys := v.pubkeys.push (unhex h) }
    | ["agg", n, h] => v := { v with aggs := v.aggs.push (n.toNat!, unhex h) }
    | _ => pure ()
  return v

def Vectors.sig (v : Vectors) (n : Nat) : ByteArray :=
  (v.aggs.find? (·.1 == n)).get!.2

/-- Median ns per op over 5 samples; each sample repeats `f` until `minNs`
has passed. `f` performs `perCall` ops. -/
def timeOp (name : String) (minNs : Nat) (perCall : Nat) (f : Nat → IO Unit) : IO Unit := do
  f 0
  -- `BENCH_ONCE=1`: one call and no timing, for leanprof's exact counts.
  if (← IO.getEnv "BENCH_ONCE").isSome then
    IO.println s!"{name} ran once"
    return
  let mut samples : Array Float := #[]
  for _ in [:5] do
    let start ← IO.monoNanosNow
    let mut iters := 0
    let mut now := start
    while iters == 0 || now - start < minNs do
      f iters
      iters := iters + 1
      now ← IO.monoNanosNow
    samples := samples.push ((now - start).toFloat / (iters * perCall).toFloat)
  let sorted := samples.qsort (· < ·)
  IO.println s!"{name} {sorted[2]!.round} ns"
  (← IO.getStdout).flush

/-- `Fp.add` without the `%`: one conditional subtraction. -/
@[inline] def addCs (a b : Fp) : Fp :=
  if h : a.val + b.val < Fp.modulus then ⟨a.val + b.val, h⟩
  else ⟨a.val + b.val - Fp.modulus, by have := a.isLt; have := b.isLt; omega⟩

/-- `Fp.sub` without the `%`. -/
@[inline] def subCs (a b : Fp) : Fp :=
  if h : b.val ≤ a.val then ⟨a.val - b.val, by have := a.isLt; omega⟩
  else ⟨a.val + Fp.modulus - b.val, by have := b.isLt; omega⟩

def flipBit (b : ByteArray) : ByteArray := b.set! 0 (b.get! 0 ^^^ 1)

def check (v : Vectors) : IO Unit := do
  let ok1 := ethFastAggregateVerify (v.pubkeys.extract 0 1) v.msg (v.sig 1)
  let ok8 := ethFastAggregateVerify (v.pubkeys.extract 0 8) v.msg (v.sig 8)
  let badMsg := ethFastAggregateVerify (v.pubkeys.extract 0 1) (flipBit v.msg) (v.sig 1)
  let badSig := ethFastAggregateVerify (v.pubkeys.extract 0 8) v.msg (v.sig 1)
  IO.println s!"check: verify n=1 {ok1}, n=8 {ok8}, wrong msg {badMsg}, wrong sig {badSig}"
  unless ok1 && ok8 && !badMsg && !badSig do
    throw (IO.userError "EthLib disagrees with blst on the test vectors")

def run (v : Vectors) (op : String) : IO Unit := do
  let micro := 200000000  -- 0.2 s per sample
  let pk0 := v.pubkeys[0]!
  let sig1 := v.sig 1
  let p ← match G1.uncompress pk0 with
    | .ok p => pure p | .error _ => throw (IO.userError "pk")
  let s ← match G2.uncompress sig1 with
    | .ok s => pure s | .error _ => throw (IO.userError "sig")
  let q ← match HashToCurve.hashToG2 v.msg DST with
    | .ok q => pure q | .error _ => throw (IO.userError "h2c")
  let f := millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)
  -- Inputs come out of a ref and results go into one, so the compiler can
  -- neither hoist the work out of the loop nor drop it.
  let fpIn ← IO.mkRef (p.x, p.y)
  let fpSink ← IO.mkRef (0 : Nat)
  let fp12In ← IO.mkRef f
  let fp12Sink ← IO.mkRef Fp12.one
  let boolSink ← IO.mkRef false
  match op with
  | "fp_mul" => timeOp op micro 1000 fun _ => do
      let (a, b) ← fpIn.get
      let mut x := a
      for _ in [:1000] do x := x * b
      fpSink.set x.val
  | "fp_add" => timeOp op micro 1000 fun _ => do
      let (a, b) ← fpIn.get
      let mut x := a
      for _ in [:1000] do x := x + b
      fpSink.set x.val
  | "fp_sub" => timeOp op micro 1000 fun _ => do
      let (a, b) ← fpIn.get
      let mut x := a
      for _ in [:1000] do x := x - b
      fpSink.set x.val
  | "fp_add_cs" => timeOp op micro 1000 fun _ => do
      let (a, b) ← fpIn.get
      let mut x := a
      for _ in [:1000] do x := addCs x b
      fpSink.set x.val
  | "fp_sub_cs" => timeOp op micro 1000 fun _ => do
      let (a, b) ← fpIn.get
      let mut x := a
      for _ in [:1000] do x := subCs x b
      fpSink.set x.val
  | "nat_mul_shr" => timeOp op micro 1000 fun _ => do
      -- Three bignum ops, none a division: the 381-bit product, a shift back
      -- to 381 bits, and an OR of the top bit so the value cannot decay.
      let (a, b) ← fpIn.get
      let top := 1 <<< 380
      let mut x := a.val ||| top
      for _ in [:1000] do x := ((x * b.val) >>> 381) ||| top
      fpSink.set x
  | "setup" => pure ()
  | "fp_inverse" => timeOp op micro 10 fun _ => do
      let (a, _) ← fpIn.get
      let mut x := a
      for _ in [:10] do x := x.inverse
      fpSink.set x.val
  | "fp_sqrt" => timeOp op micro 10 fun _ => do
      let (a, _) ← fpIn.get
      let mut x := a
      for _ in [:10] do
        x := match Fp.sqrt x with | .ok y => y | .error _ => x + 1
      fpSink.set x.val
  | "fp12_mul" => timeOp op micro 100 fun _ => do
      let a ← fp12In.get
      let mut x := a
      for _ in [:100] do x := x * a
      fp12Sink.set x
  | "fp12_inverse" => timeOp op micro 1 fun _ => do
      fp12Sink.set (← fp12In.get).inverse
  | "g1_uncompress" => timeOp op micro 1 fun i => do
      boolSink.set (G1.uncompress v.pubkeys[i % v.pubkeys.size]!).isOk
  | "g1_key_validate" => timeOp op micro 1 fun i => do
      boolSink.set (G1.keyValidate v.pubkeys[i % v.pubkeys.size]!).isOk
  | "g2_uncompress" => timeOp op micro 1 fun _ => do
      boolSink.set (G2.uncompress (← (← IO.mkRef sig1).get)).isOk
  | "g2_sig_validate" => timeOp op micro 1 fun _ => do
      let b ← (← IO.mkRef sig1).get
      boolSink.set (match G2.uncompress b with | .ok s => G2.inSubgroup s | .error _ => false)
  | "hash_to_g2" => timeOp op micro 1 fun _ => do
      let m ← (← IO.mkRef v.msg).get
      boolSink.set (HashToCurve.hashToG2 m DST).isOk
  | "miller_loop" => timeOp op micro 1 fun _ => do
      let pp ← (← IO.mkRef p).get
      fp12Sink.set (millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 pp))
  | "final_exp" => timeOp op micro 1 fun _ => do
      fp12Sink.set (finalExponentiation (← fp12In.get))
  | "pairing_check_2" => timeOp op micro 1 fun _ => do
      let ss ← (← IO.mkRef s).get
      boolSink.set (pairingCheck #[(G1.generator, ss), (G1.neg p, q)])
  | _ =>
    match op.splitOn ":" with
    | ["fast_agg_verify", n] => do
      let n := n.toNat!
      let pks := v.pubkeys.extract 0 n
      let sig := v.sig n
      timeOp s!"fast_agg_verify n={n}" micro 1 fun _ => do
        boolSink.set (ethFastAggregateVerify (← (← IO.mkRef pks).get) v.msg sig)
    | ["aggregate_pubkeys", n] => do
      let n := n.toNat!
      let pks := v.pubkeys.extract 0 n
      timeOp s!"aggregate_pubkeys n={n}" micro 1 fun _ => do
        boolSink.set (ethAggregatePubkeys (← (← IO.mkRef pks).get)).toBool
    | _ => throw (IO.userError s!"unknown op {op}")

def allOps : List String :=
  [ "fp_mul", "fp_add", "fp_inverse", "fp_sqrt", "fp12_mul", "fp12_inverse"
  , "g1_uncompress", "g1_key_validate", "g2_uncompress", "g2_sig_validate"
  , "hash_to_g2", "miller_loop", "final_exp", "pairing_check_2"
  , "fast_agg_verify:1", "aggregate_pubkeys:1", "fast_agg_verify:8", "aggregate_pubkeys:8"
  , "fast_agg_verify:64", "aggregate_pubkeys:64" ]

def main (args : List String) : IO Unit := do
  let path :: ops := args | throw (IO.userError "usage: blsbench VECTORS [OP...]")
  let v ← loadVectors path
  if ops.isEmpty then
    check v
    for op in allOps do run v op
  else
    for op in ops do
      if op == "check" then check v else run v op
