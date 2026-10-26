import EthLib.Cryptography.Bls
import EthLibImpl

/-! Differential tests and benchmarks: `EthLibImpl` against `EthLib`. -/

namespace ImplBench
abbrev S := EthLib.Cryptography.Bls.Fp
abbrev S2 := EthLib.Cryptography.Bls.Fp2
abbrev S6 := EthLib.Cryptography.Bls.Fp6
abbrev S12 := EthLib.Cryptography.Bls.Fp12
abbrev I := EthLibImpl.Cryptography.Bls.Fp
abbrev I2 := EthLibImpl.Cryptography.Bls.Fp2
abbrev I6 := EthLibImpl.Cryptography.Bls.Fp6
abbrev I12 := EthLibImpl.Cryptography.Bls.Fp12

def toS (a : I) : S := EthLib.Cryptography.Bls.Fp.ofNat a.toNat
def toS2 (a : I2) : S2 := ⟨toS a.c0, toS a.c1⟩
def toS6 (a : I6) : S6 := ⟨toS2 a.c0, toS2 a.c1, toS2 a.c2⟩
def toS12 (a : I12) : S12 := ⟨toS6 a.c0, toS6 a.c1⟩
def ofS (a : S) : I := EthLibImpl.Cryptography.Bls.Fp.ofNat a.val

/-- xorshift64* PRNG state. -/
structure Rng where s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 0x2545F4914F6CDD1D, ⟨x⟩)

def Rng.nat (g : Rng) (words : Nat) : Nat × Rng := Id.run do
  let mut g := g
  let mut acc := 0
  for _ in [0:words] do
    let (w, g') := g.next
    g := g'
    acc := (acc <<< 64) ||| w.toNat
  return (acc, g)

def Rng.fp (g : Rng) : I × Rng :=
  let (n, g) := g.nat 7
  (EthLibImpl.Cryptography.Bls.Fp.ofNat n, g)
def Rng.fp2 (g : Rng) : I2 × Rng :=
  let (a, g) := g.fp; let (b, g) := g.fp; (EthLibImpl.Cryptography.Bls.Fp2.mk a b, g)
def Rng.fp6 (g : Rng) : I6 × Rng :=
  let (a, g) := g.fp2; let (b, g) := g.fp2; let (c, g) := g.fp2; (⟨a, b, c⟩, g)
def Rng.fp12 (g : Rng) : I12 × Rng :=
  let (a, g) := g.fp6; let (b, g) := g.fp6; (⟨a, b⟩, g)

def report (name : String) (ok : Bool) : IO Unit :=
  IO.println s!"{if ok then "PASS" else "FAIL"}  {name}"

def fieldTests (iters : Nat) : IO Unit := do
  let mut g : Rng := ⟨0x9E3779B97F4A7C15⟩
  let mut okFp := true
  let mut okFp2 := true
  let mut okSqrt := true
  let mut okFp6 := true
  let mut okFp12 := true
  for k in [0:iters] do
    let (a, g1) := g.fp; let (b, g2) := g1.fp; g := g2
    let a := if k == 0 then EthLibImpl.Cryptography.Bls.Fp.zero else a
    let sa := toS a; let sb := toS b
    okFp := okFp && toS (a + b) == sa + sb && toS (a - b) == sa - sb && toS (a * b) == sa * sb
      && toS (-a) == -sa && toS a.inverse == sa.inverse
      && (match a.sqrt, sa.sqrt with
          | .ok x, .ok y => toS x == y | .error _, .error _ => true | _, _ => false)
      && (ofS sa).toNat == a.toNat && a.toBytesBE == sa.toBytesBE
      && (match EthLibImpl.Cryptography.Bls.Fp.fromBytesBE sa.toBytesBE with
          | .ok x => toS x == sa | _ => false)
      && a.signBit == EthLib.Cryptography.Bls.Fp.signBit sa
    let (x, g1) := g.fp2; let (y, g2) := g1.fp2; g := g2
    let sx := toS2 x; let sy := toS2 y
    okFp2 := okFp2 && (toS2 (x * y)).beq (sx * sy) && (toS2 x.sqr).beq (sx * sx)
      && (toS2 (x + y)).beq (sx + sy) && (toS2 (x - y)).beq (sx - sy)
      && (toS2 x.inverse).beq sx.inverse && (toS2 x.mulByXi).beq sx.mulByOnePlusI
    -- sqrt: same success; the impl's root squares back; also try a square
    for z in [x, x.sqr, EthLibImpl.Cryptography.Bls.Fp2.mk x.c0 EthLibImpl.Cryptography.Bls.Fp.zero] do
      let sz := toS2 z
      okSqrt := okSqrt && (match z.sqrt, EthLib.Cryptography.Bls.Fp2.sqrt sz with
        | .ok r, .ok r' => (toS2 r.sqr).beq sz && ((toS2 r).beq r' || (toS2 (-r)).beq r')
        | .error _, .error _ => true
        | _, _ => false)
    let (u, g1) := g.fp6; let (v, g2) := g1.fp6; g := g2
    let su := toS6 u; let sv := toS6 v
    okFp6 := okFp6 && (toS6 (u * v)).beq (su * sv) && (toS6 u.sqr).beq (su * su)
      && (toS6 u.inverse).beq su.inverse
      && (toS6 (u.mulBy01 v.c0 v.c1)).beq (su * ⟨sv.c0, sv.c1, EthLib.Cryptography.Bls.Fp2.zero⟩)
    let (m, g1) := g.fp12; let (n, g2) := g1.fp12; g := g2
    let sm := toS12 m; let sn := toS12 n
    let line : S12 := ⟨⟨sn.c0.c0, sn.c0.c1, EthLib.Cryptography.Bls.Fp2.zero⟩,
                       ⟨EthLib.Cryptography.Bls.Fp2.zero, sn.c1.c1, EthLib.Cryptography.Bls.Fp2.zero⟩⟩
    -- a cyclotomic element: (conj m / m)^(p^2+1)
    let h := m.conj * m.inverse
    let cyc := h.frobenius2 * h
    okFp12 := okFp12 && (toS12 (m * n)).beq (sm * sn) && (toS12 m.sqr).beq (sm * sm)
      && (toS12 m.inverse).beq sm.inverse
      && (toS12 (m.mulBy014 n.c0.c0 n.c0.c1 n.c1.c1)).beq (sm * line)
      && (toS12 m.frobenius1).beq (EthLib.Cryptography.Bls.Fp12.powNat sm EthLib.Cryptography.Bls.Fp.modulus)
      && (toS12 m.frobenius2).beq (toS12 m.frobenius1.frobenius1)
      && (toS12 cyc.cycSqr).beq (toS12 (cyc * cyc))
  report "Fp add/sub/mul/neg/inv/sqrt/bytes/signBit" okFp
  report "Fp2 mul/sqr/add/sub/inv/xi" okFp2
  report "Fp2 sqrt (same success, valid root, ± spec root)" okSqrt
  report "Fp6 mul/sqr/inv/mulBy01" okFp6
  report "Fp12 mul/sqr/inv/mulBy014/frobenius/cycSqr" okFp12


/-! ## Curve, compression, hashing, pairing and signature tests -/

abbrev SG1 := EthLib.Cryptography.Bls.G1
abbrev SG2 := EthLib.Cryptography.Bls.G2
abbrev IG1 := EthLibImpl.Cryptography.Bls.G1
abbrev IG2 := EthLibImpl.Cryptography.Bls.G2

def toSG1 (p : IG1) : SG1 := ⟨toS p.x, toS p.y, toS p.z⟩
def toSG2 (p : IG2) : SG2 := ⟨toS2 p.x, toS2 p.y, toS2 p.z⟩
def eqG1 (a : SG1) (b : SG1) : Bool := a.x.beq b.x && a.y.beq b.y && a.z.beq b.z
def eqG2 (a : SG2) (b : SG2) : Bool := a.x.beq b.x && a.y.beq b.y && a.z.beq b.z

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

def flipBit (b : ByteArray) : ByteArray := b.set! 0 (b.get! 0 ^^^ 1)

/-- A curve point on `E` (not necessarily in `G1`) from a seed. -/
partial def randG1Curve (g : Rng) : IG1 × Rng :=
  let (x, g) := g.fp
  let rhs := x.sqr * x + EthLibImpl.Cryptography.Bls.Fp.ofNat 4
  match rhs.sqrt with
  | .ok y => (⟨x, y, EthLibImpl.Cryptography.Bls.Fp.one⟩, g)
  | .error _ => randG1Curve g

/-- A curve point on `E'` (not necessarily in `G2`) from a seed. -/
partial def randG2Curve (g : Rng) : IG2 × Rng :=
  let (x, g) := g.fp2
  let rhs := x.sqr * x + EthLibImpl.Cryptography.Bls.G2.bTwist
  match rhs.sqrt with
  | .ok y => (⟨x, y, EthLibImpl.Cryptography.Bls.Fp2.one⟩, g)
  | .error _ => randG2Curve g

/-- `h₂ / 13`: maps a twist point to one of order dividing 13. -/
def h2Over13 : Nat :=
  0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5 / 13

def curveTests (v : Vectors) (iters : Nat) : IO Unit := do
  let mut g : Rng := ⟨0x1234567890ABCDEF⟩
  let mut ok1 := true
  let mut ok2 := true
  let mut okC := true
  for _ in [0:iters] do
    let (k, g') := g.nat 1; g := g'
    let p := EthLibImpl.Cryptography.Bls.G1.mulNat EthLibImpl.Cryptography.Bls.G1.generator k
    let sp := EthLib.Cryptography.Bls.G1.mulNat EthLib.Cryptography.Bls.G1.generator k
    let (r, g') := randG1Curve g; g := g'
    let sr := toSG1 r
    ok1 := ok1 && eqG1 (toSG1 p) sp && eqG1 (toSG1 (p.add r)) (sp.add sr)
      && eqG1 (toSG1 (r.add p)) (sr.add sp) && eqG1 (toSG1 p.double) sp.double
      && eqG1 (toSG1 (p.add p)) (sp.add sp) && eqG1 (toSG1 (p.add p.neg)) (sp.add sp.neg)
      && EthLibImpl.Cryptography.Bls.G1.compress p == EthLib.Cryptography.Bls.G1.compress sp
      && EthLibImpl.Cryptography.Bls.G1.inSubgroup r == EthLib.Cryptography.Bls.G1.inSubgroup sr
      && EthLibImpl.Cryptography.Bls.G1.inSubgroup p == EthLib.Cryptography.Bls.G1.inSubgroup sp
    let bytes := EthLib.Cryptography.Bls.G1.compress sr
    okC := okC && (match EthLibImpl.Cryptography.Bls.G1.uncompress bytes,
                        EthLib.Cryptography.Bls.G1.uncompress bytes with
      | .ok a, .ok b => eqG1 (toSG1 a) b | .error e, .error e' => e.message == e'.message | _, _ => false)
      && (EthLibImpl.Cryptography.Bls.G1.keyValidate bytes).isOk
           == (EthLib.Cryptography.Bls.G1.keyValidate bytes).isOk
    -- G2: generator multiples, random twist points, and order-13 points
    let (k2, g') := g.nat 1; g := g'
    let q := EthLibImpl.Cryptography.Bls.G2.mulNat EthLibImpl.Cryptography.Bls.G2.generator k2
    let sq := EthLib.Cryptography.Bls.G2.mulNat EthLib.Cryptography.Bls.G2.generator k2
    let (t, g') := randG2Curve g; g := g'
    let st := toSG2 t
    let small := EthLibImpl.Cryptography.Bls.G2.mulNat t h2Over13
    ok2 := ok2 && eqG2 (toSG2 q) sq && eqG2 (toSG2 (q.add t)) (sq.add st)
      && eqG2 (toSG2 q.double) sq.double
      && EthLibImpl.Cryptography.Bls.G2.compress q == EthLib.Cryptography.Bls.G2.compress sq
      && EthLibImpl.Cryptography.Bls.G2.compress t == EthLib.Cryptography.Bls.G2.compress st
      && EthLibImpl.Cryptography.Bls.G2.inSubgroup t == EthLib.Cryptography.Bls.G2.inSubgroup st
      && EthLibImpl.Cryptography.Bls.G2.inSubgroup q == EthLib.Cryptography.Bls.G2.inSubgroup sq
      && EthLibImpl.Cryptography.Bls.G2.inSubgroup small
           == EthLib.Cryptography.Bls.G2.inSubgroup (toSG2 small)
    let bytes2 := EthLib.Cryptography.Bls.G2.compress st
    for b in [bytes2, flipBit bytes2, bytes2.set! 5 0x77] do
      okC := okC && (match EthLibImpl.Cryptography.Bls.G2.uncompress b,
                          EthLib.Cryptography.Bls.G2.uncompress b with
        | .ok a, .ok b => eqG2 (toSG2 a) b | .error e, .error e' => e.message == e'.message | _, _ => false)
  -- vector pubkeys and signatures, and the infinity encodings
  for pk in v.pubkeys.extract 0 8 do
    okC := okC && (EthLibImpl.Cryptography.Bls.G1.keyValidate pk).isOk
                    == (EthLib.Cryptography.Bls.G1.keyValidate pk).isOk
  for (_, sig) in v.aggs do
    okC := okC && (match EthLibImpl.Cryptography.Bls.G2.uncompress sig,
                        EthLib.Cryptography.Bls.G2.uncompress sig with
      | .ok a, .ok b => eqG2 (toSG2 a) b && EthLibImpl.Cryptography.Bls.G2.inSubgroup a
      | _, _ => false)
  okC := okC && (EthLibImpl.Cryptography.Bls.G1.keyValidate
                    EthLibImpl.Cryptography.Bls.G1.infinityBytes).isOk == false
  report "G1 add/double/neg/mulNat/compress/inSubgroup (exact triples)" ok1
  report "G2 add/double/mulNat/compress/inSubgroup incl. order-13 points" ok2
  report "uncompress/keyValidate (same values and errors)" okC

def hashTests (iters : Nat) : IO Unit := do
  let mut g : Rng := ⟨0xCAFEF00DCAFEF00D⟩
  let mut ok := true
  for i in [0:iters] do
    let (n, g') := g.nat 4; g := g'
    let msg := (EthLib.Cryptography.Bls.Fr.toBytesBE (EthLib.Cryptography.Bls.Fr.ofNat n)).extract 0 (i % 33)
    ok := ok && (match EthLibImpl.Cryptography.Bls.HashToCurve.hashToG2 msg
                         EthLibImpl.Cryptography.Bls.Signatures.DST,
                       EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
                         EthLib.Cryptography.Bls.Signatures.DST with
      | .ok a, .ok b => eqG2 (toSG2 a) b | _, _ => false)
  report "hashToG2 (exact triples)" ok

def pairingTests (v : Vectors) : IO Unit := do
  let mut g : Rng := ⟨0x0DDBA11BADC0FFEE⟩
  let gen1 := EthLibImpl.Cryptography.Bls.G1.generator
  let gen2 := EthLibImpl.Cryptography.Bls.G2.generator
  let mut cases : Array (Array (IG1 × IG2)) := #[]
  -- bilinearity: e(aG, bH) · e(−abG, H) = 1, then a perturbed version
  let (a, g') := g.nat 1; g := g'
  let (b, g') := g.nat 1; g := g'
  let aG := gen1.mulNat a
  let bH := gen2.mulNat b
  let abG := gen1.mulNat (a * b)
  cases := cases.push #[(aG, bH), (abG.neg, gen2)]
  cases := cases.push #[(aG, bH), (abG, gen2)]
  -- an infinity pair is skipped; an empty product is one
  cases := cases.push #[(EthLibImpl.Cryptography.Bls.G1.zero, bH), (aG, gen2.mulNat a)]
  cases := cases.push #[]
  -- degenerate Miller loops: twist points of order dividing 13, off-curve points
  let (t, g') := randG2Curve g; g := g'
  let small := t.mulNat h2Over13
  let (r, g') := randG1Curve g; g := g'
  cases := cases.push #[(aG, small)]
  cases := cases.push #[(r, t)]
  let (junk, g') := g.fp2; g := g'
  cases := cases.push #[(aG, ⟨junk, junk, EthLibImpl.Cryptography.Bls.Fp2.one⟩)]
  cases := cases.push #[(⟨junk.c0, junk.c1, junk.c0⟩, bH.double)]
  let mut ok := true
  let mut i := 0
  for c in cases do
    let impl := EthLibImpl.Cryptography.Bls.pairingCheck c
    let spec := EthLib.Cryptography.Bls.pairingCheck (c.map fun (p, q) => (toSG1 p, toSG2 q))
    if impl != spec then IO.println s!"  pairing case {i}: impl {impl}, spec {spec}"
    ok := ok && impl == spec
    i := i + 1
  report s!"pairingCheck ({cases.size} cases incl. degenerate loops)" ok
  -- final exponentiation alone, on random inputs
  let mut okFe := true
  for _ in [0:2] do
    let (f, g') := g.fp12; g := g'
    okFe := okFe && (toS12 (EthLibImpl.Cryptography.Bls.finalExponentiation f)).beq
      (EthLib.Cryptography.Bls.finalExponentiation (toS12 f))
  report "finalExponentiation = f^((p^12-1)/r)" okFe
  let _ := v

def sigTests (v : Vectors) : IO Unit := do
  let mut ok := true
  let pk1 := v.pubkeys.extract 0 1
  let pk8 := v.pubkeys.extract 0 8
  let cases : Array (Array ByteArray × ByteArray × ByteArray) := #[
    (pk1, v.msg, v.sig 1), (pk8, v.msg, v.sig 8), (pk1, flipBit v.msg, v.sig 1),
    (pk8, v.msg, v.sig 1), (#[], v.msg, EthLibImpl.Cryptography.Bls.G2.infinityBytes),
    (#[], v.msg, v.sig 1), (pk1, v.msg, EthLibImpl.Cryptography.Bls.G2.infinityBytes),
    (#[flipBit pk1[0]!], v.msg, v.sig 1), (#[EthLibImpl.Cryptography.Bls.G1.infinityBytes], v.msg, v.sig 1),
    (pk1, v.msg, flipBit (v.sig 1)), (pk1, v.msg, (v.sig 1).extract 0 95),
    (pk1.push pk1[0]!, v.msg, v.sig 1)]
  let expected := #[true, true, false, false, true, false, false, false, false, false, false, false]
  let mut i := 0
  for (pks, msg, sig) in cases do
    let impl := EthLibImpl.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig
    let spec := EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig
    if impl != spec || impl != expected[i]! then
      IO.println s!"  verify case {i}: impl {impl}, spec {spec}, expected {expected[i]!}"
    ok := ok && impl == spec && impl == expected[i]!
    i := i + 1
  report s!"ethFastAggregateVerify ({cases.size} cases)" ok
  let mut okAgg := true
  for pks in [pk1, pk8, #[], #[pk1[0]!.extract 0 47], #[pk1[0]!, flipBit pk1[0]!],
              #[EthLibImpl.Cryptography.Bls.G1.infinityBytes]] do
    let a := EthLibImpl.Cryptography.Bls.Signatures.ethAggregatePubkeys pks
    let b := EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks
    okAgg := okAgg && (match a, b with
      | .ok x, .ok y => x == y | .error e, .error e' => e.message == e'.message | _, _ => false)
  report "ethAggregatePubkeys (bytes and errors)" okAgg

/-! ## Benchmarks -/

/-- Median ns per op over 5 samples; each sample repeats `f` until `minNs`
has passed. `f` performs `perCall` ops. -/
def timeOp (name : String) (minNs : Nat) (perCall : Nat) (f : Nat → IO Unit) : IO Unit := do
  f 0
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

open EthLibImpl.Cryptography.Bls in
def bench (v : Vectors) (ops : List String) : IO Unit := do
  let all := ops.isEmpty
  let want (o : String) := all || ops.contains o
  let (x0, g) := (⟨0xABCDEF0123456789⟩ : Rng).fp
  let (y0, _) := g.fp
  let xr ← IO.mkRef x0
  let yr ← IO.mkRef y0
  let sink ← IO.mkRef (0 : UInt64)
  let n := 10000
  if want "fp_mul" then
    timeOp "fp_mul" 200000000 n fun _ => do
      let mut x ← xr.get; let y ← yr.get
      for _ in [:n] do x := x * y
      sink.modify (· + x.l0)
  if want "fp_sqr" then
    timeOp "fp_sqr" 200000000 n fun _ => do
      let mut x ← xr.get
      for _ in [:n] do x := x.sqr
      sink.modify (· + x.l0)
  if want "fp_add" then
    timeOp "fp_add" 200000000 n fun _ => do
      let mut x ← xr.get; let y ← yr.get
      for _ in [:n] do x := x + y
      sink.modify (· + x.l0)
  if want "fp_sub" then
    timeOp "fp_sub" 200000000 n fun _ => do
      let mut x ← xr.get; let y ← yr.get
      for _ in [:n] do x := x - y
      sink.modify (· + x.l0)
  if want "fp_inverse" then
    timeOp "fp_inverse" 200000000 1 fun _ => do
      let x ← xr.get; sink.modify (· + x.inverse.l0)
  if want "fp_sqrt" then
    timeOp "fp_sqrt" 200000000 1 fun _ => do
      let x ← xr.get
      match x.sqrt with | .ok r => sink.modify (· + r.l0) | .error _ => sink.modify (· + 1)
  let f2r ← IO.mkRef (Fp2.mk x0 y0)
  if want "fp2_mul" then
    timeOp "fp2_mul" 200000000 n fun _ => do
      let mut x ← f2r.get; let y ← f2r.get
      for _ in [:n] do x := x * y
      sink.modify (· + x.a0)
  if want "fp2_sqr" then
    timeOp "fp2_sqr" 200000000 n fun _ => do
      let mut x ← f2r.get
      for _ in [:n] do x := x.sqr
      sink.modify (· + x.a0)
  let (f12, _) := (⟨77⟩ : Rng).fp12
  let f12r ← IO.mkRef f12
  if want "fp12_mul" then
    timeOp "fp12_mul" 200000000 1000 fun _ => do
      let mut x ← f12r.get; let y ← f12r.get
      for _ in [:1000] do x := x * y
      sink.modify (· + x.c0.c0.a0)
  if want "fp12_sqr" then
    timeOp "fp12_sqr" 200000000 1000 fun _ => do
      let mut x ← f12r.get
      for _ in [:1000] do x := x.sqr
      sink.modify (· + x.c0.c0.a0)
  if want "fp12_cyc_sqr" then
    let h := f12.conj * f12.inverse
    let cyc := h.frobenius2 * h
    let cr ← IO.mkRef cyc
    timeOp "fp12_cyc_sqr" 200000000 1000 fun _ => do
      let mut x ← cr.get
      for _ in [:1000] do x := x.cycSqr
      sink.modify (· + x.c0.c0.a0)
  let pk1r ← IO.mkRef v.pubkeys[0]!
  let sig1r ← IO.mkRef (v.sig 1)
  if want "g1_uncompress" then
    timeOp "g1_uncompress" 200000000 1 fun _ => do
      match G1.uncompress (← pk1r.get) with | .ok p => sink.modify (· + p.x.l0) | _ => pure ()
  if want "g1_key_validate" then
    timeOp "g1_key_validate" 200000000 1 fun _ => do
      if (G1.keyValidate (← pk1r.get)).isOk then sink.modify (· + 1)
  if want "g1_in_subgroup" then
    match G1.uncompress v.pubkeys[0]! with
    | .ok p =>
      let pr ← IO.mkRef p
      timeOp "g1_in_subgroup" 200000000 1 fun _ => do
        if G1.inSubgroup (← pr.get) then sink.modify (· + 1)
    | _ => pure ()
  if want "g2_uncompress" then
    timeOp "g2_uncompress" 200000000 1 fun _ => do
      match G2.uncompress (← sig1r.get) with | .ok p => sink.modify (· + p.x.a0) | _ => pure ()
  if want "g2_sig_validate" then
    timeOp "g2_sig_validate" 200000000 1 fun _ => do
      match G2.uncompress (← sig1r.get) with
      | .ok p => if G2.inSubgroup p then sink.modify (· + 1)
      | _ => pure ()
  let msgr ← IO.mkRef v.msg
  if want "hash_to_g2" then
    timeOp "hash_to_g2" 200000000 1 fun _ => do
      match HashToCurve.hashToG2 (← msgr.get) Signatures.DST with
      | .ok p => sink.modify (· + p.x.a0) | _ => pure ()
  let pis := [PairInput.ofPoints G1.generator G2.generator]
  let pisr ← IO.mkRef pis
  if want "miller_loop" then
    timeOp "miller_loop" 200000000 1 fun _ => do
      sink.modify (· + (millerLoop (← pisr.get)).c0.c0.a0)
  if want "final_exp" then
    timeOp "final_exp" 200000000 1 fun _ => do
      sink.modify (· + (finalExponentiation (← f12r.get)).c0.c0.a0)
  if want "pairing_check_2" then
    let pairs := #[(G1.generator, G2.generator), (G1.generator.neg, G2.generator)]
    let pr ← IO.mkRef pairs
    timeOp "pairing_check_2" 200000000 1 fun _ => do
      if pairingCheck (← pr.get) then sink.modify (· + 1)
  for nn in [1, 8, 64, 512] do
    if want s!"fast_agg_verify:{nn}" then
      let pks ← IO.mkRef (v.pubkeys.extract 0 nn)
      let sig := v.sig nn
      timeOp s!"fast_agg_verify:{nn}" 200000000 1 fun _ => do
        if Signatures.ethFastAggregateVerify (← pks.get) (← msgr.get) sig then sink.modify (· + 1)
    if want s!"aggregate_pubkeys:{nn}" && nn == 512 then
      let pks ← IO.mkRef (v.pubkeys.extract 0 nn)
      timeOp s!"aggregate_pubkeys:{nn}" 200000000 1 fun _ => do
        if (Signatures.ethAggregatePubkeys (← pks.get)).isOk then sink.modify (· + 1)
  IO.println s!"(sink {← sink.get})"

end ImplBench

def main (args : List String) : IO Unit := do
  match args with
  | [path, "test"] =>
    let v ← ImplBench.loadVectors path
    ImplBench.fieldTests 20
    ImplBench.curveTests v 4
    ImplBench.hashTests 6
    ImplBench.sigTests v
    ImplBench.pairingTests v
  | path :: "bench" :: ops =>
    let v ← ImplBench.loadVectors path
    ImplBench.bench v ops
  | _ => IO.println "usage: implbench VECTORS (test | bench [OP...])"
