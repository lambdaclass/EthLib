import EthLib.Cryptography.Bls
import EthLibImpl

/-!
# Differential fuzzing: `EthLibImpl` against the `EthLib` spec

```
implfuzz [--seed N] [--seconds S] [--vectors PATH] [--iter K] [TARGET...]
```

Each target runs for `S` seconds (default 10); with no target, all run.
Targets: `fp fp2 fp6 fp12 decode group hash pairing sig`.

Every iteration draws its own PRNG state from `(seed, target, iteration)`,
so a mismatch reported at `seed=S iter=K` replays alone with
`implfuzz --seed S --iter K TARGET`.

Equality is exact: `Except` results compare on value and error message, points
on their projective triples. The only exception is `Fp2.sqrt`, where the two
sides need the same success and the implementation's root must square back.
-/

namespace ImplFuzz

abbrev S := EthLib.Cryptography.Bls.Fp
abbrev S2 := EthLib.Cryptography.Bls.Fp2
abbrev S6 := EthLib.Cryptography.Bls.Fp6
abbrev S12 := EthLib.Cryptography.Bls.Fp12
abbrev I := EthLibImpl.Cryptography.Bls.Fp
abbrev I2 := EthLibImpl.Cryptography.Bls.Fp2
abbrev I6 := EthLibImpl.Cryptography.Bls.Fp6
abbrev I12 := EthLibImpl.Cryptography.Bls.Fp12
abbrev SG1 := EthLib.Cryptography.Bls.G1
abbrev SG2 := EthLib.Cryptography.Bls.G2
abbrev IG1 := EthLibImpl.Cryptography.Bls.G1
abbrev IG2 := EthLibImpl.Cryptography.Bls.G2
abbrev BlsError := EthLib.Cryptography.Bls.BlsError

/-! ## Conversions (as in `ImplBench`) -/

def toS (a : I) : S := EthLib.Cryptography.Bls.Fp.ofNat a.toNat
def toS2 (a : I2) : S2 := ⟨toS a.c0, toS a.c1⟩
def toS6 (a : I6) : S6 := ⟨toS2 a.c0, toS2 a.c1, toS2 a.c2⟩
def toS12 (a : I12) : S12 := ⟨toS6 a.c0, toS6 a.c1⟩
def toSG1 (p : IG1) : SG1 := ⟨toS p.x, toS p.y, toS p.z⟩
def toSG2 (p : IG2) : SG2 := ⟨toS2 p.x, toS2 p.y, toS2 p.z⟩

def P : Nat := EthLib.Cryptography.Bls.Fp.modulus
def R : Nat := EthLib.Cryptography.Bls.Fr.modulus

/-- `h₂ / 13`: maps a twist point to one of order dividing `13 · r`. -/
def h2Over13 : Nat :=
  0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5 / 13

/-! ## Rendering -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexNat (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def hexBytes (b : ByteArray) : String := Id.run do
  let mut s := ""
  for x in b.data do
    s := (s.push (hexDigit (x.toNat / 16))).push (hexDigit (x.toNat % 16))
  return s

def hI (a : I) : String := hexNat a.toNat
def hS (a : S) : String := hexNat a.val
def hI2 (a : I2) : String := s!"({hI a.c0}, {hI a.c1})"
def hS2 (a : S2) : String := s!"({hS a.c0}, {hS a.c1})"
def hI6 (a : I6) : String := s!"[{hI2 a.c0}, {hI2 a.c1}, {hI2 a.c2}]"
def hS6 (a : S6) : String := s!"[{hS2 a.c0}, {hS2 a.c1}, {hS2 a.c2}]"
def hI12 (a : I12) : String := s!"<{hI6 a.c0}, {hI6 a.c1}>"
def hS12 (a : S12) : String := s!"<{hS6 a.c0}, {hS6 a.c1}>"
def hIG1 (p : IG1) : String := s!"({hI p.x}, {hI p.y}, {hI p.z})"
def hSG1 (p : SG1) : String := s!"({hS p.x}, {hS p.y}, {hS p.z})"
def hIG2 (p : IG2) : String := s!"({hI2 p.x}, {hI2 p.y}, {hI2 p.z})"
def hSG2 (p : SG2) : String := s!"({hS2 p.x}, {hS2 p.y}, {hS2 p.z})"

def exStr {α : Type} (f : α → String) : Except BlsError α → String
  | .ok a => s!"ok {f a}"
  | .error e => s!"err {e.message}"

def hList {α : Type} (f : α → String) (xs : Array α) : String :=
  "[" ++ ", ".intercalate (xs.toList.map f) ++ "]"

/-! ## PRNG: xorshift64* -/

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

/-- Uniform-ish in `[0, n)`, for `n > 0`. -/
def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (w, g) := g.next
  (w.toNat % n, g)

def Rng.bool (g : Rng) : Bool × Rng :=
  let (w, g) := g.next
  ((w >>> 40) &&& 1 == 1, g)

def Rng.bytes (g : Rng) (n : Nat) : ByteArray × Rng := Id.run do
  let mut g := g
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (w, g') := g.next
    g := g'
    out := out.push (w >>> 33).toUInt8
  return (out, g)

def Rng.pick {α : Type} [Inhabited α] (g : Rng) (xs : Array α) : α × Rng :=
  let (i, g) := g.below xs.size
  (xs[i]!, g)

def mix (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def nameHash (s : String) : UInt64 :=
  s.foldl (fun h c => h * 1099511628211 + c.toNat.toUInt64) 14695981039346656037

/-- Big-endian bytes of `n mod 2^(8·len)`. -/
def natBE (n : Nat) (len : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:len] do
    out := out.push (UInt8.ofNat ((n >>> ((len - 1 - i) * 8)) &&& 0xff))
  return out

/-! ## Field element generators, weighted toward edge values -/

/-- A natural number, biased toward the values that stress limb arithmetic. May exceed `p`. -/
def Rng.edgeNat (g : Rng) : Nat × Rng :=
  let (k, g) := g.below 15
  match k with
  | 0 => (0, g)
  | 1 => (1, g)
  | 2 => (2, g)
  | 3 => (P - 1, g)
  | 4 => (P - 2, g)
  | 5 => ((P - 1) / 2, g)
  | 6 => ((P + 1) / 2, g)
  | 7 => -- small values
    let (b, g) := g.below 40
    let (n, g) := g.nat 1
    (n % (2 ^ (b + 1)), g)
  | 8 => -- just below p
    let (d, g) := g.below 300
    (P - 1 - d, g)
  | 9 => -- 2^k - 1, below p for k ≤ 380
    let (b, g) := g.below 380
    (2 ^ (b + 1) - 1, g)
  | 10 => -- p with its low j limbs replaced (may land above p)
    let (j, g) := g.below 6
    let (mode, g) := g.below 3
    let (r, g) := g.nat j
    let low := match mode with
      | 0 => 2 ^ (64 * j) - 1
      | 1 => 0
      | _ => r
    (((P >>> (64 * j)) <<< (64 * j)) ||| low, g)
  | 11 => -- limb boundaries 2^(64j) + {-1, 0, 1}
    let (j, g) := g.below 6
    let (s, g) := g.below 3
    (2 ^ (64 * (j + 1)) + s - 1, g)
  | 12 => -- high limbs all ones, random low limbs (above p once j is large)
    let (j, g) := g.below 5
    let (r, g) := g.nat (5 - j)
    ((((2 ^ (64 * (j + 1)) - 1)) <<< (64 * (5 - j))) ||| r, g)
  | 13 => g.nat 6
  | _ => g.nat 7

def Rng.fp (g : Rng) : I × Rng :=
  let (n, g) := g.edgeNat
  (EthLibImpl.Cryptography.Bls.Fp.ofNat n, g)

def Rng.fpRand (g : Rng) : I × Rng :=
  let (n, g) := g.nat 7
  (EthLibImpl.Cryptography.Bls.Fp.ofNat n, g)

/-- A component from `{0, 1, p-1}`. -/
def Rng.fpSparse (g : Rng) : I × Rng :=
  let (k, g) := g.below 3
  (EthLibImpl.Cryptography.Bls.Fp.ofNat (#[0, 1, P - 1][k]!), g)

/-- Element-level mode 0: all random; 1: all from `{0, 1, p-1}`; 2: mixed edge values. -/
def Rng.fpMode (g : Rng) (mode : Nat) : I × Rng :=
  match mode with
  | 0 => g.fpRand
  | 1 => g.fpSparse
  | _ => g.fp

def Rng.fp2M (g : Rng) (mode : Nat) : I2 × Rng :=
  let (a, g) := g.fpMode mode; let (b, g) := g.fpMode mode
  (EthLibImpl.Cryptography.Bls.Fp2.mk a b, g)
def Rng.fp6M (g : Rng) (mode : Nat) : I6 × Rng :=
  let (a, g) := g.fp2M mode; let (b, g) := g.fp2M mode; let (c, g) := g.fp2M mode
  (⟨a, b, c⟩, g)
def Rng.fp12M (g : Rng) (mode : Nat) : I12 × Rng :=
  let (a, g) := g.fp6M mode; let (b, g) := g.fp6M mode
  (⟨a, b⟩, g)

def Rng.mode (g : Rng) : Nat × Rng := g.below 3

/-- Scalars: 1, 2 and 4 random words, 0, 1, r, r±1, small, powers of two, 6 words. -/
def Rng.scalar (g : Rng) : Nat × Rng :=
  let (k, g) := g.below 12
  match k with
  | 0 => g.nat 1
  | 1 => g.nat 2
  | 2 => g.nat 4
  | 3 => (0, g)
  | 4 => (1, g)
  | 5 => (R, g)
  | 6 => (R - 1, g)
  | 7 => (R + 1, g)
  | 8 => g.below 16
  | 9 => let (b, g) := g.below 255; (2 ^ b, g)
  | 10 => g.nat 6
  | _ => let (n, g) := g.nat 4; (n % R, g)

/-! ## Reporting -/

def maxPrinted : Nat := 3

structure Ctx where
  name : String
  seed : UInt64
  iter : IO.Ref Nat
  mism : IO.Ref Nat
  /-- Comparisons whose result was a success (a root, a decoded point, a valid
  signature, ...), to show the run is not only exercising rejection paths. -/
  pos : IO.Ref Nat

def Ctx.note (c : Ctx) (b : Bool) : IO Unit := if b then c.pos.modify (· + 1) else pure ()

/-- Record one comparison; print the repro on the first few failures. -/
def Ctx.check (c : Ctx) (op : String) (ok : Bool)
    (inputs impl spec : Unit → String) : IO Unit := do
  if ok then return
  c.mism.modify (· + 1)
  if (← c.mism.get) ≤ maxPrinted then
    IO.println s!"MISMATCH target={c.name} op={op} seed={c.seed} iter={← c.iter.get}"
    IO.println s!"  input: {inputs ()}"
    IO.println s!"  impl:  {impl ()}"
    IO.println s!"  spec:  {spec ()}"
    (← IO.getStdout).flush

def Ctx.fp (c : Ctx) (op : String) (inp : Unit → String) (i : I) (s : S) : IO Unit :=
  c.check op (i.toNat == s.val) inp (fun _ => hI i) (fun _ => hS s)
def Ctx.fp2 (c : Ctx) (op : String) (inp : Unit → String) (i : I2) (s : S2) : IO Unit :=
  c.check op ((toS2 i).beq s) inp (fun _ => hI2 i) (fun _ => hS2 s)
def Ctx.fp6 (c : Ctx) (op : String) (inp : Unit → String) (i : I6) (s : S6) : IO Unit :=
  c.check op ((toS6 i).beq s) inp (fun _ => hI6 i) (fun _ => hS6 s)
def Ctx.fp12 (c : Ctx) (op : String) (inp : Unit → String) (i : I12) (s : S12) : IO Unit :=
  c.check op ((toS12 i).beq s) inp (fun _ => hI12 i) (fun _ => hS12 s)

def eqG1 (a b : SG1) : Bool := a.x.beq b.x && a.y.beq b.y && a.z.beq b.z
def eqG2 (a b : SG2) : Bool := a.x.beq b.x && a.y.beq b.y && a.z.beq b.z

def Ctx.g1 (c : Ctx) (op : String) (inp : Unit → String) (i : IG1) (s : SG1) : IO Unit :=
  c.check op (eqG1 (toSG1 i) s) inp (fun _ => hIG1 i) (fun _ => hSG1 s)
def Ctx.g2 (c : Ctx) (op : String) (inp : Unit → String) (i : IG2) (s : SG2) : IO Unit :=
  c.check op (eqG2 (toSG2 i) s) inp (fun _ => hIG2 i) (fun _ => hSG2 s)

/-- Compare two rendered results (used for `Except` values and bytes). -/
def Ctx.str (c : Ctx) (op : String) (inp : Unit → String) (i s : String) : IO Unit :=
  c.check op (i == s) inp (fun _ => i) (fun _ => s)

def Ctx.bool (c : Ctx) (op : String) (inp : Unit → String) (i s : Bool) : IO Unit :=
  c.check op (i == s) inp (fun _ => toString i) (fun _ => toString s)

/-! ## Vectors -/

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

/-! ## Curve points -/

/-- A curve point on `E` (not necessarily in `G1`). -/
partial def randG1Curve (g : Rng) : IG1 × Rng :=
  let (x, g) := g.fpRand
  let rhs := x.sqr * x + EthLibImpl.Cryptography.Bls.Fp.ofNat 4
  match rhs.sqrt with
  | .ok y => (⟨x, y, EthLibImpl.Cryptography.Bls.Fp.one⟩, g)
  | .error _ => randG1Curve g

/-- A curve point on `E'` (not necessarily in `G2`). -/
partial def randG2Curve (g : Rng) : IG2 × Rng :=
  let (x, g) := g.fp2M 0
  let rhs := x.sqr * x + EthLibImpl.Cryptography.Bls.G2.bTwist
  match rhs.sqrt with
  | .ok y => (⟨x, y, EthLibImpl.Cryptography.Bls.Fp2.one⟩, g)
  | .error _ => randG2Curve g

/-- Junk: random coordinates, almost surely off the curve. -/
def junkG1 (g : Rng) : IG1 × Rng :=
  let (x, g) := g.fp; let (y, g) := g.fp; let (z, g) := g.fp
  (⟨x, y, z⟩, g)
def junkG2 (g : Rng) : IG2 × Rng :=
  let (x, g) := g.fp2M 2; let (y, g) := g.fp2M 2; let (z, g) := g.fp2M 2
  (⟨x, y, z⟩, g)

/-- G1 inputs: subgroup points, random curve points (mostly outside the subgroup),
infinity (canonical and with garbage `x`, `y`), cofactor-subgroup points, order-3
points, and off-curve junk. -/
def Rng.g1Point (g : Rng) : IG1 × Rng :=
  let (k, g) := g.below 14
  if k < 5 then
    let (s, g) := g.scalar
    (EthLibImpl.Cryptography.Bls.G1.mulNat EthLibImpl.Cryptography.Bls.G1.generator s, g)
  else if k < 8 then randG1Curve g
  else if k == 8 then (EthLibImpl.Cryptography.Bls.G1.zero, g)
  else if k == 9 then
    let (x, g) := g.fp; let (y, g) := g.fp
    (⟨x, y, EthLibImpl.Cryptography.Bls.Fp.zero⟩, g)
  else if k == 10 then
    let (t, g) := randG1Curve g
    (EthLibImpl.Cryptography.Bls.G1.mulNat t R, g)
  else if k == 11 then
    let (b, g) := g.bool
    let two := EthLibImpl.Cryptography.Bls.Fp.ofNat 2
    (⟨EthLibImpl.Cryptography.Bls.Fp.zero, if b then two else -two,
      EthLibImpl.Cryptography.Bls.Fp.one⟩, g)
  else junkG1 g

def Rng.g2Point (g : Rng) : IG2 × Rng :=
  let (k, g) := g.below 15
  if k < 5 then
    let (s, g) := g.scalar
    (EthLibImpl.Cryptography.Bls.G2.mulNat EthLibImpl.Cryptography.Bls.G2.generator s, g)
  else if k < 8 then randG2Curve g
  else if k == 8 then (EthLibImpl.Cryptography.Bls.G2.zero, g)
  else if k == 9 then
    let (x, g) := g.fp2M 2; let (y, g) := g.fp2M 2
    (⟨x, y, EthLibImpl.Cryptography.Bls.Fp2.zero⟩, g)
  else if k == 10 then
    let (t, g) := randG2Curve g
    (EthLibImpl.Cryptography.Bls.G2.mulNat t h2Over13, g)
  else if k == 11 then
    let (t, g) := randG2Curve g
    (EthLibImpl.Cryptography.Bls.G2.mulNat t (R * h2Over13), g)
  else if k == 12 then
    let (t, g) := randG2Curve g
    (EthLibImpl.Cryptography.Bls.G2.mulNat t R, g)
  else junkG2 g

/-- Same point with a different Jacobian scaling `(λ²x, λ³y, λz)`. -/
def rescaleG1 (p : IG1) (l : I) : IG1 := ⟨p.x * l.sqr, p.y * (l.sqr * l), p.z * l⟩
def rescaleG2 (p : IG2) (l : I2) : IG2 := ⟨p.x * l.sqr, p.y * (l.sqr * l), p.z * l⟩

/-- The second operand of a binary operation, related to the first. -/
def Rng.g1Partner (g : Rng) (p : IG1) : IG1 × Rng :=
  let (k, g) := g.below 9
  match k with
  | 0 => (p.neg, g)
  | 1 => (p, g)
  | 2 => let (l, g) := g.fpRand; (rescaleG1 p l, g)
  | 3 => let (l, g) := g.fpRand; (rescaleG1 p.neg l, g)
  | 4 => (EthLibImpl.Cryptography.Bls.G1.zero, g)
  | 5 => (p.double, g)
  | _ => g.g1Point

def Rng.g2Partner (g : Rng) (p : IG2) : IG2 × Rng :=
  let (k, g) := g.below 9
  match k with
  | 0 => (p.neg, g)
  | 1 => (p, g)
  | 2 => let (l, g) := g.fp2M 0; (rescaleG2 p l, g)
  | 3 => let (l, g) := g.fp2M 0; (rescaleG2 p.neg l, g)
  | 4 => (EthLibImpl.Cryptography.Bls.G2.zero, g)
  | 5 => (p.double, g)
  | _ => g.g2Point

/-! ## Targets -/

section Targets
open EthLibImpl.Cryptography.Bls (Fp)

def fpTarget (c : Ctx) (g : Rng) : IO Unit := do
  let (a, g) := g.edgeNat
  let (b, g) := g.edgeNat
  let ia := EthLibImpl.Cryptography.Bls.Fp.ofNat a; let ib := EthLibImpl.Cryptography.Bls.Fp.ofNat b
  let sa := EthLib.Cryptography.Bls.Fp.ofNat a; let sb := EthLib.Cryptography.Bls.Fp.ofNat b
  let ra := a % P; let rb := b % P
  let inp := fun _ => s!"a={hexNat a} b={hexNat b}"
  c.check "Fp.ofNat/toNat" (ia.toNat == ra && sa.val == ra) inp (fun _ => hI ia) (fun _ => hexNat ra)
  c.fp "add" inp (ia + ib) (sa + sb)
  c.fp "sub" inp (ia - ib) (sa - sb)
  c.fp "mul" inp (ia * ib) (sa * sb)
  c.fp "sqr" inp ia.sqr (sa * sa)
  c.fp "double" inp ia.double (sa + sa)
  c.fp "neg" inp (-ia) (-sa)
  -- fast independent oracle on plain naturals
  c.check "mul-oracle" ((ia * ib).toNat == ra * rb % P) inp
    (fun _ => hI (ia * ib)) (fun _ => hexNat (ra * rb % P))
  c.check "add-oracle" ((ia + ib).toNat == (ra + rb) % P) inp
    (fun _ => hI (ia + ib)) (fun _ => hexNat ((ra + rb) % P))
  c.check "sub-oracle" ((ia - ib).toNat == (ra + P - rb) % P) inp
    (fun _ => hI (ia - ib)) (fun _ => hexNat ((ra + P - rb) % P))
  c.check "neg-oracle" ((-ia).toNat == (P - ra) % P) inp
    (fun _ => hI (-ia)) (fun _ => hexNat ((P - ra) % P))
  c.check "sqr-oracle" (ia.sqr.toNat == ra * ra % P) inp
    (fun _ => hI ia.sqr) (fun _ => hexNat (ra * ra % P))
  c.fp "inverse" inp ia.inverse sa.inverse
  c.check "inverse-oracle" (ra == 0 || (ia.inverse * ia).toNat == 1) inp
    (fun _ => hI (ia.inverse * ia)) (fun _ => "0x1")
  c.str "sqrt" inp (exStr hI ia.sqrt) (exStr hS sa.sqrt)
  c.note ia.sqrt.isOk
  c.bool "signBit" inp ia.signBit (EthLib.Cryptography.Bls.Fp.signBit sa)
  c.str "toBytesBE" inp (hexBytes ia.toBytesBE) (hexBytes sa.toBytesBE)
  -- fromBytesBE: canonical round trip, then adversarial byte strings
  let (k, g) := g.below 9
  let (bs, g) : ByteArray × Rng :=
    match k with
    | 0 => (sa.toBytesBE, g)
    | 1 => let (r, g) := g.bytes 48; (r, g)
    | 2 => (natBE a 48, g)
    | 3 => let (d, g) := g.below 5; (natBE (P + d - 2) 48, g)
    | 4 => (natBE (2 ^ 381 - 1) 48, g)
    | 5 => (ByteArray.mk (Array.replicate 48 0xff), g)
    | 6 => let (r, g) := g.bytes 48; (r.set! 0 (r.get! 0 &&& 0x1f), g)
    | 7 => let (l, g) := g.below 4
           let (r, g) := g.bytes (#[0, 47, 49, 96][l]!)
           (r, g)
    | _ => let (r, g) := g.bytes 48; (r.set! 0 (r.get! 0 &&& 0x0f), g)
  let inpB := fun _ => s!"bytes={hexBytes bs}"
  c.str "fromBytesBE" inpB
    (exStr hI (EthLibImpl.Cryptography.Bls.Fp.fromBytesBE bs))
    (exStr hS (EthLib.Cryptography.Bls.Fp.fromBytesBE bs))

def fp2Target (c : Ctx) (g : Rng) : IO Unit := do
  let (m, g) := g.mode
  let (x, g) := g.fp2M m; let (y, g) := g.fp2M m
  let sx := toS2 x; let sy := toS2 y
  let inp := fun _ => s!"x={hI2 x} y={hI2 y}"
  c.fp2 "add" inp (x + y) (sx + sy)
  c.fp2 "sub" inp (x - y) (sx - sy)
  c.fp2 "mul" inp (x * y) (sx * sy)
  c.fp2 "sqr" inp x.sqr (sx * sx)
  c.fp2 "neg" inp (-x) (-sx)
  c.fp2 "double" inp x.double (sx + sx)
  c.fp2 "conj" inp x.conj (EthLib.Cryptography.Bls.Fp2.conjugate sx)
  c.fp2 "mulByXi" inp x.mulByXi sx.mulByOnePlusI
  c.fp2 "mulFp" inp (x.mulFp y.c0) (sx * EthLib.Cryptography.Bls.Fp2.ofFp (toS y.c0))
  c.fp2 "inverse" inp x.inverse sx.inverse
  c.bool "signBit" inp x.signBit (EthLib.Cryptography.Bls.Fp2.signBit sx)
  c.check "isZero" (x.isZero == sx.isZero) inp (fun _ => toString x.isZero) (fun _ => toString sx.isZero)
  -- sqrt: same success, and the impl's root squares back (exact root is unspecified)
  for z in #[x, x.sqr, EthLibImpl.Cryptography.Bls.Fp2.mk x.c0 Fp.zero,
             EthLibImpl.Cryptography.Bls.Fp2.mk Fp.zero x.c1, -(x.sqr)] do
    let sz := toS2 z
    let inpz := fun _ => s!"z={hI2 z}"
    let ri := z.sqrt
    let rs := EthLib.Cryptography.Bls.Fp2.sqrt sz
    let ok := match ri, rs with
      | .ok r, .ok _ => (toS2 r.sqr).beq sz
      | .error e, .error e' => e.message == e'.message
      | _, _ => false
    c.note ri.isOk
    c.check "sqrt" ok inpz
      (fun _ => exStr hI2 ri) (fun _ => exStr hS2 rs ++ " (any root r with r^2 = z accepted)")

def fp6Target (c : Ctx) (g : Rng) : IO Unit := do
  let (m, g) := g.mode
  let (u, g) := g.fp6M m; let (v, g) := g.fp6M m
  let su := toS6 u; let sv := toS6 v
  let inp := fun _ => s!"u={hI6 u} v={hI6 v}"
  let z2 := EthLib.Cryptography.Bls.Fp2.zero
  c.fp6 "add" inp (u + v) (su + sv)
  c.fp6 "sub" inp (u - v) (su - sv)
  c.fp6 "neg" inp (-u) (-su)
  c.fp6 "double" inp u.double (su + su)
  c.fp6 "mul" inp (u * v) (su * sv)
  c.fp6 "sqr" inp u.sqr (su * su)
  c.fp6 "inverse" inp u.inverse su.inverse
  c.fp6 "mulBy01" inp (u.mulBy01 v.c0 v.c1) (su * ⟨sv.c0, sv.c1, z2⟩)
  c.fp6 "mulBy1" inp (u.mulBy1 v.c1) (su * ⟨z2, sv.c1, z2⟩)
  c.fp6 "mulByV" inp u.mulByV su.mulByV
  c.fp6 "mulFp2" inp (u.mulFp2 v.c0) (su * EthLib.Cryptography.Bls.Fp6.ofFp2 sv.c0)

def fp12Target (c : Ctx) (g : Rng) (iter : Nat) : IO Unit := do
  let (m, g) := g.mode
  let (a, g) := g.fp12M m; let (b, g) := g.fp12M m
  let sa := toS12 a; let sb := toS12 b
  let inp := fun _ => s!"a={hI12 a} b={hI12 b}"
  let z2 := EthLib.Cryptography.Bls.Fp2.zero
  c.fp12 "add" inp (a + b) (sa + sb)
  c.fp12 "sub" inp (a - b) (sa - sb)
  c.fp12 "neg" inp (-a) (-sa)
  c.fp12 "mul" inp (a * b) (sa * sb)
  c.fp12 "sqr" inp a.sqr (sa * sa)
  c.fp12 "inverse" inp a.inverse sa.inverse
  c.fp12 "conj" inp a.conj sa.conjugate
  c.bool "isOne" inp a.isOne sa.isOne
  let line : S12 := ⟨⟨sb.c0.c0, sb.c0.c1, z2⟩, ⟨z2, sb.c1.c1, z2⟩⟩
  c.fp12 "mulBy014" inp (a.mulBy014 b.c0.c0 b.c0.c1 b.c1.c1) (sa * line)
  c.fp12 "frobenius2" inp a.frobenius2 (toS12 a.frobenius1.frobenius1)
  -- frobenius against the p-th power (slow spec side, so only some iterations)
  if iter % 4 == 0 then
    c.fp12 "frobenius1" inp a.frobenius1
      (EthLib.Cryptography.Bls.Fp12.powNat sa EthLib.Cryptography.Bls.Fp.modulus)
  -- cycSqr on a cyclotomic element (conj a / a)^(p^2+1); a = 0 is not one
  if !(sa.beq EthLib.Cryptography.Bls.Fp12.zero) then
    let h := a.conj * a.inverse
    let cyc := h.frobenius2 * h
    let sc := toS12 cyc
    let inpc := fun _ => s!"cyc={hI12 cyc}"
    c.fp12 "cycSqr" inpc cyc.cycSqr (sc * sc)

/-! ### decode -/

/-- Flags in the top three bits of byte 0. -/
def withFlags (b : ByteArray) (flags : Nat) : ByteArray :=
  if b.size == 0 then b else b.set! 0 ((b.get! 0 &&& (0x1f : UInt8)) ||| UInt8.ofNat (flags <<< 5))

def resize (g : Rng) (b : ByteArray) (len : Nat) : ByteArray × Rng :=
  if len ≤ b.size then (b.extract 0 len, g)
  else
    let (r, g) := g.bytes (len - b.size)
    (b ++ r, g)

def mutateEnc (g : Rng) (b : ByteArray) : ByteArray × Rng :=
  let n := b.size
  let (k, g) := g.below 14
  match k with
  | 0 | 1 => -- one to three bit flips, half of them in the flag byte
    let (cnt, g) := g.below 3
    Id.run do
      let mut g := g
      let mut out := b
      for _ in [0:cnt + 1] do
        let (inFlag, g1) := g.below 3
        let (pos, g2) := g1.below (max n 1)
        let (bit, g3) := g2.below 8
        g := g3
        let pos := if inFlag == 0 then 0 else pos
        if n > 0 then out := out.set! pos (out.get! pos ^^^ (1 <<< bit.toUInt8))
      return (out, g)
  | 2 => let (f, g) := g.below 8; (withFlags b f, g)
  | 3 => -- infinity-style: flag combination over an all-zero body
    let (f, g) := g.below 8
    (withFlags (ByteArray.mk (Array.replicate n 0)) f, g)
  | 4 => -- infinity with garbage in the body
    let (f, g) := g.below 8
    let (cnt, g) := g.below 3
    Id.run do
      let mut g := g
      let mut out := withFlags (ByteArray.mk (Array.replicate n 0)) (if f % 2 == 0 then 6 else f)
      for _ in [0:cnt + 1] do
        let (pos, g1) := g.below (max n 1)
        let (v, g2) := g1.below 255
        g := g2
        if n > 1 then out := out.set! (1 + pos % (n - 1)) (UInt8.ofNat (v + 1))
      return (out, g)
  | 5 | 6 => -- x set to a value ≥ p, in either half for G2, flags kept or randomized
    let (v, g) := g.below 5
    let (d, g) := g.below 200
    let big := #[P, P + d, 2 ^ 381 - 1, P + 1, 2 ^ 381 - 1 - d][v]!
    let (half, g) := g.below (max (n / 48) 1)
    let (f, g) := g.below 8
    let keep := if n > 0 then (b.get! 0).toNat >>> 5 else 0
    let flags := if f < 5 then keep else f
    if n < 48 then (b, g)
    else
      let out := b.extract 0 (48 * half) ++ natBE big 48 ++ b.extract (48 * half + 48) n
      (if half == 0 then withFlags out flags else out, g)
  | 7 => -- swap the two Fp halves
    if n == 96 then
      (withFlags (b.extract 48 96 ++ b.extract 0 48) ((b.get! 0).toNat >>> 5), g)
    else (b, g)
  | 8 => -- wrong lengths
    let (l, g) := g.below 5
    resize g b (#[0, 47, 49, 95, 97][l]!)
  | 9 => -- random body, compressed flag set
    let (r, g) := g.bytes n
    (if n > 0 then r.set! 0 (r.get! 0 ||| 0x80) else r, g)
  | 10 => -- x from an edge value, compressed
    let (e, g) := g.edgeNat
    let (f, g) := g.below 4
    let (half, g) := g.below (max (n / 48) 1)
    let x := natBE e 48
    let out := if n < 48 then b else b.extract 0 (48 * half) ++ x ++ b.extract (48 * half + 48) n
    (withFlags out (4 + f % 2), g)
  | 11 => -- zero the tail
    let (cut, g) := g.below (max n 1)
    (b.extract 0 cut ++ ByteArray.mk (Array.replicate (n - cut) 0), g)
  | 12 => -- trailing or leading byte changed
    let (v, g) := g.below 256
    (if n > 0 then b.set! (n - 1) (UInt8.ofNat v) else b, g)
  | _ => (b, g)

def mutateSome (g : Rng) (b : ByteArray) : ByteArray × Rng :=
  let (k, g) := g.below 4
  if k == 0 then (b, g)
  else
    let (b, g) := mutateEnc g b
    if k == 3 then mutateEnc g b else (b, g)

def g1Source (c : Vectors) (g : Rng) : ByteArray × Rng :=
  let (k, g) := g.below 8
  match k with
  | 0 | 1 => if c.pubkeys.isEmpty then g.bytes 48 else g.pick c.pubkeys
  | 2 | 3 => let (p, g) := g.g1Point; (EthLibImpl.Cryptography.Bls.G1.compress p, g)
  | 4 => let (p, g) := randG1Curve g; (EthLibImpl.Cryptography.Bls.G1.compress p, g)
  | 5 => (EthLibImpl.Cryptography.Bls.G1.infinityBytes, g)
  | 6 => g.bytes 48
  | _ => let (r, g) := g.bytes 48; (withFlags r 4, g)

def g2Source (c : Vectors) (g : Rng) : ByteArray × Rng :=
  let (k, g) := g.below 8
  match k with
  | 0 | 1 => if c.aggs.isEmpty then g.bytes 96 else
      let (a, g) := g.pick c.aggs; (a.2, g)
  | 2 | 3 => let (p, g) := g.g2Point; (EthLibImpl.Cryptography.Bls.G2.compress p, g)
  | 4 => let (p, g) := randG2Curve g; (EthLibImpl.Cryptography.Bls.G2.compress p, g)
  | 5 => (EthLibImpl.Cryptography.Bls.G2.infinityBytes, g)
  | 6 => g.bytes 96
  | _ => let (r, g) := g.bytes 96; (withFlags r 4, g)

def decodeTarget (c : Ctx) (v : Vectors) (g : Rng) : IO Unit := do
  let (b1, g) := g1Source v g
  let (b1, g) := mutateSome g b1
  let inp1 := fun _ => s!"bytes={hexBytes b1}"
  c.str "G1.uncompress" inp1
    (exStr hIG1 (EthLibImpl.Cryptography.Bls.G1.uncompress b1)) (exStr hSG1 (EthLib.Cryptography.Bls.G1.uncompress b1))
  c.note (EthLibImpl.Cryptography.Bls.G1.uncompress b1).isOk
  c.note (EthLibImpl.Cryptography.Bls.G1.keyValidate b1).isOk
  c.str "G1.keyValidate" inp1
    (exStr (fun _ => "()") (EthLibImpl.Cryptography.Bls.G1.keyValidate b1)) (exStr (fun _ => "()") (EthLib.Cryptography.Bls.G1.keyValidate b1))
  let (b2, g) := g2Source v g
  let (b2, _) := mutateSome g b2
  let inp2 := fun _ => s!"bytes={hexBytes b2}"
  c.note (EthLibImpl.Cryptography.Bls.G2.uncompress b2).isOk
  c.str "G2.uncompress" inp2
    (exStr hIG2 (EthLibImpl.Cryptography.Bls.G2.uncompress b2)) (exStr hSG2 (EthLib.Cryptography.Bls.G2.uncompress b2))
  -- a G1 string fed to G2 and vice versa (length checks)
  c.str "G2.uncompress(G1 bytes)" inp1
    (exStr hIG2 (EthLibImpl.Cryptography.Bls.G2.uncompress b1)) (exStr hSG2 (EthLib.Cryptography.Bls.G2.uncompress b1))
  c.str "G1.uncompress(G2 bytes)" inp2
    (exStr hIG1 (EthLibImpl.Cryptography.Bls.G1.uncompress b2)) (exStr hSG1 (EthLib.Cryptography.Bls.G1.uncompress b2))

/-! ### group -/

def groupTarget (c : Ctx) (g : Rng) : IO Unit := do
  let (useG2, g) := g.bool
  let (k, g) := g.scalar
  if !useG2 then
    let (p, g) := g.g1Point
    let (q, _) := g.g1Partner p
    let sp := toSG1 p; let sq := toSG1 q
    let inp := fun _ => s!"p={hIG1 p} q={hIG1 q} k={hexNat k}"
    c.g1 "G1.add" inp (p.add q) (sp.add sq)
    c.g1 "G1.add(swapped)" inp (q.add p) (sq.add sp)
    c.g1 "G1.add(p,p)" inp (p.add p) (sp.add sp)
    c.g1 "G1.add(p,-p)" inp (p.add p.neg) (sp.add sp.neg)
    c.g1 "G1.double" inp p.double sp.double
    c.g1 "G1.neg" inp p.neg sp.neg
    c.g1 "G1.mulNat" inp (p.mulNat k) (sp.mulNat k)
    c.str "G1.compress" inp (hexBytes (EthLibImpl.Cryptography.Bls.G1.compress p)) (hexBytes (EthLib.Cryptography.Bls.G1.compress sp))
    c.str "G1.compress(q)" inp (hexBytes (EthLibImpl.Cryptography.Bls.G1.compress q)) (hexBytes (EthLib.Cryptography.Bls.G1.compress sq))
    c.bool "G1.inSubgroup" inp (EthLibImpl.Cryptography.Bls.G1.inSubgroup p) (EthLib.Cryptography.Bls.G1.inSubgroup sp)
    c.bool "G1.inSubgroup(q)" inp (EthLibImpl.Cryptography.Bls.G1.inSubgroup q) (EthLib.Cryptography.Bls.G1.inSubgroup sq)
  else
    let (p, g) := g.g2Point
    let (q, _) := g.g2Partner p
    let sp := toSG2 p; let sq := toSG2 q
    let inp := fun _ => s!"p={hIG2 p} q={hIG2 q} k={hexNat k}"
    c.g2 "G2.add" inp (p.add q) (sp.add sq)
    c.g2 "G2.add(swapped)" inp (q.add p) (sq.add sp)
    c.g2 "G2.add(p,p)" inp (p.add p) (sp.add sp)
    c.g2 "G2.add(p,-p)" inp (p.add p.neg) (sp.add sp.neg)
    c.g2 "G2.double" inp p.double sp.double
    c.g2 "G2.neg" inp p.neg sp.neg
    c.g2 "G2.mulNat" inp (p.mulNat k) (sp.mulNat k)
    c.str "G2.compress" inp (hexBytes (EthLibImpl.Cryptography.Bls.G2.compress p)) (hexBytes (EthLib.Cryptography.Bls.G2.compress sp))
    c.str "G2.compress(q)" inp (hexBytes (EthLibImpl.Cryptography.Bls.G2.compress q)) (hexBytes (EthLib.Cryptography.Bls.G2.compress sq))
    c.bool "G2.inSubgroup" inp (EthLibImpl.Cryptography.Bls.G2.inSubgroup p) (EthLib.Cryptography.Bls.G2.inSubgroup sp)
    c.bool "G2.inSubgroup(q)" inp (EthLibImpl.Cryptography.Bls.G2.inSubgroup q) (EthLib.Cryptography.Bls.G2.inSubgroup sq)

/-! ### hash -/

def hashTarget (c : Ctx) (g : Rng) : IO Unit := do
  let (ml, g) := g.below 301
  let (msg, g) := g.bytes ml
  let (mode, g) := g.below 4
  let (dst, _) ← do
    if mode == 0 then pure (EthLib.Cryptography.Bls.Signatures.DST, g)
    else
      let (dl, g) := g.below 301
      pure (g.bytes dl)
  let inp := fun _ => s!"msg={hexBytes msg} dst={hexBytes dst}"
  c.note (EthLibImpl.Cryptography.Bls.HashToCurve.hashToG2 msg dst).isOk
  c.str "hashToG2" inp
    (exStr hIG2 (EthLibImpl.Cryptography.Bls.HashToCurve.hashToG2 msg dst))
    (exStr hSG2 (EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst))

/-! ### pairing -/

def hPairsI (xs : Array (IG1 × IG2)) : String :=
  hList (fun (p, q) => s!"({hIG1 p}, {hIG2 q})") xs

def pairingTarget (c : Ctx) (g : Rng) (iter : Nat) : IO Unit := do
  if iter % 4 == 3 then
    let (m, g) := g.mode
    let (f, _) := g.fp12M m
    let inp := fun _ => s!"f={hI12 f}"
    let e := EthLib.Cryptography.Bls.finalExponentiation (toS12 f)
    c.fp12 "finalExpCube" inp (EthLibImpl.Cryptography.Bls.finalExpCube f) (e * e * e)
  else
    let (kind, g) := g.below 4
    let (pairs, g) : Array (IG1 × IG2) × Rng :=
      if kind == 0 then
        -- bilinear relation: e(aG, bH) e(-abG, H) = 1, possibly perturbed or padded
        let (a, g) := g.nat 1
        let (b, g) := g.nat 1
        let (pert, g) := g.below 4
        let aG := EthLibImpl.Cryptography.Bls.G1.mulNat EthLibImpl.Cryptography.Bls.G1.generator a
        let bH := EthLibImpl.Cryptography.Bls.G2.mulNat EthLibImpl.Cryptography.Bls.G2.generator b
        let abG := EthLibImpl.Cryptography.Bls.G1.mulNat EthLibImpl.Cryptography.Bls.G1.generator (a * b + (if pert == 1 then 1 else 0))
        let first := (aG, bH)
        let second := (abG.neg, EthLibImpl.Cryptography.Bls.G2.generator)
        let base := if pert == 2 then #[second, first] else #[first, second]
        let (pad, g) := g.bool
        (if pert == 3 && pad then base.push (EthLibImpl.Cryptography.Bls.G1.zero, bH) else base, g)
      else
        let (len, g) := g.below 4
        Id.run do
          let mut g := g
          let mut out : Array (IG1 × IG2) := #[]
          for _ in [0:len] do
            let (p, g2) := g.g1Point
            let (q, g3) := g2.g2Point
            g := g3
            out := out.push (p, q)
          return (out, g)
    let inp := fun _ => s!"pairs={hPairsI pairs}"
    let impl := EthLibImpl.Cryptography.Bls.pairingCheck pairs
    let spec := EthLib.Cryptography.Bls.pairingCheck
      (pairs.map fun (p, q) => (toSG1 p, toSG2 q))
    c.note impl
    c.bool "pairingCheck" inp impl spec

/-! ### sig -/

def hKeys (pks : Array ByteArray) : String := hList hexBytes pks

def sigTarget (c : Ctx) (v : Vectors) (g : Rng) : IO Unit := do
  let small := v.aggs.filter (·.1 ≤ 8)
  if small.isEmpty || v.pubkeys.isEmpty then
    c.check "vectors" false (fun _ => "no usable vectors") (fun _ => "") (fun _ => "")
    return
  let (a, g) := g.pick small
  let n := a.1
  let mut pks := v.pubkeys.extract 0 n
  let mut msg := v.msg
  let mut sig := a.2
  let (nm, g) := g.below 7
  let mut g := g
  -- zero mutations one time in seven, otherwise one to three
  for _ in [0:(nm + 1) / 2] do
    let (m, g1) := g.below 17
    g := g1
    match m with
    | 0 =>
      let (pos, g1) := g.below (max msg.size 1); let (bit, g2) := g1.below 8; g := g2
      if msg.size > 0 then msg := msg.set! pos (msg.get! pos ^^^ (1 <<< bit.toUInt8))
    | 1 =>
      let (l, g1) := g.below 65
      let (r, g2) := g1.bytes l; g := g2; msg := r
    | 2 =>
      let (i, g1) := g.below (max pks.size 1); g := g1
      if pks.size > 0 then pks := pks.eraseIdxIfInBounds i
    | 3 =>
      let (i, g1) := g.below (max pks.size 1); g := g1
      if pks.size > 0 then pks := pks.push pks[i]!
    | 4 =>
      let (kind, g1) := g.below 2
      if kind == 0 then
        let (e, g2) := g1.pick v.pubkeys; g := g2; pks := pks.push e
      else
        let (p, g2) := g1.g1Point; g := g2; pks := pks.push (EthLibImpl.Cryptography.Bls.G1.compress p)
    | 5 =>
      let (i, g1) := g.below (max pks.size 1)
      let (pos, g2) := g1.below 48; let (bit, g3) := g2.below 8; g := g3
      if pks.size > 0 then
        let pk := pks[i]!
        pks := pks.set! i (pk.set! pos (pk.get! pos ^^^ (1 <<< bit.toUInt8)))
    | 6 =>
      let (i, g1) := g.below (max pks.size 1); g := g1
      pks := if pks.size > 0 then pks.set! i EthLibImpl.Cryptography.Bls.G1.infinityBytes else pks.push EthLibImpl.Cryptography.Bls.G1.infinityBytes
    | 7 => pks := #[]
    | 8 =>
      let (r, g1) := g.bytes 48; g := g1
      pks := pks.push r
    | 9 =>
      let (i, g1) := g.below (max pks.size 1)
      let (l, g2) := g1.below 4; g := g2
      if pks.size > 0 then
        let (r, g3) := resize g pks[i]! (#[0, 47, 49, 96][l]!)
        g := g3; pks := pks.set! i r
    | 10 =>
      let (pos, g1) := g.below 96; let (bit, g2) := g1.below 8
      let (inFlag, g3) := g2.below 3; g := g3
      let pos := if inFlag == 0 then 0 else pos
      sig := sig.set! pos (sig.get! pos ^^^ (1 <<< bit.toUInt8))
    | 11 =>
      let (l, g1) := g.below 5
      let (r, g2) := resize g1 sig (#[0, 47, 95, 97, 90][l]!); g := g2; sig := r
    | 12 => sig := EthLibImpl.Cryptography.Bls.G2.infinityBytes
    | 13 => let (r, g1) := g.bytes 96; g := g1; sig := r
    | 14 => let (o, g1) := g.pick small; g := g1; sig := o.2
    | 15 => pks := pks.reverse
    | _ =>
      let (kind, g1) := g.below 2; g := g1
      let (p, g2) := g.g2Point; g := g2
      sig := if kind == 0 then EthLibImpl.Cryptography.Bls.G2.compress p else v.aggs[0]!.2
  let inp := fun _ => s!"pks={hKeys pks} msg={hexBytes msg} sig={hexBytes sig}"
  c.note (EthLibImpl.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig)
  c.bool "ethFastAggregateVerify" inp
    (EthLibImpl.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig)
    (EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig)
  let inpA := fun _ => s!"pks={hKeys pks}"
  c.str "ethAggregatePubkeys" inpA
    (exStr hexBytes (EthLibImpl.Cryptography.Bls.Signatures.ethAggregatePubkeys pks))
    (exStr hexBytes (EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks))

end Targets

/-! ## Driver -/

def allTargets : List String := ["fp", "fp2", "fp6", "fp12", "decode", "group", "hash", "pairing", "sig"]

def iterState (seed : UInt64) (name : String) (i : Nat) : Rng :=
  let s := mix (seed ^^^ (nameHash name * 0x9E3779B97F4A7C15) ^^^ mix i.toUInt64)
  ⟨if s == 0 then 1 else s⟩

def runTarget (name : String) (seed : UInt64) (seconds : Nat) (only : Option Nat)
    (v : Vectors) : IO Nat := do
  let c : Ctx := { name, seed, iter := ← IO.mkRef 0, mism := ← IO.mkRef 0, pos := ← IO.mkRef 0 }
  let start ← IO.monoMsNow
  let mut i := only.getD 0
  let mut done := 0
  repeat
    c.iter.set i
    let g := iterState seed name i
    match name with
    | "fp" => fpTarget c g
    | "fp2" => fp2Target c g
    | "fp6" => fp6Target c g
    | "fp12" => fp12Target c g i
    | "decode" => decodeTarget c v g
    | "group" => groupTarget c g
    | "hash" => hashTarget c g
    | "pairing" => pairingTarget c g i
    | "sig" => sigTarget c v g
    | _ => pure ()
    i := i + 1
    done := done + 1
    if only.isSome then break
    if (← IO.monoMsNow) - start ≥ seconds * 1000 then break
  let m ← c.mism.get
  IO.println s!"{name}: iterations={done} mismatches={m} (successful results: {← c.pos.get})"
  (← IO.getStdout).flush
  return m

structure Opts where
  seed : UInt64 := 1
  seconds : Nat := 10
  vectors : String := "../vectors.txt"
  iter : Option Nat := none
  targets : List String := []

partial def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--seed" :: n :: rest =>
    match n.toNat? with
    | some k => parseArgs { o with seed := k.toUInt64 } rest
    | none => .error s!"bad --seed {n}"
  | "--seconds" :: n :: rest =>
    match n.toNat? with
    | some k => parseArgs { o with seconds := k } rest
    | none => .error s!"bad --seconds {n}"
  | "--vectors" :: p :: rest => parseArgs { o with vectors := p } rest
  | "--iter" :: n :: rest =>
    match n.toNat? with
    | some k => parseArgs { o with iter := some k } rest
    | none => .error s!"bad --iter {n}"
  | t :: rest =>
    if allTargets.contains t then parseArgs { o with targets := o.targets ++ [t] } rest
    else .error s!"unknown argument or target {t}"

end ImplFuzz

def main (args : List String) : IO UInt32 := do
  match ImplFuzz.parseArgs {} args with
  | .error e =>
    IO.eprintln s!"{e}"
    IO.eprintln s!"usage: implfuzz [--seed N] [--seconds S] [--vectors PATH] [--iter K] [{" ".intercalate ImplFuzz.allTargets}]..."
    return 2
  | .ok o =>
    let v ← try ImplFuzz.loadVectors o.vectors catch e =>
      IO.eprintln s!"warning: cannot load vectors from {o.vectors}: {e}"
      pure ⟨.empty, #[], #[]⟩
    let targets := if o.targets.isEmpty then ImplFuzz.allTargets else o.targets
    let mut total := 0
    for t in targets do
      total := total + (← ImplFuzz.runTarget t o.seed o.seconds o.iter v)
    return if total == 0 then 0 else 1
