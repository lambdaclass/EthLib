import EthLib.Cryptography.Bls.Pairing

/-!
# Mirror: the implementation's pairing over spec types

`EthLibImpl.Cryptography.Bls.Pairing` and the new `Fp12` operations it
uses (Frobenius maps, cyclotomic squaring), restated over the spec's
`Fp`/`Fp2`/`Fp6`/`Fp12`, formula for formula.

These definitions split each equivalence proof in two:

* implementation → mirror is structural: the same formulas, with each
  implementation field operation replaced by the spec operation it
  computes (`x.double ↦ x + x`, `x.sqr ↦ x * x`, `x.mulFp s ↦ mulFp x s`,
  `Fp2.mulByXi ↦ Fp2.mulByOnePlusI`, `Fp2.conj ↦ Fp2.conjugate`);
* mirror → spec is mathematics, with no machine words involved.

Nothing here is executed; it only has to be faithful.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls

/-! ## `Fp12` operations the spec does not have -/

/-- `a · s` for `a ∈ Fp2`, `s ∈ Fp`, componentwise. -/
def fp2MulFp (a : Fp2) (s : Fp) : Fp2 := ⟨a.c0 * s, a.c1 * s⟩

/-- `ξ = 1 + i`. -/
def xi : Fp2 := ⟨Fp.one, Fp.one⟩

/-- `γₙ,ₖ = ξ^(k·(pⁿ − 1)/6)`. -/
def gamma (n k : Nat) : Fp2 := Fp2.powNat xi (k * ((Fp.modulus ^ n - 1) / 6))

/-- The implementation's `Fp12.frobenius1`. -/
def frobenius1 (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0.conjugate, a.c0.c1.conjugate * gamma 1 2, a.c0.c2.conjugate * gamma 1 4⟩,
   ⟨a.c1.c0.conjugate * gamma 1 1, a.c1.c1.conjugate * gamma 1 3,
    a.c1.c2.conjugate * gamma 1 5⟩⟩

/-- The implementation's `Fp12.frobenius2`. -/
def frobenius2 (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0, a.c0.c1 * gamma 2 2, a.c0.c2 * gamma 2 4⟩,
   ⟨a.c1.c0 * gamma 2 1, a.c1.c1 * gamma 2 3, a.c1.c2 * gamma 2 5⟩⟩

/-- The implementation's `Fp12.sqrFp4`. -/
def sqrFp4 (a0 a1 : Fp2) : Fp2 × Fp2 :=
  let t0 := a0 * a0
  let t1 := a1 * a1
  (t1.mulByOnePlusI + t0, (a0 + a1) * (a0 + a1) - t0 - t1)

/-- `3t − 2a`, as the implementation computes it. -/
def threeSubTwo (t a : Fp2) : Fp2 := ((t - a) + (t - a)) + t

/-- `3t + 2a`, as the implementation computes it. -/
def threeAddTwo (t a : Fp2) : Fp2 := ((t + a) + (t + a)) + t

/-- The implementation's `Fp12.cycSqr` (Granger–Scott). -/
def cycSqr (a : Fp12) : Fp12 :=
  let (t00, t01) := sqrFp4 a.c0.c0 a.c1.c1
  let (t10, t11) := sqrFp4 a.c1.c0 a.c0.c2
  let (t20, t21) := sqrFp4 a.c0.c1 a.c1.c2
  ⟨⟨threeSubTwo t00 a.c0.c0, threeSubTwo t10 a.c0.c1, threeSubTwo t20 a.c0.c2⟩,
   ⟨threeAddTwo t21.mulByOnePlusI a.c1.c0, threeAddTwo t01 a.c1.c1,
    threeAddTwo t11 a.c1.c2⟩⟩

/-! ## Miller loop -/

/-- `(X : Y : Z)` on the twist. -/
structure TwistPoint where
  x : Fp2
  y : Fp2
  z : Fp2

/-- The implementation's `PairInput`. -/
structure PairInput where
  r : TwistPoint
  cx : Fp
  cy : Fp
  cz : Fp
  pAffine : Bool

/-- A sparse line `b0 + b1·v + b4·v·w`. -/
structure Line where
  b0 : Fp2
  b1 : Fp2
  b4 : Fp2

/-- The line `b0 + b1·v + b4·v·w` as an `Fp12`. -/
def Line.toFp12 (l : Line) : Fp12 :=
  ⟨⟨l.b0, l.b1, Fp2.zero⟩, ⟨Fp2.zero, l.b4, Fp2.zero⟩⟩

def PairInput.line (pi : PairInput) (b0 b1 b4 : Fp2) : Line :=
  ⟨if pi.pAffine then b0 else fp2MulFp b0 pi.cz, fp2MulFp b1 pi.cx, fp2MulFp b4 pi.cy⟩

/-- The implementation's `dblStep`. -/
def dblStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  if t.y.isZero then
    (⟨-(t.x + t.x), t.y, t.z⟩, pi.line (-t.y) Fp2.zero t.z)
  else
    let n := t.x * t.x
    let n := (n + n) + n
    let d := t.y * t.z + t.y * t.z
    let d2 := d * d
    let xd2 := t.x * d2
    let w := n * n * t.z - (xd2 + xd2)
    let d3 := d2 * d
    let x' := w * d
    let y' := n * (xd2 - w) - t.y * d3
    let z' := d3 * t.z
    (⟨x', y', z'⟩, pi.line (n * t.x - t.y * d) (-(n * t.z)) (d * t.z))

/-- The implementation's `addStep`. -/
def addStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  let r := pi.r
  let nn := r.y * t.z - t.y * r.z
  let dd := r.x * t.z - t.x * r.z
  let xr := t.x * r.z
  let s := xr + r.x * t.z
  let zz := t.z * r.z
  if dd.isZero then
    (⟨-s, -(t.y * r.z), zz⟩, pi.line (-t.y) Fp2.zero t.z)
  else
    let dd2 := dd * dd
    let w := nn * nn * zz - s * dd2
    let dd3 := dd2 * dd
    let x' := dd * w
    let y' := nn * (dd2 * xr - w) - t.y * r.z * dd3
    let z' := dd3 * zz
    (⟨x', y', z'⟩, pi.line (nn * t.x - t.y * dd) (-(nn * t.z)) (dd * t.z))

def dblAll (f : Fp12) : List (PairInput × TwistPoint) → Fp12 × List (PairInput × TwistPoint)
  | [] => (f, [])
  | (pi, t) :: rest =>
    let (t', l) := dblStep pi t
    let (f', rest') := dblAll (f * l.toFp12) rest
    (f', (pi, t') :: rest')

def addAll (f : Fp12) : List (PairInput × TwistPoint) → Fp12 × List (PairInput × TwistPoint)
  | [] => (f, [])
  | (pi, t) :: rest =>
    let (t', l) := addStep pi t
    let (f', rest') := addAll (f * l.toFp12) rest
    (f', (pi, t') :: rest')

def millerSteps : Nat → List (PairInput × TwistPoint) → Fp12 → Fp12
  | 0, _, f => f
  | n + 1, st, f =>
    let (f, st) := dblAll (f * f) st
    let (f, st) := if (blsX >>> n) &&& 1 = 1 then addAll f st else (f, st)
    millerSteps n st f

def PairInput.ofPoints (p : G1) (q : G2) : PairInput :=
  let r : TwistPoint :=
    if q.z.beq Fp2.one then ⟨q.x, q.y, Fp2.one⟩
    else ⟨q.x * q.z, q.y, q.z * q.z * q.z⟩
  if p.z.beq Fp.one then ⟨r, p.x, p.y, Fp.one, true⟩
  else ⟨r, p.x * p.z, p.y, p.z * p.z * p.z, false⟩

def millerLoop (pis : List PairInput) : Fp12 :=
  millerSteps blsX.log2 (pis.map fun pi => (pi, pi.r)) Fp12.one

/-! ## Final exponentiation -/

def cycPowMsb (g : Fp12) (k : Nat) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | n + 1, acc =>
    let acc := cycSqr acc
    cycPowMsb g k n (if (k >>> n) &&& 1 = 1 then acc * g else acc)

def cycPowAbsX (g : Fp12) : Fp12 := cycPowMsb g blsX 63 g

/-- The implementation's `finalExpCube`. -/
def finalExpCube (f : Fp12) : Fp12 :=
  let f1 := f.conjugate * f.inverse
  let g := frobenius2 f1 * f1
  let a0 := cycPowAbsX g * g
  let a := cycPowAbsX a0 * a0
  let b := (cycPowAbsX a).conjugate * frobenius1 a
  let c := cycPowAbsX (cycPowAbsX b) * frobenius2 b * b.conjugate
  c * (cycSqr g * g)

/-- The implementation's `pairingCheck`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool :=
  let pis := pairs.toList.filterMap fun (p, q) =>
    if p.isInfinity || q.isInfinity then none else some (PairInput.ofPoints p q)
  (finalExpCube (millerLoop pis).conjugate).isOne

end EthLibImpl.Cryptography.Bls.Mirror
