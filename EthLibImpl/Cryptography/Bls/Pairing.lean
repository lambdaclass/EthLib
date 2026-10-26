import EthLibImpl.Cryptography.Bls.G1
import EthLibImpl.Cryptography.Bls.G2
import EthLibImpl.Cryptography.Bls.Fp12

/-!
# `Pairing`

`pairingCheck` with the spec's result on every input, computed the way
fast implementations do:

* **Miller loop on the twist.** The spec untwists `Q` into `E(Fp12)` and
  runs the affine Miller loop there, with one `Fp12` inversion per step.
  The untwisted points have the shape `(tx·w⁻², ty·w⁻³)` with `tx, ty ∈ Fp2`
  throughout, so this loop tracks `(tx, ty)` instead, in homogeneous
  projective coordinates `(X : Y : Z)` (no inversions), and multiplies `f`
  by the spec's line value scaled by `w³` and by a nonzero `Fp2` factor.
  Those factors are sent to `1` by the final exponentiation
  (`(p¹² − 1)/r` is a multiple of `6(p² − 1)`), so the pairing value is
  unchanged. All pairs share one squaring of `f` per step.
* **Degenerate steps follow the spec.** When a slope denominator is zero
  (doubling a point with `ty = 0`, or adding a point with the same `tx`),
  the spec's `inverse 0 = 0` makes the slope `0`. The step functions
  branch on exactly that case and compute the spec's resulting point and
  line, so no input is excluded.
* **Final exponentiation** computes exactly `f^((p¹² − 1)/r)`:
  `(p¹² − 1)/r = (p⁶ − 1)(p² + 1)·h` with
  `h = λ·(x + p)(x² + p² − 1) + 1` and `λ = (x − 1)²/3 = ((|x|+1)/3)(|x|+1)`.
  The first two factors use conjugation (`a^(p⁶)`) and `frobenius2`. Their
  result lies in the cyclotomic subgroup, where `cycSqr` squares and
  conjugation inverts.
-/

namespace EthLibImpl.Cryptography.Bls

/-- `|x|` for the BLS parameter `x = −0xd201000000010000`. -/
def blsX : Nat := 0xd201000000010000

/-- `blsX` as a word. -/
def blsXWord : UInt64 := 0xd201000000010000

/-! ## Miller loop -/

/-- A twist point `(X : Y : Z)`, standing for the affine `(X/Z, Y/Z)`. -/
structure TwistPoint where
  x : Fp2
  y : Fp2
  z : Fp2
deriving Inhabited

/-- One pair, prepared for the loop. `P = (Xp, Yp, Zp)` in Jacobian
coordinates enters through `cx = Xp·Zp`, `cy = Yp`, `cz = Zp³`: the line
value at the affine `(Xp/Zp², Yp/Zp³)`, times `Zp³`. -/
structure PairInput where
  r : TwistPoint
  cx : Fp
  cy : Fp
  cz : Fp
  pAffine : Bool
deriving Inhabited

/-- A sparse line `b0 + b1·v + b4·v·w`. -/
structure Line where
  b0 : Fp2
  b1 : Fp2
  b4 : Fp2

/-- Evaluate line coefficients at `P`: `b0·cz + (b1·cx)·v + (b4·cy)·v·w`,
where `b1`, `b4` still need the `x`/`y` coordinate of `P`. -/
@[inline] def PairInput.line (pi : PairInput) (b0 b1 b4 : Fp2) : Line :=
  ⟨if pi.pAffine then b0 else b0.mulFp pi.cz, b1.mulFp pi.cx, b4.mulFp pi.cy⟩

/-- Doubling step: `2T` and the tangent line at `T` (scaled by `w³·2YZ²`
times `Zp³`). With `N = 3X²`, `D = 2YZ`, the affine slope is `N/D` and
`2T = (W·D : N·(X·D² − W) − Y·D³ : D³·Z)` with `W = N²·Z − 2X·D²`. -/
def dblStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  if t.y.isZero then
    -- Spec: slope `0`, so `2T = (−2·tx, −ty)` and the line is `yp − ty·w⁻³`.
    (⟨-t.x.double, t.y, t.z⟩, pi.line t.y.neg Fp2.zero t.z)
  else
    let n := t.x.sqr
    let n := n.double + n
    let d := (t.y * t.z).double
    let d2 := d.sqr
    let xd2 := t.x * d2
    let w := n.sqr * t.z - xd2.double
    let d3 := d2 * d
    let x' := w * d
    let y' := n * (xd2 - w) - t.y * d3
    let z' := d3 * t.z
    (⟨x', y', z'⟩, pi.line (n * t.x - t.y * d) (-(n * t.z)) (d * t.z))

/-- Addition step: `T + R` and the line through them (scaled by
`w³·Dd·Z` times `Zp³`). With `Nn = Yr·Z − Y·Zr`, `Dd = Xr·Z − X·Zr`, the
affine slope is `Nn/Dd`. -/
def addStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  let r := pi.r
  let nn := r.y * t.z - t.y * r.z
  let dd := r.x * t.z - t.x * r.z
  let xr := t.x * r.z
  let s := xr + r.x * t.z
  let zz := t.z * r.z
  if dd.isZero then
    -- Spec: slope `0`, so `T + R = (−tx − rx, −ty)` and the line is
    -- `yp − ty·w⁻³`.
    (⟨-s, -(t.y * r.z), zz⟩, pi.line t.y.neg Fp2.zero t.z)
  else
    let dd2 := dd.sqr
    let w := nn.sqr * zz - s * dd2
    let dd3 := dd2 * dd
    let x' := dd * w
    let y' := nn * (dd2 * xr - w) - t.y * r.z * dd3
    let z' := dd3 * zz
    (⟨x', y', z'⟩, pi.line (nn * t.x - t.y * dd) (-(nn * t.z)) (dd * t.z))

/-- Doubling step for every pair: the new points, and `f` times every
pair's tangent line, in pair order. -/
def dblAll (f : Fp12) : List (PairInput × TwistPoint) → Fp12 × List (PairInput × TwistPoint)
  | [] => (f, [])
  | (pi, t) :: rest =>
    let (t', l) := dblStep pi t
    let (f', rest') := dblAll (f.mulBy014 l.b0 l.b1 l.b4) rest
    (f', (pi, t') :: rest')

/-- Addition step for every pair. -/
def addAll (f : Fp12) : List (PairInput × TwistPoint) → Fp12 × List (PairInput × TwistPoint)
  | [] => (f, [])
  | (pi, t) :: rest =>
    let (t', l) := addStep pi t
    let (f', rest') := addAll (f.mulBy014 l.b0 l.b1 l.b4) rest
    (f', (pi, t') :: rest')

/-- Run all pairs through the bits `n - 1 … 0` of `blsX`, sharing the
squaring of `f`. -/
def millerSteps : Nat → List (PairInput × TwistPoint) → Fp12 → Fp12
  | 0, _, f => f
  | n + 1, st, f =>
    let (f, st) := dblAll f.sqr st
    let (f, st) := if (blsXWord >>> n.toUInt64) &&& 1 != 0 then addAll f st else (f, st)
    millerSteps n st f

/-- Prepare a pair of non-infinity points. -/
def PairInput.ofPoints (p : G1) (q : G2) : PairInput :=
  let r : TwistPoint :=
    if q.z.beq Fp2.one then ⟨q.x, q.y, Fp2.one⟩
    else ⟨q.x * q.z, q.y, q.z.sqr * q.z⟩
  if p.z.beq Fp.one then ⟨r, p.x, p.y, Fp.one, true⟩
  else ⟨r, p.x * p.z, p.y, p.z.sqr * p.z, false⟩

/-- The product of the pairs' Miller loops (each up to factors the final
exponentiation removes). -/
def millerLoop (pis : List PairInput) : Fp12 :=
  millerSteps blsX.log2 (pis.map fun pi => (pi, pi.r)) Fp12.one

/-! ## Final exponentiation -/

/-- `g^k` by cyclotomic squarings, most significant bit first, for `k` of
bit length `n + 1`. Valid on the cyclotomic subgroup. -/
def cycPowMsb (g : Fp12) (k : UInt64) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | n + 1, acc =>
    let acc := acc.cycSqr
    cycPowMsb g k n (if (k >>> n.toUInt64) &&& 1 != 0 then acc * g else acc)

/-- `g^|x|`. -/
def cycPowAbsX (g : Fp12) : Fp12 := cycPowMsb g blsXWord 63 g

/-- `(|x| + 1) / 3`. -/
def lamFactor : UInt64 := 0x460055555555aaab

/-- Exactly `f^((p¹² − 1) / r)`. -/
def finalExponentiation (f : Fp12) : Fp12 :=
  -- Easy part: `g = f^((p⁶ − 1)(p² + 1))`.
  let f1 := f.conj * f.inverse
  let g := f1.frobenius2 * f1
  -- `a = g^λ`, `λ = ((|x|+1)/3)·(|x|+1)`.
  let a0 := cycPowMsb g lamFactor 62 g
  let a := cycPowAbsX a0 * a0
  -- `b = a^(x + p)`, with `a^x = conj(a^|x|)`.
  let b := (cycPowAbsX a).conj * a.frobenius1
  -- `c = b^(x² + p² − 1)`.
  let c := cycPowAbsX (cycPowAbsX b) * b.frobenius2 * b.conj
  c * g

/-! ## The pairing -/

/-- Spec `pairingCheck`: `true` iff `∏ e(Pᵢ, Qᵢ) = 1`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool :=
  let pis := pairs.toList.filterMap fun (p, q) =>
    if p.isInfinity || q.isInfinity then none else some (PairInput.ofPoints p q)
  (finalExponentiation (millerLoop pis).conj).isOne

end EthLibImpl.Cryptography.Bls
