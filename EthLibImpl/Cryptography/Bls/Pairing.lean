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
* **Final exponentiation** computes exactly the cube `f^(3·(p¹² − 1)/r)`
  of the spec's value: `(p¹² − 1)/r = (p⁶ − 1)(p² + 1)·h` and
  `3h = (x − 1)²(x + p)(x² + p² − 1) + 3`. The check only compares the
  result with one, which the cube preserves (see `finalExpCube`).
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

/-- A twist point in Jacobian coordinates `(X : Y : Z)`, standing for the
affine `(X/Z², Y/Z³)`. -/
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

/-- Doubling step: `2T` and the tangent line at `T`, scaled by `w³·2YZ³`
times `Zp³`. The point formulas are the spec's G2 doubling (valid for any
`a = 0` curve, so no point needs to be on the twist): with `E = 3X²` and
`Z' = 2YZ`, the affine slope is `E/Z'`; the line coefficients are
`(E·X − 2Y², −E·Z², Z'·Z²)`. -/
def dblStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  if t.y.isZero then
    -- Spec: slope `0`, so `2T = (−2·tx, −ty)` and the line is `yp − ty·w⁻³`
    -- (here `ty = 0`).
    (⟨-t.x.double, t.y, t.z⟩, pi.line t.y.neg Fp2.zero Fp2.one)
  else
    let a := t.x.sqr
    let b := t.y.sqr
    let c := b.sqr
    let d := ((t.x + b).sqr - a - c).double
    let e := a.double + a
    let x' := e.sqr - d.double
    let y' := e * (d - x') - c.double.double.double
    let z' := (t.y * t.z).double
    let zz := t.z.sqr
    (⟨x', y', z'⟩, pi.line (e * t.x - b.double) (-(e * zz)) (z' * zz))

/-- Addition step: `T + R` and the line through them, both in Jacobian
coordinates. With `U1 = X·Zr²`, `U2 = Xr·Z²`, `S1 = Y·Zr³`, `S2 = Yr·Z³`,
`H = U2 − U1`, `N = S2 − S1` and `Z' = Z·Zr·H`, the affine slope is
`N/Z'`; the line is scaled by `w³·Z'·Z²` times `Zp³`. -/
def addStep (pi : PairInput) (t : TwistPoint) : TwistPoint × Line :=
  let r := pi.r
  let z1z1 := t.z.sqr
  let z2z2 := r.z.sqr
  let u1 := t.x * z2z2
  let u2 := r.x * z1z1
  let s1 := t.y * (r.z * z2z2)
  let s2 := r.y * (t.z * z1z1)
  let h := u2 - u1
  let zz := t.z * r.z
  if h.isZero then
    -- Spec: slope `0`, so `T + R = (−tx − rx, −ty)` and the line is
    -- `yp − ty·w⁻³`.
    (⟨-(u1 + u2), -s1, zz⟩, pi.line t.y.neg Fp2.zero (t.z * z1z1))
  else
    let n := s2 - s1
    let hh := h.sqr
    let hhh := hh * h
    let v := u1 * hh
    let x' := n.sqr - hhh - v.double
    let y' := n * (v - x') - s1 * hhh
    let z' := zz * h
    (⟨x', y', z'⟩, pi.line (n * t.x - r.z * h * t.y) (-(n * z1z1)) (z' * z1z1))

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
  let r : TwistPoint := ⟨q.x, q.y, q.z⟩
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

/-- Exactly `f^(3·(p¹² − 1)/r)`, the cube of the spec's final
exponentiation. Since `3·(p⁴ − p² + 1)/r = (x − 1)²(x + p)(x² + p² − 1) + 3`
(Hayashida–Hayasaka–Teruya), the hard part needs only ladders in
`|x| + 1` and `|x|` (Hamming weights 7 and 6). The exact exponent
`(p⁴ − p² + 1)/r` needs the factor `(|x| + 1)/3`, whose 28 set bits cost
27 more `Fp12` products. The pairing check only asks whether the result is
one, and cubing preserves that on the `r`-th roots of unity, where the
final exponentiation lands (`3` is prime to `r`). -/
def finalExpCube (f : Fp12) : Fp12 :=
  -- Easy part: `g = f^((p⁶ − 1)(p² + 1))`.
  let f1 := f.conj * f.inverse
  let g := f1.frobenius2 * f1
  -- `a = g^((x − 1)²) = g^((|x| + 1)²)`.
  let a0 := cycPowAbsX g * g
  let a := cycPowAbsX a0 * a0
  -- `b = a^(x + p)`, with `a^x = conj(a^|x|)`.
  let b := (cycPowAbsX a).conj * a.frobenius1
  -- `c = b^(x² + p² − 1)`.
  let c := cycPowAbsX (cycPowAbsX b) * b.frobenius2 * b.conj
  c * (g.cycSqr * g)

/-! ## The pairing -/

/-- Spec `pairingCheck`: `true` iff `∏ e(Pᵢ, Qᵢ) = 1`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool :=
  let pis := pairs.toList.filterMap fun (p, q) =>
    if p.isInfinity || q.isInfinity then none else some (PairInput.ofPoints p q)
  (finalExpCube (millerLoop pis).conj).isOne

end EthLibImpl.Cryptography.Bls
