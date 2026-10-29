import EthLibImpl.Cryptography.Bls.Fp

/-!
# `Fp2`

`Fp2 = Fp[i] / (i² + 1)`, holding `c0 + c1·i` like the spec, but stored flat:
one object with twelve unboxed words (`c0`'s six, then `c1`'s six) instead
of a pair of `Fp` objects. Every operation is built from the inlined `Fp`
forms (`Fp.mulI`, `Fp.addI`, …), so its intermediate `Fp` values live in
registers and the operation allocates exactly one object, its result.
`c0`/`c1` read the halves and `mk` builds from them; both inline away.

Differences from the spec, all value-preserving:

* `mul` is Karatsuba (3 base multiplications instead of 4), and `sqr`
  uses `(a + b)(a − b)` for the real part.
* `sqrt` returns *a* square root, not necessarily the spec's. Both callers
  (G2 decompression and SSWU) normalize the sign afterwards, so only
  "is it a square" and "is it a root" matter. It costs two `Fp`
  exponentiations and no inversion; the spec's costs up to four
  exponentiations.
-/

namespace EthLibImpl.Cryptography.Bls

open EthLib.Cryptography.Bls (BlsError)

/-- An element of `Fp2`, `c0 + c1 · i` with `i² = −1`, as twelve words:
`a0 … a5` are `c0`'s, `b0 … b5` are `c1`'s. -/
structure Fp2 where
  ofWords ::
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  b0 : UInt64
  b1 : UInt64
  b2 : UInt64
  b3 : UInt64
  b4 : UInt64
  b5 : UInt64
deriving Inhabited, Repr

namespace Fp2

/-- The real part. -/
@[inline] def c0 (x : Fp2) : Fp := ⟨x.a0, x.a1, x.a2, x.a3, x.a4, x.a5⟩

/-- The imaginary part. -/
@[inline] def c1 (x : Fp2) : Fp := ⟨x.b0, x.b1, x.b2, x.b3, x.b4, x.b5⟩

/-- `c0 + c1·i`. -/
@[inline] def mk (c0 c1 : Fp) : Fp2 :=
  ⟨c0.l0, c0.l1, c0.l2, c0.l3, c0.l4, c0.l5, c1.l0, c1.l1, c1.l2, c1.l3, c1.l4, c1.l5⟩

def zero : Fp2 := mk Fp.zero Fp.zero
def one  : Fp2 := mk Fp.one Fp.zero

@[inline] def ofFp (x : Fp) : Fp2 := mk x Fp.zero

/-! As in `Fp`, each operation has an `@[inline]` form for fused callers
(`Fp6`, `Fp12`, the curve formulas) and a plain one; they are equal by
definition. -/

@[inline] def addI (a b : Fp2) : Fp2 := mk (Fp.addI a.c0 b.c0) (Fp.addI a.c1 b.c1)
@[inline] def subI (a b : Fp2) : Fp2 := mk (Fp.subI a.c0 b.c0) (Fp.subI a.c1 b.c1)
@[inline] def negI (a : Fp2) : Fp2 := mk (Fp.negI a.c0) (Fp.negI a.c1)
@[inline] def doubleI (a : Fp2) : Fp2 := mk (Fp.doubleI a.c0) (Fp.doubleI a.c1)

/-- Karatsuba with lazy reduction: `(a0 + a1 i)(b0 + b1 i)` from three
wide products and two Montgomery reductions. The real part
`a0·b0 − a1·b1` gets `p·R` added when negative; the imaginary part
`(a0 + a1)(b0 + b1) − a0·b0 − a1·b1 = a0·b1 + a1·b0` is exact and below
`2p²`, with the sums `a0 + a1`, `b0 + b1` left unreduced (below `2p`). -/
@[inline] def mulI (a b : Fp2) : Fp2 :=
  let a0 := a.c0
  let a1 := a.c1
  let b0 := b.c0
  let b1 := b.c1
  let t0 := Fp.mulWide a0 b0
  let t1 := Fp.mulWide a1 b1
  let t2 := Fp.mulWide (Fp.addRaw a0 a1) (Fp.addRaw b0 b1)
  mk (Fp.redc (Fp.subWideModPR t0 t1)) (Fp.redc (Fp.sub12 (Fp.sub12 t2 t0).1 t1).1)

/-- `(a0 + a1 i)² = (a0 + a1)(a0 − a1) + (2·a0)·a1·i`. -/
@[inline] def sqrI (a : Fp2) : Fp2 :=
  let a0 := a.c0
  let a1 := a.c1
  -- The Montgomery product accepts any first factor below `2^384`, so the
  -- sums `a0 + a1` and `2·a0` (below `2p`) are left unreduced.
  mk (Fp.mulI (Fp.addRaw a0 a1) (Fp.subI a0 a1)) (Fp.mulI (Fp.addRaw a0 a0) a1)

/-- Multiply by `ξ = 1 + i`. -/
@[inline] def mulByXiI (a : Fp2) : Fp2 :=
  let a0 := a.c0
  let a1 := a.c1
  mk (Fp.subI a0 a1) (Fp.addI a0 a1)

@[inline] def add (a b : Fp2) : Fp2 := addI a b
@[inline] def sub (a b : Fp2) : Fp2 := subI a b
@[inline] def neg (a : Fp2) : Fp2 := negI a
@[inline] def double (a : Fp2) : Fp2 := doubleI a
def mul (a b : Fp2) : Fp2 := mulI a b
def sqr (a : Fp2) : Fp2 := sqrI a
@[inline] def mulByXi (a : Fp2) : Fp2 := mulByXiI a

/-- Multiply by a base-field scalar. -/
def mulFp (a : Fp2) (s : Fp) : Fp2 := mk (Fp.mulI a.c0 s) (Fp.mulI a.c1 s)

instance : Add Fp2 := ⟨add⟩
instance : Sub Fp2 := ⟨sub⟩
instance : Mul Fp2 := ⟨mul⟩
instance : Neg Fp2 := ⟨neg⟩

@[inline] def beq (a b : Fp2) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1
@[inline] def isZero (a : Fp2) : Bool := a.c0.isZero && a.c1.isZero
instance : BEq Fp2 := ⟨beq⟩

/-- Conjugation `c0 + c1 i ↦ c0 − c1 i`, which is also the Frobenius map. -/
@[inline] def conj (a : Fp2) : Fp2 := mk a.c0 (Fp.negI a.c1)

/-- Spec `Fp2.inverse`: `(c0 − c1 i) / (c0² + c1²)`. -/
def inverse (a : Fp2) : Fp2 :=
  let invN := (a.c0 * a.c0 + a.c1 * a.c1).inverse
  mk (a.c0 * invN) (-(a.c1 * invN))

instance : Div Fp2 := ⟨fun a b => a * b.inverse⟩

/-- Inverses of `a` and `b` for one inversion (Montgomery's trick), with
the spec's `inverse 0 = 0`: a zero input is replaced by `1` in the shared
product and its own result is `0`. -/
def batchInverse2 (a b : Fp2) : Fp2 × Fp2 :=
  let a' := if a.isZero then one else a
  let b' := if b.isZero then one else b
  let i := (a' * b').inverse
  (if a.isZero then zero else i * b', if b.isZero then zero else i * a')

/-- `batchInverse2` for four values. -/
def batchInverse4 (a b c d : Fp2) : Fp2 × Fp2 × Fp2 × Fp2 :=
  let a' := if a.isZero then one else a
  let b' := if b.isZero then one else b
  let c' := if c.isZero then one else c
  let d' := if d.isZero then one else d
  let ab := a' * b'
  let cd := c' * d'
  let i := (ab * cd).inverse
  let iab := i * cd
  let icd := i * ab
  (if a.isZero then zero else iab * b', if b.isZero then zero else iab * a',
   if c.isZero then zero else icd * d', if d.isZero then zero else icd * c')

/-- Spec `Fp2.powNat`, same recursion. Used for constants. -/
def powNat (base : Fp2) (e : Nat) : Fp2 :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- `1/2`. -/
def halfFp : Fp := (Fp.ofNat 2).inverse

/-- Some square root of `a`, or `notASquare`. Callers that need a specific
root must normalize its sign.

For `a = a0 + a1 i` with `a1 ≠ 0`, a root `c0 + c1 i` satisfies
`c0² = (a0 + s)/2` and `c1² = (s − a0)/2` for `s` a square root of the
norm `a0² + a1²`. With `t = (a0 + s)/2` and `δ = t^((p−3)/4)` (`Fp.invSqrtWin`; for `t ≠ 0`,
`δ²·t = ±1` by Euler's criterion, `+1` iff `t` is a square):
if `t` is a square, `c0 = δt` and `c1 = a1/(2c0) = a1δ/2`; otherwise `−t`
is, and taking `−s` instead gives `c1 = δt`, `c0 = a1/(2c1) = −a1δ/2`.
(`t ≠ 0` here: `t = 0` would force `a1 = 0`.)

`a` is a square in `Fp2` iff its norm is a square in `Fp`, so the only
failure is `Fp.sqrt` rejecting the norm. Every element of `Fp` is a square
in `Fp2`, so the `a1 = 0` branch never fails. -/
def sqrt (a : Fp2) : Except BlsError Fp2 :=
  if a.c1.isZero then
    -- `a = a0 ∈ Fp`: `δ·a0` is a root of `a0` if `a0` is a square (or
    -- zero), otherwise of `−a0`, and then `i·δ·a0` is a root of `a0`.
    let d := Fp.powWin a.c0 Fp.invSqrtWin
    let s := d * a.c0
    if (d * s).beq Fp.one then .ok (mk s Fp.zero) else .ok (mk Fp.zero s)
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match Fp.sqrt n with
    | .error _ => .error .notASquare
    | .ok s =>
      let t := (a.c0 + s) * halfFp
      let d := Fp.powWin t Fp.invSqrtWin
      let dt := d * t
      let hd := a.c1 * d * halfFp
      if (d * dt).beq Fp.one then .ok (mk dt hd) else .ok (mk (-hd) dt)

/-- The second half of `sqrt` for `a.c1 ≠ 0`, given a square root `s` of
the norm `a0² + a1²` (either one: `t·t' = −a1²/4` for `t = (a0 + s)/2`
and `t' = (a0 − s)/2`, and `−1` is a non-square, so exactly one of `t`,
`−t` is a square whichever root is taken). Callers that already hold such
an `s` skip the norm's exponentiation inside `sqrt`. -/
def sqrtGivenNorm (a : Fp2) (s : Fp) : Fp2 :=
  let t := (a.c0 + s) * halfFp
  let d := Fp.powWin t Fp.invSqrtWin
  let dt := d * t
  let hd := a.c1 * d * halfFp
  if (d * dt).beq Fp.one then mk dt hd else mk (-hd) dt

end Fp2

end EthLibImpl.Cryptography.Bls
