/-!
# `Limbs`

64-bit word primitives for multi-precision arithmetic.

Lean has no 64×64→128-bit multiply, so `mulHi` is the single place where
this implementation trusts C: its Lean body is the definition every proof
sees, and the compiler replaces each call with the one-line C expression in
the `extern` attribute (`umulh` on AArch64, `mul` on x86-64). Everything
else is plain `UInt64` arithmetic, which Lean compiles to native C
operations.

The carry helpers return pairs; they are `@[inline]`, so after inlining the
compiler cancels each `Prod.mk` against its projections and no pair is ever
allocated.
-/

namespace EthLibImpl.Cryptography.Bls.Limbs

/-- High 64 bits of the 128-bit product `a * b`. -/
@[extern c inline "(uint64_t)(((unsigned __int128)#1 * (unsigned __int128)#2) >> 64)"]
def mulHi (a b : UInt64) : UInt64 := ((a.toNat * b.toNat) >>> 64).toUInt64

/-- `t + a * b + c` as `(low, high)`. Never overflows: the sum is at most
`2^128 - 1`. -/
@[inline] def mac (t a b c : UInt64) : UInt64 × UInt64 :=
  let lo := a * b
  let hi := mulHi a b
  let s := lo + t
  let hi := hi + (if s < t then 1 else 0)
  let s2 := s + c
  let hi := hi + (if s2 < c then 1 else 0)
  (s2, hi)

/-- `a + b + c` as `(sum, carry)` for a carry-in `c ≤ 1`. -/
@[inline] def adc (a b c : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let c1 : UInt64 := if s < a then 1 else 0
  let s2 := s + c
  let c2 : UInt64 := if s2 < c then 1 else 0
  (s2, c1 + c2)

/-- `a - b - br` as `(difference, borrow)` for a borrow-in `br ≤ 1`. -/
@[inline] def sbb (a b br : UInt64) : UInt64 × UInt64 :=
  let d := a - b
  let b1 : UInt64 := if a < b then 1 else 0
  let d2 := d - br
  let b2 : UInt64 := if d < br then 1 else 0
  (d2, b1 + b2)

end EthLibImpl.Cryptography.Bls.Limbs
