import EthLibImpl.Cryptography.Bls.Limbs

/-!
# Proofs: word primitives

The carry helpers of `EthLibImpl.Cryptography.Bls.Limbs` as equations
over `Nat`. Everything about multi-word arithmetic reduces to these facts
plus `omega`.

`mulHi` is specified by its Lean body; that the compiled code computes
the same value is the one assumption about C this implementation makes
(the body is `(a·b) >>> 64` and the C is `(unsigned __int128)a*b >> 64`).
-/

namespace EthLibImpl.Cryptography.Bls.Limbs

theorem mulHi_toNat (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have hlt : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact Nat.mul_lt_mul'' a.toNat_lt b.toNat_lt
  simp only [mulHi, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt hlt

/-- The low word of a product. -/
theorem mul_toNat_add_mulHi (a b : UInt64) :
    (a * b).toNat + 2 ^ 64 * (mulHi a b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, mulHi_toNat]
  exact Nat.mod_add_div _ _

/-- Carry detection by comparing the sum with its second operand. -/
theorem carry_snd (x y : UInt64) :
    (x + y).toNat + 2 ^ 64 * (if x + y < y then (1 : UInt64) else 0).toNat =
      x.toNat + y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega

/-- Carry detection by comparing the sum with its first operand. -/
theorem carry_fst (x y : UInt64) :
    (x + y).toNat + 2 ^ 64 * (if x + y < x then (1 : UInt64) else 0).toNat =
      x.toNat + y.toNat := by
  have h := carry_snd y x
  rw [UInt64.add_comm y x] at h
  omega

theorem ite_toNat_le_one (c : Prop) [Decidable c] :
    (if c then (1 : UInt64) else 0).toNat ≤ 1 := by
  split <;> simp

/-- `mac t a b c = (lo, hi)` with `lo + 2^64·hi = t + a·b + c`. -/
theorem mac_spec (t a b c : UInt64) :
    (mac t a b c).1.toNat + 2 ^ 64 * (mac t a b c).2.toNat =
      t.toNat + a.toNat * b.toNat + c.toNat := by
  have hP : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  have ht := t.toNat_lt
  have hc := c.toNat_lt
  have hprod := mul_toNat_add_mulHi a b
  have h1 := carry_snd (a * b) t
  have h2 := carry_snd (a * b + t) c
  have c1 := ite_toNat_le_one (a * b + t < t)
  have c2 := ite_toNat_le_one (a * b + t + c < c)
  simp only [mac]
  generalize (if a * b + t < t then (1 : UInt64) else 0) = k1 at *
  generalize (if a * b + t + c < c then (1 : UInt64) else 0) = k2 at *
  generalize a * b + t = s at *
  generalize a.toNat * b.toNat = P at *
  -- the high word cannot overflow: the whole sum is below 2^128
  have hs := s.toNat_lt
  have hs2 := (s + c).toNat_lt
  rw [UInt64.toNat_add (mulHi a b + k1) k2, UInt64.toNat_add (mulHi a b) k1]
  have hm := (mulHi a b).toNat_lt
  omega

/-- `adc a b c = (s, c')` with `s + 2^64·c' = a + b + c` and `c' ≤ 1`, for
`c ≤ 1`. -/
theorem adc_spec (a b c : UInt64) (hc : c.toNat ≤ 1) :
    (adc a b c).1.toNat + 2 ^ 64 * (adc a b c).2.toNat = a.toNat + b.toNat + c.toNat ∧
      (adc a b c).2.toNat ≤ 1 := by
  have h1 := carry_fst a b
  have h2 := carry_snd (a + b) c
  have c1 := ite_toNat_le_one (a + b < a)
  have c2 := ite_toNat_le_one (a + b + c < c)
  simp only [adc]
  generalize (if a + b < a then (1 : UInt64) else 0) = k1 at *
  generalize (if a + b + c < c then (1 : UInt64) else 0) = k2 at *
  generalize a + b = s at *
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hs := s.toNat_lt
  rw [UInt64.toNat_add k1 k2]
  omega

/-- Borrow detection: `a - b` borrows iff `a < b`. -/
theorem borrow_spec (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (if a < b then (1 : UInt64) else 0).toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [UInt64.toNat_sub]
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [UInt64.reduceToNat]
    omega
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [UInt64.reduceToNat]
    omega

/-- `sbb a b br = (d, br')` with `d + b + br = a + 2^64·br'` and `br' ≤ 1`,
for `br ≤ 1`. -/
theorem sbb_spec (a b br : UInt64) (hbr : br.toNat ≤ 1) :
    (sbb a b br).1.toNat + b.toNat + br.toNat = a.toNat + 2 ^ 64 * (sbb a b br).2.toNat ∧
      (sbb a b br).2.toNat ≤ 1 := by
  have h1 := borrow_spec a b
  have h2 := borrow_spec (a - b) br
  have c1 := ite_toNat_le_one (a < b)
  have c2 := ite_toNat_le_one (a - b < br)
  simp only [sbb]
  generalize (if a < b then (1 : UInt64) else 0) = k1 at *
  generalize (if a - b < br then (1 : UInt64) else 0) = k2 at *
  generalize a - b = d at *
  have ha := a.toNat_lt
  have hd := d.toNat_lt
  have hdb := (d - br).toNat_lt
  have hb := b.toNat_lt
  rw [UInt64.toNat_add k1 k2]
  omega

end EthLibImpl.Cryptography.Bls.Limbs
