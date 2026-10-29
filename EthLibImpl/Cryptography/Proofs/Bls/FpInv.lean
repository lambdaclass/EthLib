import EthLibImpl.Cryptography.Proofs.Bls.Fp

/-!
# Inversion (`Fp.inverse`)

Proves that `Fp.inverse`, Kaliski's almost Montgomery inverse (see
`EthLibImpl.Cryptography.Bls.Fp`), is canonical and computes the spec's
`Fp.inverse` on every canonical input.

* `Inv.ctz_spec`: the binary-search trailing-zero count (`2^n ∣ x`, `x / 2^n`
  odd, `n ≤ 63`), then `tz`, `shr` and `shl` on word vectors.
* `GI`: the loop invariant `p = u·s + v·r`, `A·r + u·2^k ≡ 0`, `A·s ≡ v·2^k`,
  `1 ≤ u ≤ p`, `1 ≤ v < p`, `u·v·2^k ≤ p·A`, with one preservation lemma per
  branch of the loop.
* `Inv.go_spec`: by induction on the fuel, the loop returns `(s, k)` with
  `A·s ≡ 2^k`, `s < p` and `k < 762`; the fuel `1000` is never exhausted.
* `Inv.mulPow2_val`: the `2^j` correction.
* `inverse_canonical`, `val_inverse`: the two statements consumers use.
-/

namespace EthLibImpl.Cryptography.Bls.Fp

open Limbs
open scoped EthLib.Cryptography.Bls.Fp
open EthLib.Cryptography.Bls.Fp (toZMod toZMod_add toZMod_sub toZMod_neg toZMod_mul toZMod_zero
  toZMod_one toZMod_pow toZMod_ofNat toZMod_mk val_toZMod)

local notation "Z" => ZMod EthLib.Cryptography.Bls.Fp.modulus

namespace Inv

/-! ## Trailing zeros -/

/-- One binary-search step. -/
def cx (m sh x : UInt64) : UInt64 := if (x &&& m) == 0 then x >>> sh else x
def cn (m sh x n : UInt64) : UInt64 := if (x &&& m) == 0 then n + sh else n

/-- The invariant carried between steps. -/
def CInv (x0 : Nat) (x n : UInt64) (w : Nat) : Prop :=
  x0 = x.toNat * 2 ^ n.toNat ∧ x.toNat % 2 ^ w ≠ 0 ∧ n.toNat + w ≤ 64

theorem cx_inv (h : Nat) (m sh : UInt64) (hm : m.toNat = 2 ^ h - 1) (hsh : sh.toNat = h)
    (hh : h < 64) {x0 : Nat} {x n : UInt64} (hI : CInv x0 x n (2 * h)) :
    CInv x0 (cx m sh x) (cn m sh x n) h := by
  obtain ⟨e, hne, hb⟩ := hI
  have hand : (x &&& m).toNat = x.toNat % 2 ^ h := by
    rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  have hshr : (x >>> sh).toNat = x.toNat / 2 ^ h := by
    rw [UInt64.toNat_shiftRight, hsh, Nat.mod_eq_of_lt hh, Nat.shiftRight_eq_div_pow]
  unfold cx cn
  by_cases hz : (x &&& m) == 0
  · simp only [hz, if_true]
    have hz' : x.toNat % 2 ^ h = 0 := by
      have : x &&& m = 0 := by simpa using hz
      rw [← hand, this]; rfl
    have hx : x.toNat = x.toNat / 2 ^ h * 2 ^ h := by
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hz')).symm
    have hn : (n + sh).toNat = n.toNat + h := by
      rw [UInt64.toNat_add, hsh, Nat.mod_eq_of_lt]; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hshr, hn, pow_add, e]
      generalize x.toNat / 2 ^ h = q at hx ⊢
      generalize x.toNat = X at hx ⊢
      subst hx; ring
    · rw [hshr]
      intro hc
      apply hne
      have h2 : 2 ^ (2 * h) = 2 ^ h * 2 ^ h := by rw [two_mul, pow_add]
      rw [h2, hx, mul_comm (x.toNat / 2 ^ h) (2 ^ h)]
      rw [Nat.mul_mod_mul_left, hc]; simp
    · rw [hn]; omega
  · simp only [hz]
    simp only [Bool.false_eq_true, if_false]
    have hz' : x.toNat % 2 ^ h ≠ 0 := by
      intro hc; apply hz
      have : x &&& m = 0 := by
        apply UInt64.toNat_inj.mp; rw [hand, hc]; rfl
      simp [this]
    exact ⟨e, hz', by omega⟩


def cfin (x n : UInt64) : UInt64 := if (x &&& 0x1) == 0 then n + 1 else n

theorem ctz_eq (x : UInt64) :
    ctz x = (let n1 := cn 0xFFFFFFFF 32 x 0
             let x1 := cx 0xFFFFFFFF 32 x
             let n2 := cn 0xFFFF 16 x1 n1
             let x2 := cx 0xFFFF 16 x1
             let n3 := cn 0xFF 8 x2 n2
             let x3 := cx 0xFF 8 x2
             let n4 := cn 0xF 4 x3 n3
             let x4 := cx 0xF 4 x3
             let n5 := cn 0x3 2 x4 n4
             let x5 := cx 0x3 2 x4
             cfin x5 n5) := rfl

theorem cfin_spec {x0 : Nat} {x n : UInt64} (hI : CInv x0 x n 2) :
    (cfin x n).toNat ≤ 63 ∧ x0 % 2 ^ (cfin x n).toNat = 0 ∧ (x0 / 2 ^ (cfin x n).toNat) % 2 = 1 := by
  obtain ⟨e, hne, hb⟩ := hI
  have hand : (x &&& 1).toNat = x.toNat % 2 := by
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 1
    rw [UInt64.toNat_and]; simp at this ⊢
  unfold cfin
  by_cases hz : (x &&& 1) == 0
  · simp only [hz, if_true]
    have hz' : x.toNat % 2 = 0 := by
      have : x &&& 1 = 0 := by simpa using hz
      rw [← hand, this]; rfl
    have hn : (n + 1).toNat = n.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; rw [Nat.mod_eq_of_lt]; omega
    rw [hn]
    obtain ⟨w, hw⟩ : ∃ w, x.toNat = 2 * w := ⟨x.toNat / 2, by omega⟩
    have hw1 : w % 2 = 1 := by simp at hne; omega
    have hx0 : x0 = w * 2 ^ (n.toNat + 1) := by rw [e, hw, pow_succ]; ring
    refine ⟨by omega, ?_, ?_⟩
    · rw [hx0]; exact Nat.mul_mod_left _ _
    · rw [hx0, Nat.mul_div_cancel _ (by positivity)]; exact hw1
  · simp only [hz]
    simp only [Bool.false_eq_true, if_false]
    have hz' : x.toNat % 2 = 1 := by
      have : x.toNat % 2 ≠ 0 := by
        intro hc; apply hz
        have : x &&& 1 = 0 := by
          apply UInt64.toNat_inj.mp; rw [hand, hc]; rfl
        simp [this]
      omega
    refine ⟨by omega, ?_, ?_⟩
    · rw [e]; exact Nat.mul_mod_left _ _
    · rw [e, Nat.mul_div_cancel _ (by positivity)]; exact hz'

theorem ctz_spec (x : UInt64) (hx : x ≠ 0) :
    (ctz x).toNat ≤ 63 ∧ x.toNat % 2 ^ (ctz x).toNat = 0 ∧
      (x.toNat / 2 ^ (ctz x).toNat) % 2 = 1 := by
  rw [ctz_eq]
  have h0 : CInv x.toNat x 0 64 := by
    refine ⟨by simp, ?_, by simp⟩
    have : x.toNat ≠ 0 := fun h => hx (UInt64.toNat_inj.mp h)
    have := x.toNat_lt
    rw [Nat.mod_eq_of_lt (by simpa using this)]; assumption
  have h1 := cx_inv 32 0xFFFFFFFF 32 (by decide) (by decide) (by decide) h0
  have h2 := cx_inv 16 0xFFFF 16 (by decide) (by decide) (by decide) h1
  have h3 := cx_inv 8 0xFF 8 (by decide) (by decide) (by decide) h2
  have h4 := cx_inv 4 0xF 4 (by decide) (by decide) (by decide) h3
  have h5 := cx_inv 2 0x3 2 (by decide) (by decide) (by decide) h4
  exact cfin_spec h5


/-! ## `tz`, `shr`, `shl` -/

theorem toNat_sub64 {t : UInt64} (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    (64 - t).toNat = 64 - t.toNat := by
  rw [UInt64.toNat_sub]
  have h64 : (64 : UInt64).toNat = 64 := rfl
  have ht := t.toNat_lt
  rw [h64]
  omega

/-- A right shift joined with a left shift of the next word. -/
theorem word_shr (x y t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    ((x >>> t) ||| (y <<< (64 - t))).toNat =
      x.toNat / 2 ^ t.toNat + (y.toNat % 2 ^ t.toNat) * 2 ^ (64 - t.toNat) := by
  have hs := toNat_sub64 h1 h2
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hs,
    Nat.mod_eq_of_lt (by omega : t.toNat < 64), Nat.mod_eq_of_lt (by omega : 64 - t.toNat < 64),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h64 : (2 : Nat) ^ 64 = 2 ^ t.toNat * 2 ^ (64 - t.toNat) := by
    rw [← pow_add]; congr 1; omega
  have hm : (y.toNat * 2 ^ (64 - t.toNat)) % 2 ^ 64 = (y.toNat % 2 ^ t.toNat) * 2 ^ (64 - t.toNat) := by
    rw [h64, Nat.mul_mod_mul_right]
  have hlt : x.toNat / 2 ^ t.toNat < 2 ^ (64 - t.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have := x.toNat_lt
    rw [mul_comm, ← h64]; exact this
  rw [hm, Nat.or_comm]
  have := Nat.shiftLeft_add_eq_or_of_lt hlt (y.toNat % 2 ^ t.toNat)
  rw [Nat.shiftLeft_eq] at this
  rw [← this]; ring

theorem word_shr_top (x t : UInt64) (h2 : t.toNat ≤ 63) :
    (x >>> t).toNat = x.toNat / 2 ^ t.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega : t.toNat < 64), Nat.shiftRight_eq_div_pow]

/-- A left shift joined with the high part of the previous word. -/
theorem word_shl (x y t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    ((y <<< t) ||| (x >>> (64 - t))).toNat =
      (y.toNat % 2 ^ (64 - t.toNat)) * 2 ^ t.toNat + x.toNat / 2 ^ (64 - t.toNat) := by
  have hs := toNat_sub64 h1 h2
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hs,
    Nat.mod_eq_of_lt (by omega : t.toNat < 64), Nat.mod_eq_of_lt (by omega : 64 - t.toNat < 64),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h64 : (2 : Nat) ^ 64 = 2 ^ (64 - t.toNat) * 2 ^ t.toNat := by
    rw [← pow_add]; congr 1; omega
  have hm : (y.toNat * 2 ^ t.toNat) % 2 ^ 64 = (y.toNat % 2 ^ (64 - t.toNat)) * 2 ^ t.toNat := by
    rw [h64, Nat.mul_mod_mul_right]
  have hlt : x.toNat / 2 ^ (64 - t.toNat) < 2 ^ t.toNat := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have := x.toNat_lt
    rw [mul_comm, ← h64]; exact this
  rw [hm]
  have := Nat.shiftLeft_add_eq_or_of_lt hlt (y.toNat % 2 ^ (64 - t.toNat))
  rw [Nat.shiftLeft_eq] at this
  rw [← this]

theorem word_shl_low (y t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    (y <<< t).toNat = (y.toNat % 2 ^ (64 - t.toNat)) * 2 ^ t.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega : t.toNat < 64), Nat.shiftLeft_eq]
  have h64 : (2 : Nat) ^ 64 = 2 ^ (64 - t.toNat) * 2 ^ t.toNat := by
    rw [← pow_add]; congr 1; omega
  rw [h64, Nat.mul_mod_mul_right]

theorem shr_arith (K T T' q0 q1 q2 q3 q4 q5 m0 m1 m2 m3 m4 m5 : Nat) (hK : K = T * T') :
    ((q0 + m1 * T') + K * ((q1 + m2 * T') + K * ((q2 + m3 * T') + K * ((q3 + m4 * T') +
      K * ((q4 + m5 * T') + K * q5))))) * T + m0 =
    (q0 * T + m0) + K * ((q1 * T + m1) + K * ((q2 * T + m2) + K * ((q3 * T + m3) +
      K * ((q4 * T + m4) + K * (q5 * T + m5))))) := by
  subst hK; ring

/-- `shr a t`, times `2^t`, plus the dropped low bits, is `a`. -/
theorem shr_spec (a : Fp) (t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    (shr a t).raw * 2 ^ t.toNat + a.l0.toNat % 2 ^ t.toNat = a.raw := by
  have e0 := word_shr a.l0 a.l1 t h1 h2
  have e1 := word_shr a.l1 a.l2 t h1 h2
  have e2 := word_shr a.l2 a.l3 t h1 h2
  have e3 := word_shr a.l3 a.l4 t h1 h2
  have e4 := word_shr a.l4 a.l5 t h1 h2
  have e5 := word_shr_top a.l5 t h2
  have h64 : (2 : Nat) ^ 64 = 2 ^ t.toNat * 2 ^ (64 - t.toNat) := by
    rw [← pow_add]; congr 1; omega
  have key := shr_arith (2 ^ 64) (2 ^ t.toNat) (2 ^ (64 - t.toNat))
    (a.l0.toNat / 2 ^ t.toNat) (a.l1.toNat / 2 ^ t.toNat) (a.l2.toNat / 2 ^ t.toNat)
    (a.l3.toNat / 2 ^ t.toNat) (a.l4.toNat / 2 ^ t.toNat) (a.l5.toNat / 2 ^ t.toNat)
    (a.l0.toNat % 2 ^ t.toNat) (a.l1.toNat % 2 ^ t.toNat) (a.l2.toNat % 2 ^ t.toNat)
    (a.l3.toNat % 2 ^ t.toNat) (a.l4.toNat % 2 ^ t.toNat) (a.l5.toNat % 2 ^ t.toNat) h64
  have d0 := Nat.div_add_mod' a.l0.toNat (2 ^ t.toNat)
  have d1 := Nat.div_add_mod' a.l1.toNat (2 ^ t.toNat)
  have d2 := Nat.div_add_mod' a.l2.toNat (2 ^ t.toNat)
  have d3 := Nat.div_add_mod' a.l3.toNat (2 ^ t.toNat)
  have d4 := Nat.div_add_mod' a.l4.toNat (2 ^ t.toNat)
  have d5 := Nat.div_add_mod' a.l5.toNat (2 ^ t.toNat)
  rw [d0, d1, d2, d3, d4, d5] at key
  simp only [shr, raw, e0, e1, e2, e3, e4, e5]
  exact key

theorem shl_arith (K T T' h0 h1 h2 h3 h4 h5 l0 l1 l2 l3 l4 l5 : Nat) (hK : K = T * T') :
    (l0 * T + K * ((l1 * T + h0) + K * ((l2 * T + h1) + K * ((l3 * T + h2) +
      K * ((l4 * T + h3) + K * (l5 * T + h4)))))) + K ^ 6 * h5 =
    ((h0 * T' + l0) + K * ((h1 * T' + l1) + K * ((h2 * T' + l2) + K * ((h3 * T' + l3) +
      K * ((h4 * T' + l4) + K * (h5 * T' + l5)))))) * T := by
  subst hK; ring

/-- `shl a t` is `a · 2^t` modulo `2^384`; the dropped top bits are `a.l5 / 2^(64 - t)`. -/
theorem shl_spec (a : Fp) (t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63) :
    (shl a t).raw + 2 ^ 384 * (a.l5.toNat / 2 ^ (64 - t.toNat)) = a.raw * 2 ^ t.toNat := by
  have e0 := word_shl_low a.l0 t h1 h2
  have e1 := word_shl a.l0 a.l1 t h1 h2
  have e2 := word_shl a.l1 a.l2 t h1 h2
  have e3 := word_shl a.l2 a.l3 t h1 h2
  have e4 := word_shl a.l3 a.l4 t h1 h2
  have e5 := word_shl a.l4 a.l5 t h1 h2
  have h64 : (2 : Nat) ^ 64 = 2 ^ t.toNat * 2 ^ (64 - t.toNat) := by
    rw [← pow_add]; congr 1; omega
  have key := shl_arith (2 ^ 64) (2 ^ t.toNat) (2 ^ (64 - t.toNat))
    (a.l0.toNat / 2 ^ (64 - t.toNat)) (a.l1.toNat / 2 ^ (64 - t.toNat))
    (a.l2.toNat / 2 ^ (64 - t.toNat)) (a.l3.toNat / 2 ^ (64 - t.toNat))
    (a.l4.toNat / 2 ^ (64 - t.toNat)) (a.l5.toNat / 2 ^ (64 - t.toNat))
    (a.l0.toNat % 2 ^ (64 - t.toNat)) (a.l1.toNat % 2 ^ (64 - t.toNat))
    (a.l2.toNat % 2 ^ (64 - t.toNat)) (a.l3.toNat % 2 ^ (64 - t.toNat))
    (a.l4.toNat % 2 ^ (64 - t.toNat)) (a.l5.toNat % 2 ^ (64 - t.toNat))
    (by rw [h64, mul_comm])
  have d0 := Nat.div_add_mod' a.l0.toNat (2 ^ (64 - t.toNat))
  have d1 := Nat.div_add_mod' a.l1.toNat (2 ^ (64 - t.toNat))
  have d2 := Nat.div_add_mod' a.l2.toNat (2 ^ (64 - t.toNat))
  have d3 := Nat.div_add_mod' a.l3.toNat (2 ^ (64 - t.toNat))
  have d4 := Nat.div_add_mod' a.l4.toNat (2 ^ (64 - t.toNat))
  have d5 := Nat.div_add_mod' a.l5.toNat (2 ^ (64 - t.toNat))
  have h384 : ((2 : Nat) ^ 64) ^ 6 = 2 ^ 384 := by rw [← pow_mul]
  rw [h384] at key
  rw [d0, d1, d2, d3, d4, d5] at key
  simp only [shl, raw, e0, e1, e2, e3, e4, e5]
  exact key

/-! ## The loop invariant -/

/-- The loop invariant, on the integers the word vectors spell. -/
def GI (P A U V R S K : ℕ) : Prop :=
  P = U * S + V * R ∧ ((A : ZMod P) * R + U * 2 ^ K = 0) ∧ ((A : ZMod P) * S = V * 2 ^ K) ∧
    1 ≤ U ∧ U ≤ P ∧ 1 ≤ V ∧ V < P ∧ U * V * 2 ^ K ≤ P * A

theorem gi_u_even {P A U V R S K U' S' T t : ℕ} (h : GI P A U V R S K) (hT : T = 2 ^ t)
    (hU : U = U' * T) (hS : S' = S * T) : GI P A U' V R S' (K + t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  subst hT hS
  have hU' : 1 ≤ U' := by
    rcases Nat.eq_zero_or_pos U' with h0 | h0
    · subst h0; simp at hU; omega
    · exact h0
  have hT1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hUU : U' ≤ U := by rw [hU]; exact Nat.le_mul_of_pos_right _ hT1
  subst hU
  refine ⟨?_, ?_, ?_, hU', by omega, h6, h7, ?_⟩
  · rw [h1]; ring
  · rw [pow_add]; push_cast at h2 ⊢; linear_combination h2
  · rw [pow_add]; push_cast at h3 ⊢; linear_combination 2 ^ t * h3
  · rw [pow_add]; calc U' * V * (2 ^ K * 2 ^ t) = U' * 2 ^ t * V * 2 ^ K := by ring
      _ ≤ _ := h8

theorem gi_v_even {P A U V R S K V' R' T t : ℕ} (h : GI P A U V R S K) (hT : T = 2 ^ t)
    (hV : V = V' * T) (hR : R' = R * T) : GI P A U V' R' S (K + t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  subst hT hR
  have hV' : 1 ≤ V' := by
    rcases Nat.eq_zero_or_pos V' with h0 | h0
    · subst h0; simp at hV; omega
    · exact h0
  have hT1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hVV : V' ≤ V := by rw [hV]; exact Nat.le_mul_of_pos_right _ hT1
  subst hV
  refine ⟨?_, ?_, ?_, h4, h5, hV', by omega, ?_⟩
  · rw [h1]; ring
  · rw [pow_add]; push_cast at h2 ⊢; linear_combination 2 ^ t * h2
  · rw [pow_add]; push_cast at h3 ⊢; linear_combination h3
  · rw [pow_add]; calc U * V' * (2 ^ K * 2 ^ t) = U * (V' * 2 ^ t) * 2 ^ K := by ring
      _ ≤ _ := h8

theorem gi_u_sub {P A U V R S K U' R' S' d T t : ℕ} (h : GI P A U V R S K) (hT : T = 2 ^ t)
    (hd : U = d + V) (hd0 : 0 < d) (hU : d = U' * T) (hR : R' = R + S) (hS : S' = S * T) :
    GI P A U' V R' S' (K + t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  subst hT hR hS
  have hU' : 1 ≤ U' := by
    rcases Nat.eq_zero_or_pos U' with h0 | h0
    · subst h0; simp at hU; omega
    · exact h0
  have hT1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hUU : U' ≤ d := by rw [hU]; exact Nat.le_mul_of_pos_right _ hT1
  refine ⟨?_, ?_, ?_, hU', by omega, h6, h7, ?_⟩
  · rw [h1, hd, hU]; ring
  · rw [pow_add]; push_cast at h2 ⊢
    have hd' : (U : ZMod P) = d + V := by rw [hd]; push_cast; ring
    have hU2 : (d : ZMod P) = U' * 2 ^ t := by rw [hU]; push_cast; ring
    linear_combination h2 + h3 - 2 ^ K * hd' - 2 ^ K * hU2
  · rw [pow_add]; push_cast at h3 ⊢; linear_combination 2 ^ t * h3
  · rw [pow_add]
    calc U' * V * (2 ^ K * 2 ^ t) = (U' * 2 ^ t) * V * 2 ^ K := by ring
      _ = d * V * 2 ^ K := by rw [← hU]
      _ ≤ U * V * 2 ^ K := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
      _ ≤ _ := h8

theorem gi_v_sub {P A U V R S K V' R' S' d T t : ℕ} (h : GI P A U V R S K) (hT : T = 2 ^ t)
    (hd : V = d + U) (hd0 : 0 < d) (hV : d = V' * T) (hR : R' = R * T) (hS : S' = R + S) :
    GI P A U V' R' S' (K + t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  subst hT hR hS
  have hV' : 1 ≤ V' := by
    rcases Nat.eq_zero_or_pos V' with h0 | h0
    · subst h0; simp at hV; omega
    · exact h0
  have hT1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hVV : V' ≤ d := by rw [hV]; exact Nat.le_mul_of_pos_right _ hT1
  refine ⟨?_, ?_, ?_, h4, h5, hV', by omega, ?_⟩
  · rw [h1, hd, hV]; ring
  · rw [pow_add]; push_cast at h2 ⊢; linear_combination 2 ^ t * h2
  · rw [pow_add]; push_cast at h3 h2 ⊢
    have hd' : (V : ZMod P) = d + U := by rw [hd]; push_cast; ring
    have hV2 : (d : ZMod P) = V' * 2 ^ t := by rw [hV]; push_cast; ring
    linear_combination h2 + h3 + 2 ^ K * hd' + 2 ^ K * hV2
  · rw [pow_add]
    calc U * V' * (2 ^ K * 2 ^ t) = U * (V' * 2 ^ t) * 2 ^ K := by ring
      _ = U * d * 2 ^ K := by rw [← hV]
      _ ≤ U * V * 2 ^ K := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
      _ ≤ _ := h8


theorem gi_init {P A : ℕ} (hA0 : 1 ≤ A) (hA : A < P) (hP : 1 < P) : GI P A P A 0 1 0 := by
  refine ⟨by ring, by simp, by simp, by omega, le_refl _, hA0, hA, by simp⟩

theorem gi_k {P A U V R S K : ℕ} (h : GI P A U V R S K) (hA : A < P) (hP : P < 2 ^ 381) :
    K < 762 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have h9 : 2 ^ K ≤ P * A := by
    calc 2 ^ K = 1 * 1 * 2 ^ K := by ring
      _ ≤ U * V * 2 ^ K := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul h4 h6
      _ ≤ _ := h8
  have h10 : P * A < 2 ^ 762 := by
    calc P * A < 2 ^ 381 * 2 ^ 381 := Nat.mul_lt_mul'' hP (by omega)
      _ = 2 ^ 762 := by rw [← pow_add]
  have : 2 ^ K < 2 ^ 762 := lt_of_le_of_lt h9 h10
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

theorem gi_add_le {P A U V R S K : ℕ} (h : GI P A U V R S K) : R + S ≤ P ∧ S ≤ P ∧ R ≤ P := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have a : S ≤ U * S := Nat.le_mul_of_pos_left _ h4
  have b : R ≤ V * R := Nat.le_mul_of_pos_left _ h6
  omega

theorem gi_stop {P A U V R S K : ℕ} [Fact P.Prime] (h : GI P A U V R S K) (huv : U = V)
    (h2ne : (2 : ZMod P) ≠ 0) :
    U = 1 ∧ S < P ∧ (A : ZMod P) * S = 2 ^ K := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  subst huv
  have hd : U ∣ P := ⟨S + R, by rw [h1]; ring⟩
  have hp := (Fact.out : P.Prime)
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · subst h
    refine ⟨rfl, ?_, by simpa using h3⟩
    rcases Nat.lt_or_ge S P with h | h
    · exact h
    · exfalso
      have hS : S = P := le_antisymm (by omega) h
      have hR : R = 0 := by omega
      subst hR
      have : ((2 : ZMod P)) ^ K = 0 := by simpa using h2
      exact pow_ne_zero K h2ne this
  · omega


/-! ## Branch lemmas on word vectors -/

theorem raw_mod_two (a : Fp) : a.raw % 2 = a.l0.toNat % 2 := by
  simp only [raw]; omega

theorem and_one_beq (x : UInt64) : ((x &&& 1) == 0) = true ↔ x.toNat % 2 = 0 := by
  have hand : (x &&& 1).toNat = x.toNat % 2 := by
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 1
    rw [UInt64.toNat_and]; simp at this ⊢
  constructor
  · intro h
    have : x &&& 1 = 0 := by simpa using h
    rw [← hand, this]; rfl
  · intro h
    have : x &&& 1 = 0 := by
      apply UInt64.toNat_inj.mp; rw [hand, h]; rfl
    simp [this]

theorem tz_spec (d : Fp) (he : d.l0.toNat % 2 = 0) :
    1 ≤ (tz d).toNat ∧ (tz d).toNat ≤ 63 ∧ d.l0.toNat % 2 ^ (tz d).toNat = 0 := by
  unfold tz
  by_cases h : (d.l0 == 0) = true
  · have h0 : d.l0 = 0 := by simpa using h
    rw [if_pos h]
    refine ⟨by decide, by decide, ?_⟩
    rw [h0]; rfl
  · rw [if_neg h]
    have hne : d.l0 ≠ 0 := by simpa using h
    obtain ⟨c1, c2, c3⟩ := ctz_spec d.l0 hne
    refine ⟨?_, c1, c2⟩
    by_contra hc
    have : (ctz d.l0).toNat = 0 := by omega
    rw [this] at c3
    simp at c3
    omega

/-- `shr` by `tz` is exact. -/
theorem shr_tz (d : Fp) (he : d.l0.toNat % 2 = 0) :
    (shr d (tz d)).raw * 2 ^ (tz d).toNat = d.raw := by
  obtain ⟨h1, h2, h3⟩ := tz_spec d he
  have := shr_spec d (tz d) h1 h2
  omega

theorem sub6_eq (a b : Fp) : sub6 a b = sbb6 a b := rfl

theorem add6_raw {a b : Fp} (h : a.raw + b.raw < 2 ^ 384) : (add6 a b).raw = a.raw + b.raw :=
  addRaw_raw h

/-- Shifting a vector left by `t` is exact when the result is bounded by `p`. -/
theorem shl_exact (a : Fp) (t : UInt64) (h1 : 1 ≤ t.toNat) (h2 : t.toNat ≤ 63)
    (h : a.raw * 2 ^ t.toNat < 2 ^ 384) : (shl a t).raw = a.raw * 2 ^ t.toNat := by
  have := shl_spec a t h1 h2
  have h5 : a.l5.toNat / 2 ^ (64 - t.toNat) = 0 := by
    by_contra hc
    have : 1 ≤ a.l5.toNat / 2 ^ (64 - t.toNat) := by omega
    have : 2 ^ 384 * 1 ≤ 2 ^ 384 * (a.l5.toNat / 2 ^ (64 - t.toNat)) := Nat.mul_le_mul_left _ this
    omega
  rw [h5] at this
  omega

theorem no_wrap {P A U V R S K t : ℕ} (hA : A < P) (hP : P < 2 ^ 381)
    {k t' : UInt64} (hk : k.toNat = K) (ht : t'.toNat = t) (h' : GI P A U V R S (K + t)) :
    (k + t').toNat = K + t := by
  have := gi_k h' hA hP
  rw [UInt64.toNat_add, hk, ht, Nat.mod_eq_of_lt]
  omega

theorem mod_lt' : modulus < 2 ^ 381 := modulus_lt_381

/-- Halving `u`. -/
theorem step_u_even {A : ℕ} (hA : A < modulus) (u v r s : Fp) (k : UInt64)
    (hI : GI modulus A u.raw v.raw r.raw s.raw k.toNat) (he : u.l0.toNat % 2 = 0) :
    1 ≤ (tz u).toNat ∧ (k + tz u).toNat = k.toNat + (tz u).toNat ∧
      GI modulus A (shr u (tz u)).raw v.raw r.raw (shl s (tz u)).raw (k.toNat + (tz u).toNat) := by
  obtain ⟨t1, t2, -⟩ := tz_spec u he
  have hU := shr_tz u he
  have hI' := hI
  obtain ⟨h1, -, -, h4, -, h6, -, -⟩ := hI
  have hU' : 1 ≤ (shr u (tz u)).raw := by
    rcases Nat.eq_zero_or_pos (shr u (tz u)).raw with h0 | h0
    · rw [h0] at hU; omega
    · exact h0
  have hS : s.raw * 2 ^ (tz u).toNat < 2 ^ 384 := by
    have a1 : s.raw * 2 ^ (tz u).toNat ≤ (shr u (tz u)).raw * (s.raw * 2 ^ (tz u).toNat) :=
      Nat.le_mul_of_pos_left _ hU'
    have a2 : (shr u (tz u)).raw * (s.raw * 2 ^ (tz u).toNat) = u.raw * s.raw := by
      rw [← hU]; ring
    have := modulus_lt
    omega
  have hSe := shl_exact s (tz u) t1 t2 hS
  have hG := gi_u_even hI' (T := 2 ^ (tz u).toNat) rfl hU.symm hSe
  exact ⟨t1, no_wrap hA mod_lt' rfl rfl hG, hG⟩

/-- Halving `v`. -/
theorem step_v_even {A : ℕ} (hA : A < modulus) (u v r s : Fp) (k : UInt64)
    (hI : GI modulus A u.raw v.raw r.raw s.raw k.toNat) (he : v.l0.toNat % 2 = 0) :
    1 ≤ (tz v).toNat ∧ (k + tz v).toNat = k.toNat + (tz v).toNat ∧
      GI modulus A u.raw (shr v (tz v)).raw (shl r (tz v)).raw s.raw (k.toNat + (tz v).toNat) := by
  obtain ⟨t1, t2, -⟩ := tz_spec v he
  have hV := shr_tz v he
  have hI' := hI
  obtain ⟨h1, -, -, h4, -, h6, -, -⟩ := hI
  have hV' : 1 ≤ (shr v (tz v)).raw := by
    rcases Nat.eq_zero_or_pos (shr v (tz v)).raw with h0 | h0
    · rw [h0] at hV; omega
    · exact h0
  have hR : r.raw * 2 ^ (tz v).toNat < 2 ^ 384 := by
    have a1 : r.raw * 2 ^ (tz v).toNat ≤ (shr v (tz v)).raw * (r.raw * 2 ^ (tz v).toNat) :=
      Nat.le_mul_of_pos_left _ hV'
    have a2 : (shr v (tz v)).raw * (r.raw * 2 ^ (tz v).toNat) = v.raw * r.raw := by
      rw [← hV]; ring
    have := modulus_lt
    omega
  have hRe := shl_exact r (tz v) t1 t2 hR
  have hG := gi_v_even hI' (T := 2 ^ (tz v).toNat) rfl hV.symm hRe
  exact ⟨t1, no_wrap hA mod_lt' rfl rfl hG, hG⟩

/-- `u > v`, both odd. -/
theorem step_u_sub {A : ℕ} (hA : A < modulus) (u v r s : Fp) (k : UInt64)
    (hI : GI modulus A u.raw v.raw r.raw s.raw k.toNat)
    (hu : u.l0.toNat % 2 = 1) (hv : v.l0.toNat % 2 = 1)
    (hb : (sub6 u v).2 = 0) (hd : (sub6 u v).1.raw ≠ 0) :
    1 ≤ (tz (sub6 u v).1).toNat ∧ (k + tz (sub6 u v).1).toNat = k.toNat + (tz (sub6 u v).1).toNat ∧
      GI modulus A (shr (sub6 u v).1 (tz (sub6 u v).1)).raw v.raw (add6 r s).raw
        (shl s (tz (sub6 u v).1)).raw (k.toNat + (tz (sub6 u v).1).toNat) := by
  have hs := sbb6_spec u v
  rw [sub6_eq] at hb hd ⊢
  set d := (sbb6 u v).1 with hdd
  rw [hb] at hs
  simp only [UInt64.toNat_zero, mul_zero, add_zero] at hs
  have hev : d.l0.toNat % 2 = 0 := by
    have := raw_mod_two d; have := raw_mod_two u; have := raw_mod_two v; omega
  obtain ⟨t1, t2, -⟩ := tz_spec d hev
  have hD := shr_tz d hev
  have hI' := hI
  have hadd := gi_add_le hI
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := hI
  have hD0 : 1 ≤ (shr d (tz d)).raw := by
    rcases Nat.eq_zero_or_pos (shr d (tz d)).raw with h0 | h0
    · rw [h0] at hD; omega
    · exact h0
  have hlt := modulus_lt
  have hS : s.raw * 2 ^ (tz d).toNat < 2 ^ 384 := by
    have a1 : s.raw * 2 ^ (tz d).toNat ≤ (shr d (tz d)).raw * (s.raw * 2 ^ (tz d).toNat) :=
      Nat.le_mul_of_pos_left _ hD0
    have a2 : (shr d (tz d)).raw * (s.raw * 2 ^ (tz d).toNat) = d.raw * s.raw := by
      rw [← hD]; ring
    have a3 : d.raw * s.raw ≤ u.raw * s.raw := Nat.mul_le_mul_right _ (by omega)
    omega
  have hSe := shl_exact s (tz d) t1 t2 hS
  have hRe := add6_raw (a := r) (b := s) (by omega)
  have hG := gi_u_sub hI' (T := 2 ^ (tz d).toNat) rfl (d := d.raw) (by omega) (by omega) hD.symm
    hRe hSe
  exact ⟨t1, no_wrap hA mod_lt' rfl rfl hG, hG⟩

/-- `u < v`, both odd. -/
theorem step_v_sub {A : ℕ} (hA : A < modulus) (u v r s : Fp) (k : UInt64)
    (hI : GI modulus A u.raw v.raw r.raw s.raw k.toNat)
    (hu : u.l0.toNat % 2 = 1) (hv : v.l0.toNat % 2 = 1)
    (hb : (sub6 u v).2 ≠ 0) :
    1 ≤ (tz (sub6 v u).1).toNat ∧ (k + tz (sub6 v u).1).toNat = k.toNat + (tz (sub6 v u).1).toNat ∧
      GI modulus A u.raw (shr (sub6 v u).1 (tz (sub6 v u).1)).raw (shl r (tz (sub6 v u).1)).raw
        (add6 r s).raw (k.toNat + (tz (sub6 v u).1).toNat) := by
  have hs1 := sbb6_spec u v
  have hs := sbb6_spec v u
  rw [sub6_eq] at hb ⊢
  have hb1 : (sbb6 u v).2.toNat = 1 := by
    have : (sbb6 u v).2.toNat ≠ 0 := fun h => hb (UInt64.toNat_inj.mp h)
    omega
  rw [hb1] at hs1
  have hUV : u.raw < v.raw := by
    have := raw_lt (sbb6 u v).1
    omega
  have hbz : (sbb6 v u).2.toNat = 0 := by
    have := raw_lt (sbb6 v u).1
    have := raw_lt u; have := raw_lt v
    omega
  set d := (sbb6 v u).1 with hdd
  rw [hbz] at hs
  simp only [mul_zero, add_zero] at hs
  have hev : d.l0.toNat % 2 = 0 := by
    have := raw_mod_two d; have := raw_mod_two u; have := raw_mod_two v; omega
  obtain ⟨t1, t2, -⟩ := tz_spec d hev
  have hD := shr_tz d hev
  have hI' := hI
  have hadd := gi_add_le hI
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := hI
  have hD0 : 1 ≤ (shr d (tz d)).raw := by
    rcases Nat.eq_zero_or_pos (shr d (tz d)).raw with h0 | h0
    · rw [h0] at hD
      have : d.raw = 0 := by omega
      have := raw_lt u
      omega
    · exact h0
  have hlt := modulus_lt
  have hR : r.raw * 2 ^ (tz d).toNat < 2 ^ 384 := by
    have a1 : r.raw * 2 ^ (tz d).toNat ≤ (shr d (tz d)).raw * (r.raw * 2 ^ (tz d).toNat) :=
      Nat.le_mul_of_pos_left _ hD0
    have a2 : (shr d (tz d)).raw * (r.raw * 2 ^ (tz d).toNat) = d.raw * r.raw := by
      rw [← hD]; ring
    have a3 : d.raw * r.raw ≤ v.raw * r.raw := Nat.mul_le_mul_right _ (by omega)
    omega
  have hRe := shl_exact r (tz d) t1 t2 hR
  have hSe := add6_raw (a := r) (b := s) (by omega)
  have hG := gi_v_sub hI' (T := 2 ^ (tz d).toNat) rfl (d := d.raw) (by omega) (by omega) hD.symm
    hRe hSe
  exact ⟨t1, no_wrap hA mod_lt' rfl rfl hG, hG⟩

/-! ## The loop -/

theorem two_ne_zero_modulus : (2 : ZMod modulus) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod modulus) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have h3 : ¬ modulus ≤ 2 := by unfold modulus; decide
  exact h3 this

theorem odd_of_not_even {x : UInt64} (h : ¬ ((x &&& 1) == 0) = true) : x.toNat % 2 = 1 := by
  rw [and_one_beq] at h; omega

/-- The loop ends at the stop with `A · s ≡ 2^k`, `s < p`, `k < 762`. -/
theorem go_spec {A : ℕ} (hA : A < modulus) : ∀ (fuel : ℕ) (u v r s : Fp) (k : UInt64),
    GI modulus A u.raw v.raw r.raw s.raw k.toNat → 762 ≤ k.toNat + fuel →
    (go fuel u.l0 u.l1 u.l2 u.l3 u.l4 u.l5 v.l0 v.l1 v.l2 v.l3 v.l4 v.l5
      r.l0 r.l1 r.l2 r.l3 r.l4 r.l5 s.l0 s.l1 s.l2 s.l3 s.l4 s.l5 k).1.raw < modulus ∧
    ((A : ZMod modulus) * (go fuel u.l0 u.l1 u.l2 u.l3 u.l4 u.l5 v.l0 v.l1 v.l2 v.l3 v.l4 v.l5
      r.l0 r.l1 r.l2 r.l3 r.l4 r.l5 s.l0 s.l1 s.l2 s.l3 s.l4 s.l5 k).1.raw =
      2 ^ (go fuel u.l0 u.l1 u.l2 u.l3 u.l4 u.l5 v.l0 v.l1 v.l2 v.l3 v.l4 v.l5
      r.l0 r.l1 r.l2 r.l3 r.l4 r.l5 s.l0 s.l1 s.l2 s.l3 s.l4 s.l5 k).2.toNat) ∧
    (go fuel u.l0 u.l1 u.l2 u.l3 u.l4 u.l5 v.l0 v.l1 v.l2 v.l3 v.l4 v.l5
      r.l0 r.l1 r.l2 r.l3 r.l4 r.l5 s.l0 s.l1 s.l2 s.l3 s.l4 s.l5 k).2.toNat < 762 := by
  haveI : Fact (Nat.Prime modulus) := ⟨by rw [modulus_eq]; exact EthLib.Cryptography.Bls.Fp.modulus_prime⟩
  intro fuel
  induction fuel with
  | zero =>
    intro u v r s k hI hf
    have := gi_k hI hA mod_lt'
    omega
  | succ fuel ih =>
    intro u v r s k hI hf
    have hI0 := hI
    obtain ⟨u0, u1, u2, u3, u4, u5⟩ := u
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := v
    obtain ⟨r0, r1, r2, r3, r4, r5⟩ := r
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := s
    simp only [go]
    by_cases hu : ((u0 &&& 1) == 0) = true
    · rw [if_pos hu]
      have he := (and_one_beq u0).mp hu
      obtain ⟨h1, h2, h3⟩ := step_u_even hA ⟨u0, u1, u2, u3, u4, u5⟩ ⟨v0, v1, v2, v3, v4, v5⟩
        ⟨r0, r1, r2, r3, r4, r5⟩ ⟨s0, s1, s2, s3, s4, s5⟩ k hI he
      have := ih (shr ⟨u0, u1, u2, u3, u4, u5⟩ (tz ⟨u0, u1, u2, u3, u4, u5⟩))
        ⟨v0, v1, v2, v3, v4, v5⟩ ⟨r0, r1, r2, r3, r4, r5⟩
        (shl ⟨s0, s1, s2, s3, s4, s5⟩ (tz ⟨u0, u1, u2, u3, u4, u5⟩))
        (k + tz ⟨u0, u1, u2, u3, u4, u5⟩) (by rw [h2]; exact h3) (by rw [h2]; omega)
      exact this
    · rw [if_neg hu]
      have hu1 := odd_of_not_even hu
      by_cases hv : ((v0 &&& 1) == 0) = true
      · rw [if_pos hv]
        have he := (and_one_beq v0).mp hv
        obtain ⟨h1, h2, h3⟩ := step_v_even hA ⟨u0, u1, u2, u3, u4, u5⟩ ⟨v0, v1, v2, v3, v4, v5⟩
          ⟨r0, r1, r2, r3, r4, r5⟩ ⟨s0, s1, s2, s3, s4, s5⟩ k hI he
        have := ih ⟨u0, u1, u2, u3, u4, u5⟩
          (shr ⟨v0, v1, v2, v3, v4, v5⟩ (tz ⟨v0, v1, v2, v3, v4, v5⟩))
          (shl ⟨r0, r1, r2, r3, r4, r5⟩ (tz ⟨v0, v1, v2, v3, v4, v5⟩))
          ⟨s0, s1, s2, s3, s4, s5⟩
          (k + tz ⟨v0, v1, v2, v3, v4, v5⟩) (by rw [h2]; exact h3) (by rw [h2]; omega)
        exact this
      · rw [if_neg hv]
        have hv1 := odd_of_not_even hv
        set u : Fp := ⟨u0, u1, u2, u3, u4, u5⟩ with hu_def
        set v : Fp := ⟨v0, v1, v2, v3, v4, v5⟩ with hv_def
        set r : Fp := ⟨r0, r1, r2, r3, r4, r5⟩ with hr_def
        set s : Fp := ⟨s0, s1, s2, s3, s4, s5⟩ with hs_def
        have hu1' : u.l0.toNat % 2 = 1 := hu1
        have hv1' : v.l0.toNat % 2 = 1 := hv1
        by_cases hbr : (sub6 u v).2 = 0
        · rw [if_pos (by simp [hbr])]
          by_cases hd : ((sub6 u v).1.l0 ||| (sub6 u v).1.l1 ||| (sub6 u v).1.l2 |||
              (sub6 u v).1.l3 ||| (sub6 u v).1.l4 ||| (sub6 u v).1.l5 == 0) = true
          · rw [if_pos hd]
            have hz : (sub6 u v).1.raw = 0 := by
              rw [← or_words_eq_zero]; simpa using hd
            have hs := sbb6_spec u v
            rw [← sub6_eq] at hs
            have hb0 : (sub6 u v).2.toNat = 0 := by rw [hbr]; rfl
            rw [hb0, hz] at hs
            have huv : u.raw = v.raw := by omega
            obtain ⟨-, hs1, hs2⟩ := gi_stop hI0 huv two_ne_zero_modulus
            exact ⟨hs1, hs2, gi_k hI0 hA mod_lt'⟩
          · rw [if_neg hd]
            have hd' : (sub6 u v).1.raw ≠ 0 := by
              intro h0; apply hd
              have := (or_words_eq_zero (sub6 u v).1).mpr h0
              simp [this]
            obtain ⟨h1, h2, h3⟩ := step_u_sub hA u v r s k hI0 hu1' hv1' hbr hd'
            exact ih _ _ _ _ _ (by rw [h2]; exact h3) (by rw [h2]; omega)
        · rw [if_neg (by simpa using hbr)]
          obtain ⟨h1, h2, h3⟩ := step_v_sub hA u v r s k hI0 hu1' hv1' hbr
          exact ih _ _ _ _ _ (by rw [h2]; exact h3) (by rw [h2]; omega)


/-! ## The `2^j` correction -/

theorem beq_toNat (w : UInt64) (n : UInt64) : (w == n) = true ↔ w.toNat = n.toNat := by
  rw [beq_iff_eq, UInt64.toNat_inj]

set_option exponentiation.threshold 512 in
theorem pow2_raw (J : UInt64) (hJ : J.toNat < 384) : (pow2 J).raw = 2 ^ J.toNat := by
  have hw : (J >>> 6).toNat = J.toNat / 64 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have hm : (J &&& 63).toNat = J.toNat % 64 := by
    have := Nat.and_two_pow_sub_one_eq_mod J.toNat 6
    rw [UInt64.toNat_and]; simpa using this
  have hb : (1 <<< (J &&& 63) : UInt64).toNat = 2 ^ (J.toNat % 64) := by
    rw [UInt64.toNat_shiftLeft, hm, Nat.mod_eq_of_lt (by omega : J.toNat % 64 < 64),
      Nat.shiftLeft_eq]
    simp only [UInt64.toNat_one, one_mul]
    apply Nat.mod_eq_of_lt
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold pow2
  dsimp only
  generalize (1 <<< (J &&& 63) : UInt64) = b at hb ⊢
  generalize (J >>> 6) = w at hw ⊢
  simp only [beq_toNat, hw, raw]
  have hq : J.toNat / 64 < 6 := by omega
  have hJ' : J.toNat = 64 * (J.toNat / 64) + J.toNat % 64 := by omega
  generalize J.toNat / 64 = q at hq hJ' ⊢
  generalize J.toNat % 64 = r at hJ' hb ⊢
  rw [hJ']
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 by omega) with h | h | h | h | h | h <;>
    subst h <;> simp [hb, pow_add] <;> ring


theorem toNat_toUInt64 {j : Nat} (hj : j < 2 ^ 64) : j.toUInt64.toNat = j := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hj

set_option exponentiation.threshold 512 in
theorem pow2_canonical (j : Nat) (hj : j ≤ 256) : Canonical (pow2 j.toUInt64) := by
  have hJ := toNat_toUInt64 (j := j) (by omega)
  have := pow2_raw j.toUInt64 (by omega)
  unfold Canonical
  rw [this, hJ]
  have h1 : 2 ^ j ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) hj
  have h2 : 256 ^ 32 < modulus := pow256_lt_modulus
  have h3 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  omega

set_option exponentiation.threshold 512 in
theorem toZ_pow2 (j : Nat) (hj : j ≤ 256) :
    toZMod (pow2 j.toUInt64).val = 2 ^ j * toZMod rInv := by
  have hJ := toNat_toUInt64 (j := j) (by omega)
  rw [toZ_val, pow2_raw j.toUInt64 (by omega), hJ]
  push_cast; rfl

/-- One piece of the correction: multiplies by `2^j`, for `j ≤ 256`. -/
theorem mulPow2Small_spec (x : Fp) (j : Nat) (hj : j ≤ 256) :
    Canonical (mulPow2Small x j) ∧
      toZMod (mulPow2Small x j).val = toZMod x.val * 2 ^ j := by
  have hc := pow2_canonical j hj
  unfold mulPow2Small
  refine ⟨mul_canonical _ hc, ?_⟩
  rw [val_mul _ hc, val_mul _ R2_canonical, toZMod_mul, toZMod_mul, val_R2, toZMod_ofNat,
    toZ_pow2 j hj]
  have hr := toZ_rInv
  push_cast
  generalize toZMod rInv = ri at *
  generalize toZMod x.val = X
  linear_combination (X * 2 ^ j) * hr

theorem mulPow2_spec (x : Fp) (j : Nat) (hj : j ≤ 768) :
    Canonical (mulPow2 x j) ∧ toZMod (mulPow2 x j).val = toZMod x.val * 2 ^ j := by
  unfold mulPow2
  dsimp only
  have h1 := mulPow2Small_spec x (min j 256) (by omega)
  have h2 := mulPow2Small_spec (mulPow2Small x (min j 256)) (min (j - min j 256) 256) (by omega)
  have h3 := mulPow2Small_spec (mulPow2Small (mulPow2Small x (min j 256))
    (min (j - min j 256) 256)) (j - min j 256 - min (j - min j 256) 256) (by omega)
  refine ⟨h3.1, ?_⟩
  rw [h3.2, h2.2, h1.2]
  have : j = min j 256 + min (j - min j 256) 256 + (j - min j 256 - min (j - min j 256) 256) := by
    omega
  conv_rhs => rw [this]
  rw [pow_add, pow_add]; ring

end Inv

/-! ## The two consumer theorems -/

theorem two_ne_zero_mod : (2 : ZMod modulus) ≠ 0 := Inv.two_ne_zero_modulus

theorem inverse_zero_case {a : Fp} (hz : a.isZero = true) : inverse a = zero := by
  unfold inverse; rw [if_pos hz]

/-- Everything about `inverse` at once. -/
theorem inverse_spec {a : Fp} (ha : Canonical a) :
    Canonical (inverse a) ∧ toZMod (inverse a).val = (toZMod a.val)⁻¹ := by
  haveI : Fact (Nat.Prime modulus) := ⟨by rw [modulus_eq]; exact EthLib.Cryptography.Bls.Fp.modulus_prime⟩
  by_cases hz : a.isZero = true
  · rw [inverse_zero_case hz, val_zero, toZMod_zero]
    have : a.val = 0 := (isZero_iff ha).mp hz
    rw [this, toZMod_zero, inv_zero]
    exact ⟨zero_canonical, rfl⟩
  · have hz' : a.isZero = false := by simpa using hz
    have hA0 : a.raw ≠ 0 := by
      intro h; apply hz
      exact (isZero_iff ha).mpr ((val_eq_zero_iff ha).mpr h)
    have hA : a.raw < modulus := ha
    have hGI : Inv.GI modulus a.raw Pw.raw a.raw zero.raw rawOne.raw (0 : UInt64).toNat :=
      Inv.gi_init (by omega) hA (by have := modulus_lt_381; omega)
    have key := Inv.go_spec hA 1000 Pw a zero rawOne 0 hGI (by simp)
    unfold inverse
    rw [if_neg hz]
    revert key
    generalize hres : Inv.go 1000 P0 P1 P2 P3 P4 P5 a.l0 a.l1 a.l2 a.l3 a.l4 a.l5
      0 0 0 0 0 0 1 0 0 0 0 0 0 = res
    rcases res with ⟨x, k⟩
    intro key
    rw [show Inv.go 1000 Pw.l0 Pw.l1 Pw.l2 Pw.l3 Pw.l4 Pw.l5 a.l0 a.l1 a.l2 a.l3 a.l4 a.l5
      zero.l0 zero.l1 zero.l2 zero.l3 zero.l4 zero.l5 rawOne.l0 rawOne.l1 rawOne.l2 rawOne.l3
      rawOne.l4 rawOne.l5 0 = (x, k) from hres] at key
    obtain ⟨-, hAx, hk⟩ := key
    simp only at hAx hk ⊢
    replace hAx : (a.raw : Z) * (x.raw : Z) = 2 ^ k.toNat := hAx
    obtain ⟨hc, hv⟩ := Inv.mulPow2_spec x (768 - k.toNat) (by omega)
    refine ⟨hc, ?_⟩
    rw [hv, toZ_val x, toZ_val a]
    have hr := toZ_rInv
    apply eq_inv_of_mul_eq_one_left
    have h768 : (2 : Z) ^ k.toNat * 2 ^ (768 - k.toNat) = 2 ^ 384 * 2 ^ 384 := by
      have : k.toNat + (768 - k.toNat) = 384 + 384 := by omega
      rw [← pow_add, ← pow_add, this]
    generalize toZMod rInv = ri at *
    generalize (2 : Z) ^ 384 = T at *
    linear_combination (ri ^ 2 * 2 ^ (768 - k.toNat)) * hAx + ri ^ 2 * h768 +
      (T * ri + 1) * hr

/-- The inverse is canonical. -/
theorem inverse_canonical {a : Fp} (ha : Canonical a) : Canonical (inverse a) :=
  (inverse_spec ha).1

/-- `Fp.inverse` computes the spec's `Fp.inverse`. -/
theorem val_inverse {a : Fp} (ha : Canonical a) :
    (inverse a).val = EthLib.Cryptography.Bls.Fp.inverse a.val := by
  haveI : Fact (Nat.Prime modulus) := ⟨by rw [modulus_eq]; exact EthLib.Cryptography.Bls.Fp.modulus_prime⟩
  apply toZMod.injective
  rw [(inverse_spec ha).2, EthLib.Cryptography.Bls.Fp.inverse_eq_inv]
  rfl

end EthLibImpl.Cryptography.Bls.Fp
