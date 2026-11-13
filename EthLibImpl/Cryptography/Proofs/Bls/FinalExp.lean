import EthLibImpl.Cryptography.Proofs.Bls.SpecFp12

/-!
# Proofs: the implementation's final exponentiation is the spec's cube

`Mirror.finalExpCube f = (f ^ finalExpExponent) ^ 3` for every `f : Fp12`
(`Mirror.finalExpCube_eq_pow`), hence
`Mirror.finalExpCube f = (EthLib.Cryptography.Bls.finalExponentiation f) ^ 3`
(`Mirror.finalExpCube_eq`), through the spec proofs' `finalExponentiation_eq_pow`
(`finalExponentiation f = f ^ ((p¹² - 1)/r)`). The implementation (mirrored
over spec types in `MirrorPairing`) runs the easy part, then the hard part with
compressed cyclotomic squarings and ladders in `|x|`.

* `Mirror.cycSqr_eq`: on the cyclotomic subgroup
  `{a : a^(p⁴ - p² + 1) = 1}`, `cycSqr a = a * a`. The mirror's `cycSqr` is
  the spec's `Fp12.cyclotomicSquare` (`Mirror.cycSqr_eq_cyclotomicSquare`, a
  ring identity per coordinate), which the spec proves is squaring there
  (`Fp12.cyclotomicSquare_eq_mul_self_of_order`).
* Karabina compression: for cyclotomic `a`, coordinates `a0 … a5` satisfy
  `4·a1·a3 = ξ·a5² + 3·a2² - 2·a4`, `ξ(a3·a4 - 2·a2·a5) = a1(1 - a0)` and
  `a0 = ξ(2·a3² + a1·a5 - 3·a2·a4) + 1` (`Mirror.cyc_rels`, certificates by
  polynomial division, from `a^(p⁴)·a = a^(p²)` with `frobenius2` as
  `x ↦ x^(p²)` and `γ² - γ + 1 = 0` for `γ = ξ^((p² - 1)/6)`). They give
  `Mirror.decompress_compress`, including the degenerate case `a1 = a4 = 0`,
  which forces `a = 1` because `ξ` is not a square (`Mirror.xi_not_sq`).
  `Mirror.csqrN_compress` and `Mirror.cycPowAbsX_eq` assemble `g^|x|` from the
  saved powers `g^(2^k)`.
* Exponent bookkeeping (`decide` on `Nat`): the result is `g^N` with
  `g = f^((p⁶ - 1)(p² + 1))` cyclotomic and `N ≡ 3(p⁴ - p² + 1)/r` modulo
  `p⁴ - p² + 1`; and `E = (p⁶ - 1)(p² + 1)·(p⁴ - p² + 1)/r`. The case
  `f = 0` is separate (every step maps `0` to `0`).
* For the Miller loop: `Fp12.ι2_pow_finalExpExponent`,
  `Fp12.ι1_pow_finalExpExponent` (nonzero `Fp2`/`Fp` scalars are killed by
  `E`) and `Fp12.w_pow_three_mul_finalExpExponent` (`w^(3E) = 1`).
-/

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2
open scoped EthLib.Cryptography.Bls.Fp12

namespace EthLib.Cryptography.Bls.Fp12

open EthLibImpl.Cryptography.Bls

/-- Nonzero `Fp2` scalars are killed by the final exponent:
`(p² - 1) ∣ E`. -/
theorem ι2_pow_finalExpExponent {c : Fp2} (hc : c ≠ 0) : ι2 c ^ finalExpExponent = 1 := by
  rw [show finalExpExponent = (Fp.modulus ^ 2 - 1) * (finalExpExponent / (Fp.modulus ^ 2 - 1))
    by decide +kernel, pow_mul, ← _root_.map_pow, Fp2.pow_card_sub_one_eq_one hc,
    _root_.map_one, one_pow]

/-- Nonzero `Fp` scalars are killed by the final exponent. -/
theorem ι1_pow_finalExpExponent {c : Fp} (hc : c ≠ 0) : ι1 c ^ finalExpExponent = 1 :=
  ι2_pow_finalExpExponent fun h => hc (congrArg Fp2.c0 h)

/-- `w^(3E) = 1`: `w⁶ = ξ` and `2(p² - 1) ∣ E`. -/
theorem w_pow_three_mul_finalExpExponent : w ^ (3 * finalExpExponent) = 1 := by
  rw [show 3 * finalExpExponent = 6 * ((Fp.modulus ^ 2 - 1)
      * (finalExpExponent / (2 * (Fp.modulus ^ 2 - 1)))) by decide +kernel,
    pow_mul, w_pow_six, pow_mul, ← _root_.map_pow,
    Fp2.pow_card_sub_one_eq_one Mirror.xi_ne_zero, _root_.map_one, one_pow]

end EthLib.Cryptography.Bls.Fp12

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Fp12 (mk6 mk6_eta mk6_inj mk6_congr mk6_mul_mk6 zero_eq_mk6
  conjugate_eq_pow conjugate_mk6)

/-! ## Cyclotomic squaring -/

/-- `cycSqr` in `w`-power coordinates. -/
theorem cycSqr_mk6 (a0 a1 a2 a3 a4 a5 : Fp2) :
    cycSqr (mk6 a0 a1 a2 a3 a4 a5) = mk6 (3 * (a0 * a0 + xi * (a3 * a3)) - 2 * a0)
      (3 * (xi * (2 * (a2 * a5))) + 2 * a1) (3 * (a1 * a1 + xi * (a4 * a4)) - 2 * a2)
      (3 * (2 * (a0 * a3)) + 2 * a3) (3 * (a2 * a2 + xi * (a5 * a5)) - 2 * a4)
      (3 * (2 * (a1 * a4)) + 2 * a5) := by
  simp only [cycSqr, sqrFp4, threeSubTwo, threeAddTwo, mk6, Fp2.mulByOnePlusI_eq, xi_eq]
  apply Fp12.ext <;> apply Fp6.ext <;> ring

/-- The mirror's `cycSqr` (the implementation's Granger–Scott formulas) is the
spec's `Fp12.cyclotomicSquare`, for every input. -/
theorem cycSqr_eq_cyclotomicSquare (a : Fp12) : cycSqr a = a.cyclotomicSquare := by
  simp only [cycSqr, sqrFp4, threeSubTwo, threeAddTwo, Fp12.cyclotomicSquare,
    Fp2.mulByOnePlusI_eq]
  apply Fp12.ext <;> apply Fp6.ext <;> ring

/-- Granger–Scott: on the cyclotomic subgroup `a^(p⁴ - p² + 1) = 1`, the
implementation's `cycSqr` is squaring. -/
theorem cycSqr_eq {a : Fp12} (ha : a ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    cycSqr a = a * a := by
  rw [cycSqr_eq_cyclotomicSquare, Fp12.cyclotomicSquare_eq_mul_self_of_order ha]

theorem cycSqr_zero : cycSqr 0 = 0 := by
  rw [cycSqr_eq_cyclotomicSquare, Fp12.cyclotomicSquare_zero]

/-! ## Karabina decompression -/

/-- Coordinates of a cyclotomic element: `R1` to `R3` express `a3` and `a0` by the
compressed coordinates, and `N0` is the zeroth coordinate of `conj a * a = 1`. -/
theorem cyc_rels {a0 a1 a2 a3 a4 a5 : Fp2}
    (ha : mk6 a0 a1 a2 a3 a4 a5 ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    4 * a1 * a3 = xi * a5 ^ 2 + 3 * a2 ^ 2 - 2 * a4 ∧
    xi * (a3 * a4 - 2 * a2 * a5) = a1 * (1 - a0) ∧
    a0 = xi * (2 * a3 ^ 2 + a1 * a5 - 3 * a2 * a4) + 1 ∧
    a0 ^ 2 + xi * (2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2) = 1 := by
  generalize hA : mk6 a0 a1 a2 a3 a4 a5 = A at ha
  have H : frobenius2 (frobenius2 A) * A = frobenius2 A := by
    rw [frobenius2_eq, frobenius2_eq, ← pow_mul, ← pow_succ,
      show Fp.modulus ^ 2 * Fp.modulus ^ 2 + 1
        = Fp.modulus ^ 2 + (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) by decide,
      pow_add, ha, mul_one]
  have N : A.conjugate * A = 1 := by
    rw [conjugate_eq_pow, ← pow_succ,
      show Fp.modulus ^ 6 + 1 = (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) * (Fp.modulus ^ 2 + 1)
        by decide, pow_mul, ha, one_pow]
  subst hA
  rw [frobenius2_mk6, frobenius2_mk6, mk6_mul_mk6] at H
  rw [conjugate_mk6, mk6_mul_mk6, show (1 : Fp12) = mk6 1 0 0 0 0 0 from rfl] at N
  obtain ⟨H0, H1, H2, H3, H4, H5⟩ := mk6_inj H
  obtain ⟨N0, N1, N2, N3, N4, N5⟩ := mk6_inj N
  have hg := gamma_two_one_sq
  simp only [gamma_eq_pow 2 2, gamma_eq_pow 2 3, gamma_eq_pow 2 4, gamma_eq_pow 2 5]
    at H0 H1 H2 H3 H4 H5
  generalize gamma 2 1 = g at H0 H1 H2 H3 H4 H5 hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-2 * (g - 1)) * H4 + (-1) * N4 + (2*a0*a4*g^7 - 2*a0*a4*g^5 - 2*a0*a4*g^4 + 2*a0*a4*g^2 + 2*a0*a4*g + 2*a1*a3*g^5 - 2*a1*a3*g^3 - 2*a1*a3*g^2 + 2*a1*a3*g + 2*a1*a3 + 2*a2^2*g^3 - 2*a2^2*g - 2*a2^2 - 2*a4*g^3 + 2*a4*g + 2*a4 + 2*a5^2*g^9*xi - 2*a5^2*g^7*xi - 2*a5^2*g^6*xi + 2*a5^2*g^4*xi + 2*a5^2*g^3*xi - 2*a5^2*g*xi - 2*a5^2*xi) * hg
  · linear_combination (-(g - 1)) * H1 + (a0*a1*g - a1 + a2*a5*g^9*xi - a2*a5*g^7*xi - a2*a5*g^6*xi + a2*a5*g^4*xi + 2*a2*a5*g^3*xi - 2*a2*a5*g*xi - 2*a2*a5*xi + a3*a4*g^7*xi - a3*a4*g^4*xi - a3*a4*g^3*xi + a3*a4*g*xi + a3*a4*xi) * hg
  · linear_combination (-1) * H0 + N0 + (a1*a5*g^8*xi + a1*a5*g^7*xi - a1*a5*g^5*xi - a1*a5*g^4*xi + a1*a5*g^2*xi + a1*a5*g*xi + a1*a5*xi + a2*a4*g^6*xi + a2*a4*g^5*xi - a2*a4*g^3*xi + a2*a4*g*xi + a2*a4*xi + a3^2*g^4*xi + a3^2*g^3*xi - a3^2*g*xi - a3^2*xi) * hg
  · linear_combination N0

/-- `ξ` is not a square in `Fp2`: `ξ^((p² - 1)/2) = γ³ = -1`. -/
theorem xi_not_sq (s : Fp2) : xi ≠ s * s := fun hs => xi_not_square s hs.symm

private theorem two_ne_zero' : (2 : Fp2) ≠ 0 := by decide_eq_at_model []
private theorem three_ne_zero' : (3 : Fp2) ≠ 0 := by decide_eq_at_model []
private theorem four_ne_zero' : (4 : Fp2) ≠ 0 := by decide_eq_at_model []

/-- `4ξt² + 3 = 0` has no solution `t ≠ 0`: it would make `ξ` a square, since
`(2γ - 1)² = -3`. -/
theorem no_root {t : Fp2} (h : 4 * xi * t ^ 2 + 3 = 0) : t = 0 := by
  by_contra h0
  have hg := gamma_two_one_sq
  have h2 := two_ne_zero'
  generalize gamma 2 1 = g at hg
  apply xi_not_sq ((2 * g - 1) / (2 * t))
  field_simp
  linear_combination h - 4 * hg

theorem g4_eq {a0 a1 a2 a3 a4 a5 : Fp2}
    (ha : mk6 a0 a1 a2 a3 a4 a5 ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    (g4Frac (compress (mk6 a0 a1 a2 a3 a4 a5))).1 *
      (g4Frac (compress (mk6 a0 a1 a2 a3 a4 a5))).2.inverse = a3 := by
  obtain ⟨R1, R2, R3, N0⟩ := cyc_rels ha
  have h3 := three_ne_zero'
  have h4 := four_ne_zero'
  have hxi := xi_ne_zero
  unfold g4Frac compress
  simp only [mk6]
  by_cases h1 : a1 = 0
  · have hz : a1.isZero = true := Fp2.isZero_iff.mpr h1
    simp only [hz, ↓reduceIte]
    subst h1
    by_cases h4' : a4 = 0
    · subst h4'
      simp only [Fp2.inverse_eq_inv, inv_zero, mul_zero]
      have h2 := two_ne_zero'
      have h25 : a2 * a5 = 0 := by
        have : 2 * (xi * (a2 * a5)) = 0 := by linear_combination (-1) * R2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h h2
        · exact (mul_eq_zero.1 h).resolve_left hxi
      have h2z : a2 = 0 ∧ a5 = 0 := by
        rcases mul_eq_zero.1 h25 with h | h
        · subst h
          have : xi * a5 ^ 2 = 0 := by linear_combination (-1) * R1
          have := (mul_eq_zero.1 this).resolve_left hxi
          exact ⟨rfl, pow_eq_zero_iff (two_ne_zero) |>.1 this⟩
        · subst h
          have : 3 * a2 ^ 2 = 0 := by linear_combination (-1) * R1
          have := (mul_eq_zero.1 this).resolve_left h3
          exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 this, rfl⟩
      obtain ⟨rfl, rfl⟩ := h2z
      have e : xi * a3 ^ 2 * (4 * xi * a3 ^ 2 + 3) = 0 := by
        have : a0 = 2 * xi * a3 ^ 2 + 1 := by linear_combination R3
        subst this
        linear_combination N0
      by_cases ha3 : a3 = 0
      · exact ha3.symm
      · have := (mul_eq_zero.1 e).resolve_left (mul_ne_zero hxi (pow_ne_zero 2 ha3))
        exact absurd (no_root this) ha3
    · simp only [Fp2.inverse_eq_inv]
      rw [mul_inv_eq_iff_eq_mul₀ h4']
      have : xi * (a3 * a4 - 2 * a2 * a5) = 0 := by linear_combination R2
      have := (mul_eq_zero.1 this).resolve_left hxi
      linear_combination (-1) * this
  · have hz : a1.isZero = false := Bool.eq_false_iff.mpr fun h => h1 (Fp2.isZero_iff.mp h)
    simp only [hz, Bool.false_eq_true, ↓reduceIte]
    simp only [Fp2.inverse_eq_inv, Fp2.mulByOnePlusI_eq, ← xi_eq]
    have hd : a1 + a1 + (a1 + a1) ≠ 0 := by
      have : a1 + a1 + (a1 + a1) = 4 * a1 := by ring
      rw [this]; exact mul_ne_zero h4 h1
    rw [mul_inv_eq_iff_eq_mul₀ hd]
    linear_combination (-1) * R1

/-- Karabina decompression recovers a cyclotomic element from its compression. -/
theorem decompress_compress {A : Fp12} (hA : A ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    decompress (compress A) = A := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5, A = mk6 a0 a1 a2 a3 a4 a5 := ⟨_, _, _, _, _, _, (mk6_eta A).symm⟩
  obtain ⟨_, _, R3, _⟩ := cyc_rels hA
  unfold decompress
  rw [g4_eq hA]
  show mk6 _ a1 a2 a3 a4 a5 = _
  apply mk6_congr _ rfl rfl rfl rfl rfl
  simp only [compress, mk6, Fp2.mulByOnePlusI_eq, ← xi_eq, Fp2.one_eq_one]
  linear_combination (-1) * R3

/-- Compression commutes with `cycSqr` (formula equality). -/
theorem compress_cycSqr (a : Fp12) : compress (cycSqr a) = csqr (compress a) := rfl

/-- On the cyclotomic subgroup, `n` compressed squarings compress `2ⁿ`-th powers. -/
theorem csqrN_compress (n : ℕ) : ∀ {b : Fp12},
    b ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 →
    csqrN (compress b) n = compress (b ^ (2 ^ n)) := by
  induction n with
  | zero => intro b _; rw [csqrN, pow_zero, pow_one]
  | succ n ih =>
    intro b hb
    have hb2 : (b ^ 2) ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hb, one_pow]
    rw [csqrN, ← compress_cycSqr, cycSqr_eq hb, ← sq, ih hb2, ← pow_mul, ← Nat.pow_succ']

/-- `cycPowAbsX` raises a cyclotomic element to `|x|`. -/
theorem cycPowAbsX_eq {h : Fp12} (hh : h ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    cycPowAbsX h = h ^ blsX := by
  have hc : ∀ m : ℕ, (h ^ m) ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hh, one_pow]
  have c16 : csqrN (compress h) 16 = compress (h ^ (2 ^ 16)) := csqrN_compress 16 hh
  have c48 : csqrN (compress (h ^ (2 ^ 16))) 32 = compress (h ^ (2 ^ 48)) := by
    rw [csqrN_compress 32 (hc _), ← pow_mul, ← pow_add]
  have c57 : csqrN (compress (h ^ (2 ^ 48))) 9 = compress (h ^ (2 ^ 57)) := by
    rw [csqrN_compress 9 (hc _), ← pow_mul, ← pow_add]
  have c60 : csqrN (compress (h ^ (2 ^ 57))) 3 = compress (h ^ (2 ^ 60)) := by
    rw [csqrN_compress 3 (hc _), ← pow_mul, ← pow_add]
  have c62 : csqrN (compress (h ^ (2 ^ 60))) 2 = compress (h ^ (2 ^ 62)) := by
    rw [csqrN_compress 2 (hc _), ← pow_mul, ← pow_add]
  have c63 : csqr (compress (h ^ (2 ^ 62))) = compress (h ^ (2 ^ 63)) := by
    rw [← compress_cycSqr, cycSqr_eq (hc _), ← sq, ← pow_mul, ← Nat.pow_succ]
  simp only [cycPowAbsX, decompress6]
  rw [c16, c48, c57, c60, c62, c63, decompress_compress (hc _), decompress_compress (hc _),
    decompress_compress (hc _), decompress_compress (hc _), decompress_compress (hc _),
    decompress_compress (hc _), ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1

/-! ## The final exponentiation -/

theorem finalExpCube_zero : finalExpCube 0 = 0 := by
  have hc : Fp12.conjugate (0 : Fp12) = 0 := by rw [conjugate_eq_pow, zero_pow (pow_pos Fp.modulus_pos _).ne']
  have hf1 : frobenius1 0 = 0 := by rw [frobenius1_eq, zero_pow (by decide)]
  have hf2 : frobenius2 0 = 0 := by rw [frobenius2_eq, zero_pow (pow_pos Fp.modulus_pos _).ne']
  have hi : Fp12.inverse (0 : Fp12) = 0 := Fp12.inverse_zero
  have hs : cycSqr (0 : Fp12) = 0 := cycSqr_zero
  simp only [finalExpCube, hc, hi, mul_zero, hf2, hf1, hs]

/-- The implementation's final exponentiation computes the cube of
`f ^ ((p¹² - 1)/r)` for every `f`. -/
theorem finalExpCube_eq_pow (f : Fp12) : finalExpCube f = (f ^ finalExpExponent) ^ 3 := by
  by_cases hf : f = 0
  · subst hf
    rw [finalExpCube_zero, zero_pow (by decide), zero_pow (by decide)]
  -- The easy part: `f1 = f^(p⁶ - 1)` has `f1^(p⁶ + 1) = 1`.
  have hcf : f.conjugate ≠ 0 := by
    rw [conjugate_eq_pow]
    exact pow_ne_zero _ hf
  have hf1 : f.conjugate * f.inverse = f ^ (Fp.modulus ^ 6 - 1) := by
    rw [pow_sub₀ f hf (Nat.one_le_pow _ _ Fp.modulus_pos), pow_one, conjugate_eq_pow,
      Fp12.inverse_eq_inv]
  have hf1c : (f.conjugate * f.inverse) ^ (Fp.modulus ^ 6 + 1) = 1 := by
    rw [pow_succ, mul_pow, ← conjugate_eq_pow, Fp12.conjugate_conjugate, Fp12.inverse_eq_inv,
      inv_pow, ← conjugate_eq_pow, mul_assoc, inv_mul_cancel_left₀ hcf, mul_inv_cancel₀ hf]
  -- `g = f1^(p² + 1)` is cyclotomic.
  generalize hG : frobenius2 (f.conjugate * f.inverse) * (f.conjugate * f.inverse) = g
  have hgf : f ^ ((Fp.modulus ^ 6 - 1) * (Fp.modulus ^ 2 + 1)) = g := by
    rw [← hG, frobenius2_eq, ← pow_succ, hf1, ← pow_mul]
  have hgc : g ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := by
    rw [← hG, frobenius2_eq, ← pow_succ, ← pow_mul,
      show (Fp.modulus ^ 2 + 1) * (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1)
        = Fp.modulus ^ 6 + 1 by decide, hf1c]
  have hpc : ∀ m, (g ^ m) ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hgc, one_pow]
  -- The hard part, as powers of `g`.
  have hA0 : cycPowAbsX g * g = g ^ (blsX + 1) := by rw [cycPowAbsX_eq hgc, ← pow_succ]
  have hS : cycSqr g * g = g ^ 3 := by rw [cycSqr_eq hgc]; ring
  have hX : ∀ m, cycPowAbsX (g ^ m) = g ^ (m * blsX) := fun m => by
    rw [cycPowAbsX_eq (hpc m), ← pow_mul]
  have hC : ∀ m, (g ^ m).conjugate = g ^ (m * Fp.modulus ^ 6) := fun m => by
    rw [conjugate_eq_pow, ← pow_mul]
  have hF1 : ∀ m, frobenius1 (g ^ m) = g ^ (m * Fp.modulus) := fun m => by
    rw [frobenius1_eq, ← pow_mul]
  have hF2 : ∀ m, frobenius2 (g ^ m) = g ^ (m * Fp.modulus ^ 2) := fun m => by
    rw [frobenius2_eq, ← pow_mul]
  simp only [finalExpCube, hG, hA0, hS, hX, hC, hF1, hF2, ← pow_add]
  rw [show finalExpExponent = (Fp.modulus ^ 6 - 1) * (Fp.modulus ^ 2 + 1)
      * ((Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) / Fr.modulus) by decide +kernel,
    pow_mul, hgf, ← pow_mul, pow_eq_pow_mod _ hgc]
  conv_rhs => rw [pow_eq_pow_mod _ hgc]
  congr 1

/-- The implementation's final exponentiation computes the cube of the spec's
`finalExponentiation f` for every `f`. -/
theorem finalExpCube_eq (f : Fp12) :
    finalExpCube f = (EthLib.Cryptography.Bls.finalExponentiation f) ^ 3 := by
  rw [finalExpCube_eq_pow, finalExponentiation_eq_pow]

end EthLibImpl.Cryptography.Bls.Mirror
