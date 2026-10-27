import Mathlib

/-! # Eigenspace characterisation of the `r`-torsion (`ψ⁴ - ψ² + 1 = 0` case) -/

namespace EigenTorsion

/-- Two scalars below `n` whose difference is a multiple of `n` agree. -/
private theorem eq_of_dvd_sub' {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (n : ℤ) ∣ (a : ℤ) - b) : a = b := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

end EigenTorsion

/-- Group-theoretic core of the `ψ(Q) = [x]Q` subgroup test for `ψ⁴ - ψ² + 1 = 0`.
The factorisation of `X⁴ - X² + 1` modulo `r` is given coefficient by coefficient. -/
theorem rTorsion_iff_eigen_phi12 {A : Type*} [AddCommGroup A] [Finite A]
    (ψ : A →+ A) (hψ : ∀ Q, ψ (ψ (ψ (ψ Q))) - ψ (ψ Q) + Q = 0)
    {r q : ℕ} [Fact r.Prime] [Fact q.Prime] (hqr : q ≠ r)
    {x l2 l3 l4 : ℤ}
    (hf1 : (r : ℤ) ∣ x + l2 + l3 + l4)
    (hf2 : (r : ℤ) ∣ (x * l2 + x * l3 + x * l4 + l2 * l3 + l2 * l4 + l3 * l4) + 1)
    (hf3 : (r : ℤ) ∣ x * l2 * l3 + x * l2 * l4 + x * l3 * l4 + l2 * l3 * l4)
    (hf4 : (r : ℤ) ∣ x * l2 * l3 * l4 - 1)
    (hx : (r : ℤ) = x ^ 4 - x ^ 2 + 1)
    (hcop2 : IsCoprime (x - l2) (r : ℤ)) (hcop3 : IsCoprime (x - l3) (r : ℤ))
    (hcop4 : IsCoprime (x - l4) (r : ℤ))
    (hcard : Nat.card A < r * r * q)
    {G : A} (hG0 : G ≠ 0) (hGr : r • G = 0) (hψG : ψ G = x • G)
    {P : A} (hP0 : P ≠ 0) (hPq : q • P = 0)
    (Q : A) : r • Q = 0 ↔ ψ Q = x • Q := by
  have hrp : (r : ℕ).Prime := Fact.out
  have hqp : (q : ℕ).Prime := Fact.out
  constructor
  · intro hQ
    have hQ' : (r : ℤ) • Q = 0 := by rw [natCast_zsmul]; exact hQ
    -- r-torsion is closed under `ψ - c`
    have hker : ∀ (c : ℤ) (E : A), (r : ℤ) • E = 0 → (r : ℤ) • (ψ E - c • E) = 0 := by
      intro c E hE
      rw [smul_sub, ← map_zsmul, hE, map_zero, smul_comm, hE, smul_zero, sub_zero]
    have hkerψ : ∀ E : A, (r : ℤ) • E = 0 → (r : ℤ) • ψ E = 0 := by
      intro E hE
      rw [← map_zsmul, hE, map_zero]
    by_contra hne
    set D := ψ Q - x • Q with hD
    have hDr : (r : ℤ) • D = 0 := hker x Q hQ'
    have hD0 : D ≠ 0 := by
      intro h0; apply hne
      linear_combination (norm := module) h0
    set D1 := ψ D - l4 • D with hD1
    set D2 := ψ D1 - l3 • D1 with hD2
    set D3 := ψ D2 - l2 • D2 with hD3
    have hD1r : (r : ℤ) • D1 = 0 := hker l4 D hDr
    have hD2r : (r : ℤ) • D2 = 0 := hker l3 D1 hD1r
    -- D3 = 0
    have hD3z : D3 = 0 := by
      obtain ⟨k1, hk1⟩ := hf1
      obtain ⟨k2, hk2⟩ := hf2
      obtain ⟨k3, hk3⟩ := hf3
      obtain ⟨k4, hk4⟩ := hf4
      have e : D3 = ψ (ψ (ψ (ψ Q))) - (x + l2 + l3 + l4) • ψ (ψ (ψ Q))
          + (x * l2 + x * l3 + x * l4 + l2 * l3 + l2 * l4 + l3 * l4) • ψ (ψ Q)
          - (x * l2 * l3 + x * l2 * l4 + x * l3 * l4 + l2 * l3 * l4) • ψ Q
          + (x * l2 * l3 * l4) • Q := by
        simp only [hD3, hD2, hD1, hD, map_sub, map_zsmul]
        module
      have h1 := hkerψ Q hQ'
      have h2 := hkerψ _ h1
      have h3 := hkerψ _ h2
      have hs := hψ Q
      have e2 : (x * l2 + x * l3 + x * l4 + l2 * l3 + l2 * l4 + l3 * l4) = r * k2 - 1 := by
        linarith
      have e4 : x * l2 * l3 * l4 = r * k4 + 1 := by linarith
      rw [e, hk1, hk3, e2, e4]
      linear_combination (norm := module) hs - k1 • h3 + k2 • h2 - k3 • h1 + k4 • hQ'
    -- Pick an eigenvector
    have key : ∃ (E : A) (μ : ℤ), E ≠ 0 ∧ (r : ℤ) • E = 0 ∧ ψ E = μ • E ∧
        IsCoprime (x - μ) (r : ℤ) := by
      by_cases h2 : D2 = 0
      · by_cases h1 : D1 = 0
        · refine ⟨D, l4, hD0, hDr, ?_, hcop4⟩
          rw [hD1] at h1
          linear_combination (norm := module) h1
        · refine ⟨D1, l3, h1, hD1r, ?_, hcop3⟩
          rw [hD2] at h2
          linear_combination (norm := module) h2
      · refine ⟨D2, l2, h2, hD2r, ?_, hcop2⟩
        rw [hD3] at hD3z
        linear_combination (norm := module) hD3z
    obtain ⟨E, μ, hE0, hEr, hψE, hcop⟩ := key
    have hordG : addOrderOf G = r := addOrderOf_eq_prime hGr hG0
    have hordE : addOrderOf E = r := addOrderOf_eq_prime (by
      rw [← natCast_zsmul]; exact hEr) hE0
    have hordP : addOrderOf P = q := addOrderOf_eq_prime hPq hP0
    let f : Fin r × Fin r × Fin q → A :=
      fun t => (t.1 : ℕ) • G + (t.2.1 : ℕ) • E + (t.2.2 : ℕ) • P
    have hf : Function.Injective f := by
      rintro ⟨a, b, k⟩ ⟨a', b', k'⟩ hab
      simp only [f] at hab
      set α : ℤ := (a : ℤ) - a' with hα
      set β : ℤ := (b : ℤ) - b' with hβ
      set κ : ℤ := (k : ℤ) - k' with hκ
      have hsum : α • G + β • E + κ • P = 0 := by
        simp only [hα, hβ, hκ, sub_smul, natCast_zsmul]
        rw [← sub_eq_zero] at hab
        rw [← hab]
        abel
      -- kill G and E terms by multiplying with r
      have hrP : ((r : ℤ) * κ) • P = 0 := by
        have h := congrArg (fun W => (r : ℤ) • W) hsum
        simp only [smul_add, smul_zero] at h
        rw [smul_comm (r : ℤ) α G, smul_comm (r : ℤ) β E, smul_comm (r : ℤ) κ P] at h
        have hGz : (r : ℤ) • G = 0 := by rw [natCast_zsmul]; exact hGr
        rw [hGz, hEr, smul_zero, smul_zero, zero_add, zero_add] at h
        rw [mul_smul, smul_comm]; exact h
      have hqd : (q : ℤ) ∣ (r : ℤ) * κ := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordP] at hrP
        exact hrP
      have hqr' : ¬ (q : ℤ) ∣ (r : ℤ) := by
        intro h
        have h' : q ∣ r := by exact_mod_cast h
        exact hqr ((Nat.prime_dvd_prime_iff_eq hqp hrp).mp h')
      have hqκ : (q : ℤ) ∣ κ := by
        have hqp' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqp
        exact (hqp'.dvd_or_dvd hqd).resolve_left hqr'
      have hκP : κ • P = 0 := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordP]; exact hqκ
      have hsum2 : α • G + β • E = 0 := by rw [hκP, add_zero] at hsum; exact hsum
      -- apply ψ - x
      have hβ0 : ((μ - x) * β) • E = 0 := by
        have h := congrArg (fun W => ψ W - x • W) hsum2
        simp only [map_add, map_zsmul, hψG, hψE, smul_zero, map_zero, sub_zero] at h
        rw [← h]
        module
      have hrβ : (r : ℤ) ∣ (μ - x) * β := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordE] at hβ0; exact hβ0
      have hrβ' : (r : ℤ) ∣ β := by
        have hc : IsCoprime (r : ℤ) (μ - x) := by
          have := hcop.neg_left
          rw [neg_sub] at this
          exact this.symm
        exact hc.dvd_of_dvd_mul_left hrβ
      have hβE : β • E = 0 := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordE]; exact hrβ'
      have hαG : α • G = 0 := by rw [hβE, add_zero] at hsum2; exact hsum2
      have hrα : (r : ℤ) ∣ α := by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordG] at hαG; exact hαG
      have hea := EigenTorsion.eq_of_dvd_sub' a.isLt a'.isLt hrα
      have heb := EigenTorsion.eq_of_dvd_sub' b.isLt b'.isLt hrβ'
      have hek := EigenTorsion.eq_of_dvd_sub' k.isLt k'.isLt hqκ
      rw [Fin.ext hea, Fin.ext heb, Fin.ext hek]
    have := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at this
    have hmul : r * (r * q) = r * r * q := by ring
    omega
  · intro hQ
    have h := hψ Q
    have h2 : ψ (ψ Q) = (x * x) • Q := by rw [hQ, map_zsmul, hQ, mul_smul]
    have h3 : ψ (ψ (ψ Q)) = (x * x * x) • Q := by rw [h2, map_zsmul, hQ]; module
    have h4 : ψ (ψ (ψ (ψ Q))) = (x * x * x * x) • Q := by rw [h3, map_zsmul, hQ]; module
    rw [h4, h2] at h
    have h' : (r : ℤ) • Q = 0 := by
      rw [hx]
      linear_combination (norm := module) h
    rw [← natCast_zsmul]
    exact h'

/-- The BLS12-381 arithmetic hypotheses discharge on the real numbers. -/
example :
    let r : ℤ := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
    let x : ℤ := -15132376222941642752
    let l2 : ℤ := 52435875175126190475982595682112313518914282969839895044348538607396160864257
    let l3 : ℤ := 15132376222941642752
    let l4 : ℤ := 3465144826073652318776269530687742778255120092542420320256
    r ∣ x + l2 + l3 + l4 ∧
    r ∣ (x * l2 + x * l3 + x * l4 + l2 * l3 + l2 * l4 + l3 * l4) + 1 ∧
    r ∣ x * l2 * l3 + x * l2 * l4 + x * l3 * l4 + l2 * l3 * l4 ∧
    r ∣ x * l2 * l3 * l4 - 1 ∧
    r = x ^ 4 - x ^ 2 + 1 ∧
    IsCoprime (x - l2) r ∧ IsCoprime (x - l3) r ∧ IsCoprime (x - l4) r := by
  intro r x l2 l3 l4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ⟨-17478625058375396825327531894037437839638094323279965014787890327873034169003, -17478625058375396824172483618679553733455667416434933948062845614753339321002, by norm_num [x, l2, l3, l4, r]⟩
  · exact ⟨1732572413036826159388134765343871389127560046271210160128, 1, by norm_num [x, l2, l3, l4, r]⟩
  · exact ⟨3465144826073652318776269530687742778270252468765361963008, 228988810152649578064853576960394133505, by norm_num [x, l2, l3, l4, r]⟩

