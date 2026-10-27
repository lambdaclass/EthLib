import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.PowMod
import EthLib.Cryptography.Proofs.Bls.FrZMod
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.G2Group
import EthLibImpl.Cryptography.Proofs.Bls.G2Check
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: the order of the twist curve and a point of order `q`

Three facts about `E'(Fp2)` (the spec's `G2` curve) used to pin down its
group structure:

* `card_point_lt_rrq`: the curve has fewer than `r² · q` points. A point is
  determined by `x` and the sign bit of `y`, so `#E'(Fp2) ≤ 2p² + 1`.
* `q_prime`: the 448-bit prime `q`, the largest prime factor of the `G2`
  cofactor, is prime, by a Pratt tree of Lucas certificates (as for `p` in
  `Proofs.Bls.FpZMod`).
* `P1_order`: an explicit point `P1` of order `q`, i.e. `toPoint P1 ≠ 0` and
  `q • toPoint P1 = 0`. The multiplication is the structural MSB-first ladder
  `Mirror.G2.mulMsb`, evaluated by the kernel.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2
open scoped EthLib.Cryptography.Bls.Fp2
open EthLib.Cryptography
open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian

set_option maxRecDepth 8000
set_option exponentiation.threshold 600

/-! ## `q` is prime -/

private theorem pow_card_sub_one_63240439939 :
    ((3 : Nat) : ZMod 63240439939) ^ (63240439939 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 63240439939 36 3 (63240439939 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_63240439939 :
    ∀ q : Nat, q.Prime → q ∣ 63240439939 - 1 →
      ((3 : Nat) : ZMod 63240439939) ^ ((63240439939 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 63240439939 - 1 = 2 * (3 * (13 * (810774871))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 63240439939 36 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 63240439939 36 3 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 63240439939 36 3 13 (by decide) (by decide)
  · obtain rfl := heq 810774871 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 63240439939 36 3 810774871 (by decide) (by decide)

/-- Pratt-tree node: `63240439939` is prime (witness `3`). -/
private theorem prime_63240439939 : Nat.Prime 63240439939 :=
  lucas_primality 63240439939 ((3 : Nat) : ZMod 63240439939)
    pow_card_sub_one_63240439939 pow_div_prime_ne_one_63240439939

private theorem pow_card_sub_one_1435735831703 :
    ((5 : Nat) : ZMod 1435735831703) ^ (1435735831703 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1435735831703 41 5 (1435735831703 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1435735831703 :
    ∀ q : Nat, q.Prime → q ∣ 1435735831703 - 1 →
      ((5 : Nat) : ZMod 1435735831703) ^ ((1435735831703 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1435735831703 - 1 = 2 * (2969 * (241787779)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 1435735831703 41 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2969 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1435735831703 41 5 2969 (by decide) (by decide)
  · obtain rfl := heq 241787779 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 1435735831703 41 5 241787779 (by decide) (by decide)

/-- Pratt-tree node: `1435735831703` is prime (witness `5`). -/
private theorem prime_1435735831703 : Nat.Prime 1435735831703 :=
  lucas_primality 1435735831703 ((5 : Nat) : ZMod 1435735831703)
    pow_card_sub_one_1435735831703 pow_div_prime_ne_one_1435735831703

private theorem pow_card_sub_one_1770732318293 :
    ((2 : Nat) : ZMod 1770732318293) ^ (1770732318293 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1770732318293 41 2 (1770732318293 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1770732318293 :
    ∀ q : Nat, q.Prime → q ∣ 1770732318293 - 1 →
      ((2 : Nat) : ZMod 1770732318293) ^ ((1770732318293 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1770732318293 - 1 = 2 ^ 2 * (7 * (63240439939)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1770732318293 41 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1770732318293 41 2 7 (by decide) (by decide)
  · obtain rfl := heq 63240439939 prime_63240439939 hdvd
    exact PowMod.natCast_pow_div_ne_one 1770732318293 41 2 63240439939 (by decide) (by decide)

/-- Pratt-tree node: `1770732318293` is prime (witness `2`). -/
private theorem prime_1770732318293 : Nat.Prime 1770732318293 :=
  lucas_primality 1770732318293 ((2 : Nat) : ZMod 1770732318293)
    pow_card_sub_one_1770732318293 pow_div_prime_ne_one_1770732318293

private theorem pow_card_sub_one_12192593745179 :
    ((2 : Nat) : ZMod 12192593745179) ^ (12192593745179 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 12192593745179 44 2 (12192593745179 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_12192593745179 :
    ∀ q : Nat, q.Prime → q ∣ 12192593745179 - 1 →
      ((2 : Nat) : ZMod 12192593745179) ^ ((12192593745179 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 12192593745179 - 1 = 2 * (7 * (11 * (107 * (541 * (1367711))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 7 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 107 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 107 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 541 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 541 (by decide) (by decide)
  · obtain rfl := heq 1367711 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 12192593745179 44 2 1367711 (by decide) (by decide)

/-- Pratt-tree node: `12192593745179` is prime (witness `2`). -/
private theorem prime_12192593745179 : Nat.Prime 12192593745179 :=
  lucas_primality 12192593745179 ((2 : Nat) : ZMod 12192593745179)
    pow_card_sub_one_12192593745179 pow_div_prime_ne_one_12192593745179

private theorem pow_card_sub_one_16297965815447 :
    ((5 : Nat) : ZMod 16297965815447) ^ (16297965815447 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 16297965815447 44 5 (16297965815447 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_16297965815447 :
    ∀ q : Nat, q.Prime → q ∣ 16297965815447 - 1 →
      ((5 : Nat) : ZMod 16297965815447) ^ ((16297965815447 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 16297965815447 - 1 = 2 * (7 ^ 3 * (68059 * (349079))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 16297965815447 44 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 16297965815447 44 5 7 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 68059 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 16297965815447 44 5 68059 (by decide) (by decide)
  · obtain rfl := heq 349079 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 16297965815447 44 5 349079 (by decide) (by decide)

/-- Pratt-tree node: `16297965815447` is prime (witness `5`). -/
private theorem prime_16297965815447 : Nat.Prime 16297965815447 :=
  lucas_primality 16297965815447 ((5 : Nat) : ZMod 16297965815447)
    pow_card_sub_one_16297965815447 pow_div_prime_ne_one_16297965815447

private theorem pow_card_sub_one_512088937297519 :
    ((6 : Nat) : ZMod 512088937297519) ^ (512088937297519 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 512088937297519 49 6 (512088937297519 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_512088937297519 :
    ∀ q : Nat, q.Prime → q ∣ 512088937297519 - 1 →
      ((6 : Nat) : ZMod 512088937297519) ^ ((512088937297519 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 512088937297519 - 1 = 2 * (3 * (7 * (12192593745179))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 49 6 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 49 6 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 49 6 7 (by decide) (by decide)
  · obtain rfl := heq 12192593745179 prime_12192593745179 hdvd
    exact PowMod.natCast_pow_div_ne_one 512088937297519 49 6 12192593745179 (by decide) (by decide)

/-- Pratt-tree node: `512088937297519` is prime (witness `6`). -/
private theorem prime_512088937297519 : Nat.Prime 512088937297519 :=
  lucas_primality 512088937297519 ((6 : Nat) : ZMod 512088937297519)
    pow_card_sub_one_512088937297519 pow_div_prime_ne_one_512088937297519

private theorem pow_card_sub_one_1857858664515398933 :
    ((2 : Nat) : ZMod 1857858664515398933) ^ (1857858664515398933 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1857858664515398933 61 2 (1857858664515398933 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1857858664515398933 :
    ∀ q : Nat, q.Prime → q ∣ 1857858664515398933 - 1 →
      ((2 : Nat) : ZMod 1857858664515398933) ^ ((1857858664515398933 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1857858664515398933 - 1 = 2 ^ 2 * (907 * (512088937297519)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 61 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 907 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 61 2 907 (by decide) (by decide)
  · obtain rfl := heq 512088937297519 prime_512088937297519 hdvd
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 61 2 512088937297519 (by decide) (by decide)

/-- Pratt-tree node: `1857858664515398933` is prime (witness `2`). -/
private theorem prime_1857858664515398933 : Nat.Prime 1857858664515398933 :=
  lucas_primality 1857858664515398933 ((2 : Nat) : ZMod 1857858664515398933)
    pow_card_sub_one_1857858664515398933 pow_div_prime_ne_one_1857858664515398933

private theorem pow_card_sub_one_21561538103037546247 :
    ((5 : Nat) : ZMod 21561538103037546247) ^ (21561538103037546247 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 21561538103037546247 65 5 (21561538103037546247 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_21561538103037546247 :
    ∀ q : Nat, q.Prime → q ∣ 21561538103037546247 - 1 →
      ((5 : Nat) : ZMod 21561538103037546247) ^ ((21561538103037546247 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 21561538103037546247 - 1 = 2 * (3 ^ 3 * (225493 * (1770732318293))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 65 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 65 5 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 225493 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 65 5 225493 (by decide) (by decide)
  · obtain rfl := heq 1770732318293 prime_1770732318293 hdvd
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 65 5 1770732318293 (by decide) (by decide)

/-- Pratt-tree node: `21561538103037546247` is prime (witness `5`). -/
private theorem prime_21561538103037546247 : Nat.Prime 21561538103037546247 :=
  lucas_primality 21561538103037546247 ((5 : Nat) : ZMod 21561538103037546247)
    pow_card_sub_one_21561538103037546247 pow_div_prime_ne_one_21561538103037546247

private theorem pow_card_sub_one_22294303974184787197 :
    ((14 : Nat) : ZMod 22294303974184787197) ^ (22294303974184787197 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 22294303974184787197 65 14 (22294303974184787197 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_22294303974184787197 :
    ∀ q : Nat, q.Prime → q ∣ 22294303974184787197 - 1 →
      ((14 : Nat) : ZMod 22294303974184787197) ^ ((22294303974184787197 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 22294303974184787197 - 1 = 2 ^ 2 * (3 * (1857858664515398933)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 65 14 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 65 14 3 (by decide) (by decide)
  · obtain rfl := heq 1857858664515398933 prime_1857858664515398933 hdvd
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 65 14 1857858664515398933 (by decide) (by decide)

/-- Pratt-tree node: `22294303974184787197` is prime (witness `14`). -/
private theorem prime_22294303974184787197 : Nat.Prime 22294303974184787197 :=
  lucas_primality 22294303974184787197 ((14 : Nat) : ZMod 22294303974184787197)
    pow_card_sub_one_22294303974184787197 pow_div_prime_ne_one_22294303974184787197

private theorem pow_card_sub_one_86246152412150184989 :
    ((2 : Nat) : ZMod 86246152412150184989) ^ (86246152412150184989 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 86246152412150184989 67 2 (86246152412150184989 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_86246152412150184989 :
    ∀ q : Nat, q.Prime → q ∣ 86246152412150184989 - 1 →
      ((2 : Nat) : ZMod 86246152412150184989) ^ ((86246152412150184989 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 86246152412150184989 - 1 = 2 ^ 2 * (21561538103037546247) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 86246152412150184989 67 2 2 (by decide) (by decide)
  · obtain rfl := heq 21561538103037546247 prime_21561538103037546247 hdvd
    exact PowMod.natCast_pow_div_ne_one 86246152412150184989 67 2 21561538103037546247 (by decide) (by decide)

/-- Pratt-tree node: `86246152412150184989` is prime (witness `2`). -/
private theorem prime_86246152412150184989 : Nat.Prime 86246152412150184989 :=
  lucas_primality 86246152412150184989 ((2 : Nat) : ZMod 86246152412150184989)
    pow_card_sub_one_86246152412150184989 pow_div_prime_ne_one_86246152412150184989

private theorem pow_card_sub_one_19931107752921199754119 :
    ((3 : Nat) : ZMod 19931107752921199754119) ^ (19931107752921199754119 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 19931107752921199754119 75 3 (19931107752921199754119 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_19931107752921199754119 :
    ∀ q : Nat, q.Prime → q ∣ 19931107752921199754119 - 1 →
      ((3 : Nat) : ZMod 19931107752921199754119) ^ ((19931107752921199754119 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 19931107752921199754119 - 1 = 2 * (3 * (149 * (22294303974184787197))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 75 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 75 3 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 149 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 75 3 149 (by decide) (by decide)
  · obtain rfl := heq 22294303974184787197 prime_22294303974184787197 hdvd
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 75 3 22294303974184787197 (by decide) (by decide)

/-- Pratt-tree node: `19931107752921199754119` is prime (witness `3`). -/
private theorem prime_19931107752921199754119 : Nat.Prime 19931107752921199754119 :=
  lucas_primality 19931107752921199754119 ((3 : Nat) : ZMod 19931107752921199754119)
    pow_card_sub_one_19931107752921199754119 pow_div_prime_ne_one_19931107752921199754119

private theorem pow_card_sub_one_81162125843606155545104998607900118769099783 :
    ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783) ^ (81162125843606155545104998607900118769099783 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 81162125843606155545104998607900118769099783 146 5 (81162125843606155545104998607900118769099783 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_81162125843606155545104998607900118769099783 :
    ∀ q : Nat, q.Prime → q ∣ 81162125843606155545104998607900118769099783 - 1 →
      ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783) ^ ((81162125843606155545104998607900118769099783 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 81162125843606155545104998607900118769099783 - 1 = 2 * (3 ^ 2 * (2731 * (57697 * (1435735831703 * (19931107752921199754119))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2731 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 2731 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 57697 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 57697 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 1435735831703 prime_1435735831703 h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 1435735831703 (by decide) (by decide)
  · obtain rfl := heq 19931107752921199754119 prime_19931107752921199754119 hdvd
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 146 5 19931107752921199754119 (by decide) (by decide)

/-- Pratt-tree node: `81162125843606155545104998607900118769099783` is prime (witness `5`). -/
private theorem prime_81162125843606155545104998607900118769099783 : Nat.Prime 81162125843606155545104998607900118769099783 :=
  lucas_primality 81162125843606155545104998607900118769099783 ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783)
    pow_card_sub_one_81162125843606155545104998607900118769099783 pow_div_prime_ne_one_81162125843606155545104998607900118769099783

private theorem pow_card_sub_one_26935696298915610574513298451669528361624243820491956655650666425177 :
    ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177) ^ (26935696298915610574513298451669528361624243820491956655650666425177 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 26935696298915610574513298451669528361624243820491956655650666425177 224 3 (26935696298915610574513298451669528361624243820491956655650666425177 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_26935696298915610574513298451669528361624243820491956655650666425177 :
    ∀ q : Nat, q.Prime → q ∣ 26935696298915610574513298451669528361624243820491956655650666425177 - 1 →
      ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177) ^ ((26935696298915610574513298451669528361624243820491956655650666425177 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 26935696298915610574513298451669528361624243820491956655650666425177 - 1 = 2 ^ 3 * (13 * (37 * (86246152412150184989 * (81162125843606155545104998607900118769099783)))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 224 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 224 3 13 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 37 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 224 3 37 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 86246152412150184989 prime_86246152412150184989 h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 224 3 86246152412150184989 (by decide) (by decide)
  · obtain rfl := heq 81162125843606155545104998607900118769099783 prime_81162125843606155545104998607900118769099783 hdvd
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 224 3 81162125843606155545104998607900118769099783 (by decide) (by decide)

/-- Pratt-tree node: `26935696298915610574513298451669528361624243820491956655650666425177` is prime (witness `3`). -/
private theorem prime_26935696298915610574513298451669528361624243820491956655650666425177 : Nat.Prime 26935696298915610574513298451669528361624243820491956655650666425177 :=
  lucas_primality 26935696298915610574513298451669528361624243820491956655650666425177 ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177)
    pow_card_sub_one_26935696298915610574513298451669528361624243820491956655650666425177 pow_div_prime_ne_one_26935696298915610574513298451669528361624243820491956655650666425177

private theorem pow_card_sub_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :
    ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297) ^ (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :
    ∀ q : Nat, q.Prime → q ∣ 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1 →
      ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297) ^ ((4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1 = 2 ^ 3 * (373 * (8329 * (37501 * (661873 * (12211063 * (1402724681 * (16297965815447 * (26935696298915610574513298451669528361624243820491956655650666425177)))))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 373 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 373 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 8329 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 8329 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 37501 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 37501 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 661873 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 661873 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 12211063 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 12211063 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 1402724681 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 1402724681 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 16297965815447 prime_16297965815447 h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 16297965815447 (by decide) (by decide)
  · obtain rfl := heq 26935696298915610574513298451669528361624243820491956655650666425177 prime_26935696298915610574513298451669528361624243820491956655650666425177 hdvd
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 381 3 26935696298915610574513298451669528361624243820491956655650666425177 (by decide) (by decide)

/-- Pratt-tree node: `4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297` is prime (witness `3`). -/
private theorem prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : Nat.Prime 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :=
  lucas_primality 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297)
    pow_card_sub_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 pow_div_prime_ne_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297

private theorem pow_card_sub_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 :
    ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 :
    ∀ q : Nat, q.Prime → q ∣ 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 →
      ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ ((402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 = 2 ^ 4 * (3 * (11 * (631 * (4920833 * (52872661 * (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297)))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 631 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 631 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 4920833 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 4920833 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52872661 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 52872661 (by decide) (by decide)
  · obtain rfl := heq 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 hdvd
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 448 13 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 (by decide) (by decide)

/-- Pratt-tree node: `402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249` is prime (witness `13`). -/
private theorem prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : Nat.Prime 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 :=
  lucas_primality 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249)
    pow_card_sub_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 pow_div_prime_ne_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-- The largest prime factor of the `G2` cofactor (448 bits). -/
abbrev q : Nat :=
  402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-- `q` is prime, by a Pratt tree of Lucas certificates. -/
theorem q_prime : Nat.Prime q :=
  prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-! ## The order of the curve -/

/-- Encode a curve point as `none` (infinity) or its `x` with the sign bit of its `y`. -/
private noncomputable def pointCode : curve.toAffine.Point → Option (Fp2 × Bool)
  | .zero => none
  | .some x y _ => some (x, Fp2.signBit y)

private theorem pointCode_injective : Function.Injective pointCode := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hc
  · rfl
  · cases hc
  · cases hc
  · simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, hs⟩ := hc
    have e1 := (Affine.equation_iff _ _).mp h.1
    have e2 := (Affine.equation_iff _ _).mp h'.1
    have hy : y' = y ∨ y' = -y := by
      have : (y' - y) * (y' + y) = 0 := by
        simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
          show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
          show curve.a₆ = bTwist from rfl] at e1 e2
        linear_combination e2 - e1
      rcases mul_eq_zero.mp this with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases hy with rfl | rfl
    · rfl
    · rw [Affine.Point.some.injEq]
      refine ⟨rfl, ?_⟩
      by_contra hne
      have hy0 : y ≠ 0 := fun h0 => hne (by rw [h0, neg_zero])
      have hneg := Fp2.signBit_neg hy0
      have := hs.trans hneg
      cases hb : Fp2.signBit y <;> rw [hb] at this <;> exact absurd this (by decide)

/-- The twist curve has finitely many points. -/
instance finite_point : Finite curve.toAffine.Point :=
  Finite.of_injective pointCode pointCode_injective

/-- The twist curve has at most `2p² + 1` points. -/
theorem card_point_le : Nat.card curve.toAffine.Point ≤ 2 * Fp.modulus ^ 2 + 1 := by
  have h := Nat.card_le_card_of_injective _ pointCode_injective
  rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, Fintype.card_prod,
    Fp2.card_eq, Fintype.card_bool] at h
  omega

/-- The twist curve has fewer than `r² · q` points. -/
theorem card_point_lt_rrq : Nat.card curve.toAffine.Point < Fr.modulus * Fr.modulus * q := by
  have h := card_point_le
  have hlt : 2 * Fp.modulus ^ 2 + 1 < Fr.modulus * Fr.modulus * q := by decide
  omega

/-! ## A point of order `q` -/

/-- A point of order `q` on the twist, in affine coordinates. -/
def P1 : G2 :=
  ⟨⟨Fp.ofNat 0xffd5c7041594275710810912f235d186a22fbb5433a8e60b514da2bcb92a91ab996b90fee5916ff94feeb24500f5717,
    Fp.ofNat 0x754ea28f6cdfe1c0852776f2806261cd6d0ee0b5a41856e67850e23f8b9f2ae2c2a714a83d44264b9690444ad2dd925⟩,
   ⟨Fp.ofNat 0x195a84dedaff659d2b408c0afbc06f860cac7f6f974e6dea31394c600236c4bcfb34e597e8312b5e2b93dc85cff852ce,
    Fp.ofNat 0xb34aaa1ac510f29f9f993112f20698e9d669d6a48fe7e2937d86d6680e641fcbb27902586329e5f0cb3941e6aa58cd9⟩,
   Fp2.one⟩

private theorem P1_curve : P1.y * P1.y = P1.x * P1.x * P1.x + bTwist := by decide

/-- `P1` is a valid curve point. -/
theorem valid_P1 : Valid P1 := valid_affine P1_curve

private theorem P1_z_ne : P1.isInfinity = false := by decide

/-- `P1` is not the point at infinity. -/
theorem toPoint_P1_ne_zero : toPoint P1 ≠ 0 := fun h =>
  absurd ((isInfinity_iff valid_P1).mpr h) (by rw [P1_z_ne]; decide)

/-- The ladder `[q]P1` ends at the point at infinity (kernel computation). -/
private theorem mulMsb_P1_isInfinity : (mulMsb P1 q 447 P1).isInfinity = true := by
  decide +kernel

/-- `[q]P1 = 0`. -/
theorem q_smul_P1 : q • toPoint P1 = 0 := by
  have h := (isInfinity_iff (valid_mulMsb valid_P1 valid_P1 q 447)).mp mulMsb_P1_isInfinity
  rw [toPoint_mulMsb valid_P1 valid_P1, ← add_nsmul] at h
  have e : 2 ^ 447 + q % 2 ^ 447 = q := by decide
  rwa [e] at h

end EthLibImpl.Cryptography.Bls.Mirror.G2
