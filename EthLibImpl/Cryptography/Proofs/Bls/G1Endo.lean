import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Group
import EthLib.Cryptography.Proofs.Bls.G1Order
import EthLib.Cryptography.Proofs.Bls.FrZMod
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Endomorphism
import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan

/-!
# Proofs: the endomorphism subgroup test for `G1`

The implementation decides `G1` subgroup membership (`[r]P = O`) with the
GLV endomorphism test `σ(P) = -[|x|]([|x|]P)`. The spec's `G1.inSubgroup`
is the same test, written with the spec's `sigma`, `projectiveEq` and
`mulNat · blsX`, and the spec's proofs (`G1Endomorphism`,
`G1SubgroupSpan`) show it decides `[r]P = O`. This file restates the
implementation's version at the level of spec types (`G1` triples over
spec `Fp`) and reduces it to the spec's; the implementation's own field is
mapped onto these definitions elsewhere.

* `endo`, `eqProj`, `mulMsb`, `mulAbsX`: spec-level copies of the
  implementation's definitions (`EthLibImpl/Cryptography/Bls/G1.lean`).
* `SpecG1.endo_eq_sigma`, `SpecG1.eqProj_eq_projectiveEq`: `endo` is the
  spec's `sigma` (with `β` on the other side of the product), and `eqProj`
  is the spec's `projectiveEq` (up to the association of `z³`).
* `toPoint_endo`: `endo` computes the spec's `sigmaHom`.
* `eqProj_iff`: `eqProj` decides equality of the denoted points.
* `toPoint_mulMsb`, `toPoint_mulAbsX`: the MSB-first ladder computes
  `[2ⁿ]acc + [k mod 2ⁿ]P`, so `mulAbsX` multiplies by `|x|`.
* `inSubgroup_iff_endo`: the main theorem, `[r]P = O` iff
  `σ(P) = -[x²]P`, from the spec's `modulus_smul_eq_zero_of_sigmaHom` and
  `sigmaHom_of_modulus_smul_eq_zero`.
* `SpecG1.inSubgroup_eq_endo`: the spec's `G1.inSubgroup` is the
  implementation's test, on valid points.
-/

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian

/-- `σ(x, y) = (β·x, y)`, in Jacobian coordinates `(X·β, Y, Z)`. The spec's
`sigma` multiplies on the other side. -/
def endo (P : G1) : G1 := ⟨P.x * beta, P.y, P.z⟩

/-- Whether two triples stand for the same point. -/
def eqProj (P Q : G1) : Bool :=
  if P.z.isZero then Q.z.isZero
  else if Q.z.isZero then false
  else
    let z1z1 := P.z * P.z
    let z2z2 := Q.z * Q.z
    (P.x * z2z2).beq (Q.x * z1z1) && (P.y * (Q.z * z2z2)).beq (Q.y * (P.z * z1z1))

/-- `[2ⁿ]acc + [k mod 2ⁿ]P`, consuming the low `n` bits of `k` most
significant first. -/
def mulMsb (P : G1) (k : Nat) : Nat → G1 → G1
  | 0, acc => acc
  | n + 1, acc =>
    let acc := double acc
    mulMsb P k n (if k.testBit n then add acc P else acc)

/-- `[|x|]P` for the BLS parameter `x = -0xd201000000010000` (its top bit
is consumed by starting the ladder at `P`). -/
def mulAbsX (P : G1) : G1 := mulMsb P 0xd201000000010000 63 P

private theorem mulMsb_succ (P : G1) (k n : Nat) (acc : G1) :
    mulMsb P k (n + 1) acc
      = mulMsb P k n (if k.testBit n then add (double acc) P else double acc) := rfl

end EthLib.Cryptography.Bls.G1

namespace EthLibImpl.Cryptography.Bls.SpecG1

open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.G1
open scoped EthLib.Cryptography.Bls.Fp

/-- `endo` is the spec's `sigma`: they differ only in the order of the
product `X·β`. -/
theorem endo_eq_sigma (P : G1) : endo P = sigma P := by
  have h : P.x * beta = beta * P.x := mul_comm _ _
  rw [endo, h]
  rfl

/-- `eqProj` is the spec's `projectiveEq`: they differ only in how `z³` is
associated. -/
theorem eqProj_eq_projectiveEq (P Q : G1) : eqProj P Q = projectiveEq P Q := by
  have hp : P.z * (P.z * P.z) = P.z * P.z * P.z := (mul_assoc _ _ _).symm
  have hq : Q.z * (Q.z * Q.z) = Q.z * Q.z * Q.z := (mul_assoc _ _ _).symm
  simp only [eqProj, projectiveEq, Fp.baseField_isZero, Fp.baseField_beq, hp, hq]

end EthLibImpl.Cryptography.Bls.SpecG1

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian
open EthLibImpl.Cryptography.Bls.SpecG1 (endo_eq_sigma eqProj_eq_projectiveEq)

/-! ## `endo` on spec triples -/

/-- `endo` unfolded to an explicit triple. -/
theorem endo_eq (P : G1) : endo P = ⟨P.x * beta, P.y, P.z⟩ := rfl

/-- The `X` coordinate of `endo P` is `β·X`. -/
theorem rep_endo_x (P : G1) : rep (endo P) 0 = betaZ * rep P 0 := by
  rw [endo_eq_sigma, rep_sigma, Matrix.cons_val_zero]

/-- `endo` keeps `Y`. -/
theorem rep_endo_y (P : G1) : rep (endo P) 1 = rep P 1 := by
  rw [endo_eq_sigma, rep_sigma, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- `endo` keeps `Z`. -/
theorem rep_endo_z (P : G1) : rep (endo P) 2 = rep P 2 := by
  rw [endo_eq_sigma, rep_sigma, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `endo` preserves validity. -/
theorem valid_endo {P : G1} (h : Valid P) : Valid (endo P) := by
  rw [endo_eq_sigma]
  exact valid_sigma h

/-- `endo` computes `σ` on the points spec triples denote. -/
theorem toPoint_endo {P : G1} (h : Valid P) : toPoint (endo P) = sigmaHom (toPoint P) := by
  rw [endo_eq_sigma]
  exact toPoint_sigma h

/-! ## `eqProj` decides equality of the denoted points -/

/-- A valid triple is the point at infinity exactly when it denotes `0`. -/
theorem isInfinity_iff {P : G1} (hP : Valid P) : P.isInfinity = true ↔ toPoint P = 0 :=
  isInfinity_eq_true_iff_toPoint_eq_zero hP

/-- `eqProj` decides whether two valid triples denote the same point. -/
theorem eqProj_iff {P Q : G1} (hP : Valid P) (hQ : Valid Q) :
    eqProj P Q = true ↔ toPoint P = toPoint Q := by
  rw [eqProj_eq_projectiveEq]
  exact projectiveEq_eq_true_iff_toPoint_eq hP hQ

/-! ## Most-significant-bit-first scalar multiplication -/

/-- `mulMsb` preserves validity. -/
theorem valid_mulMsb {P acc : G1} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
    Valid (mulMsb P k n acc) := by
  induction n generalizing acc with
  | zero => exact hacc
  | succ n ih =>
    rw [mulMsb_succ]
    apply ih
    split
    · exact valid_add (valid_double hacc) hP
    · exact valid_double hacc

private theorem mod_two_pow_succ' (k n : Nat) :
    k % 2 ^ (n + 1) = (if k.testBit n then 2 ^ n else 0) + k % 2 ^ n := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_two_eq_zero_or_one (k / 2 ^ n)
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; simp; omega

/-- MSB-first ladder: `mulMsb P k n acc = [2ⁿ]acc + [k mod 2ⁿ]P`. -/
theorem toPoint_mulMsb {P acc : G1} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
    toPoint (mulMsb P k n acc) = 2 ^ n • toPoint acc + (k % 2 ^ n) • toPoint P := by
  induction n generalizing acc with
  | zero =>
    rw [pow_zero, Nat.mod_one, one_nsmul, zero_nsmul, add_zero]
    rfl
  | succ n ih =>
    rw [mulMsb_succ]
    have hv : Valid (if k.testBit n then add (double acc) P else double acc) := by
      split
      · exact valid_add (valid_double hacc) hP
      · exact valid_double hacc
    rw [ih hv, mod_two_pow_succ']
    by_cases hb : k.testBit n = true
    · rw [ite_eq_left hb, ite_eq_left hb, toPoint_add (valid_double hacc) hP, toPoint_double hacc]
      module
    · rw [ite_eq_right hb, ite_eq_right hb, toPoint_double hacc]
      module

/-- `mulAbsX` preserves validity. -/
theorem valid_mulAbsX {P : G1} (hP : Valid P) : Valid (mulAbsX P) :=
  valid_mulMsb hP hP _ _

/-- `mulAbsX` multiplies by `|x| = 0xd201000000010000`. -/
theorem toPoint_mulAbsX {P : G1} (hP : Valid P) :
    toPoint (mulAbsX P) = 0xd201000000010000 • toPoint P := by
  rw [mulAbsX, toPoint_mulMsb hP hP, ← add_nsmul]
  rfl

/-! ## The subgroup test -/

set_option linter.unusedVariables false in
/-- The endomorphism subgroup test decides `[r]P = O`: for a valid,
finite `P`, `[r]P` is the point at infinity iff `σ(P) = -[|x|]([|x|]P)`.
(`hz` is not needed for the equivalence; both sides are `true` at infinity.) -/
theorem inSubgroup_iff_endo {P : G1} (hP : Valid P) (hz : ¬ P.z.isZero = true) :
    (mulNat P Fr.modulus).isInfinity = eqProj (endo P) (neg (mulAbsX (mulAbsX P))) := by
  have hx := valid_mulAbsX (valid_mulAbsX hP)
  rw [Bool.eq_iff_iff, isInfinity_iff (valid_mulNat hP _), toPoint_mulNat hP,
    eqProj_iff (valid_endo hP) (valid_neg hx), toPoint_endo hP, toPoint_neg hx,
    toPoint_mulAbsX (valid_mulAbsX hP), toPoint_mulAbsX hP, smul_smul,
    show (0xd201000000010000 : ℕ) = blsX from rfl]
  exact ⟨sigmaHom_of_modulus_smul_eq_zero, modulus_smul_eq_zero_of_sigmaHom⟩

end EthLib.Cryptography.Bls.G1

namespace EthLibImpl.Cryptography.Bls.SpecG1

open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.G1

/-- On a valid triple, the spec's form of the endomorphism test (`sigma`,
`projectiveEq`, `mulNat · blsX`) is the implementation's (`endo`, `eqProj`,
`mulAbsX`). -/
theorem projectiveEq_sigma_eq_eqProj_endo {P : G1} (hP : Valid P) :
    projectiveEq (sigma P) (neg (mulNat (mulNat P blsX) blsX))
      = eqProj (endo P) (neg (mulAbsX (mulAbsX P))) := by
  have hv := valid_mulNat (valid_mulNat hP blsX) blsX
  have hx := valid_mulAbsX (valid_mulAbsX hP)
  rw [Bool.eq_iff_iff, projectiveEq_eq_true_iff_toPoint_eq (valid_sigma hP) (valid_neg hv),
    eqProj_iff (valid_endo hP) (valid_neg hx), toPoint_sigma hP, toPoint_endo hP,
    toPoint_neg hv, toPoint_neg hx, toPoint_mulNat (valid_mulNat hP blsX),
    toPoint_mulNat hP, toPoint_mulAbsX (valid_mulAbsX hP), toPoint_mulAbsX hP,
    show (0xd201000000010000 : ℕ) = blsX from rfl]

/-- On a valid triple, the spec's subgroup check is the implementation's
endomorphism test. -/
theorem inSubgroup_eq_endo {P : G1} (hP : Valid P) :
    inSubgroup P = if P.isInfinity then true else eqProj (endo P) (neg (mulAbsX (mulAbsX P))) := by
  rw [inSubgroup, projectiveEq_sigma_eq_eqProj_endo hP]

end EthLibImpl.Cryptography.Bls.SpecG1
