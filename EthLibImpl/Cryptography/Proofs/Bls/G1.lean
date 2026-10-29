import EthLibImpl.Cryptography.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.Fp
import EthLibImpl.Cryptography.Proofs.Bls.FpInv
import EthLibImpl.Cryptography.Proofs.Bls.G1Endo
import EthLib.Cryptography.Proofs.Bls.G1Group

/-!
# Proofs: the implementation's `G1` computes the spec's `G1`

For canonical inputs every operation of `EthLibImpl.Cryptography.Bls.G1`
returns the spec's triple, component by component through `Fp.val`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls.G1

open EthLib.Cryptography.Bls.Fp (toZMod toZMod_add toZMod_sub toZMod_neg toZMod_mul toZMod_zero
  toZMod_one toZMod_ofNat toZMod_pow)

open private mulMsb_succ from EthLibImpl.Cryptography.Proofs.Bls.G1Endo

local notation "SFp" => EthLib.Cryptography.Bls.Fp
local notation "SG1" => EthLib.Cryptography.Bls.G1

/-- All three coordinates are canonical field elements. -/
def Canonical (p : G1) : Prop := p.x.Canonical ∧ p.y.Canonical ∧ p.z.Canonical

/-- The spec triple a canonical implementation point stands for. -/
def toSpec (p : G1) : SG1 := ⟨p.x.val, p.y.val, p.z.val⟩

theorem isZero_eq {a : Fp} (ha : a.Canonical) : a.isZero = (a.val).isZero := by
  rw [Bool.eq_iff_iff, Fp.isZero_iff ha]
  unfold EthLib.Cryptography.Bls.Fp.isZero
  rw [beq_iff_eq]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

theorem beq_eq {a b : Fp} (ha : a.Canonical) (hb : b.Canonical) :
    a.beq b = EthLib.Cryptography.Bls.Fp.beq a.val b.val := by
  rw [Bool.eq_iff_iff, Fp.beq_iff ha hb, EthLib.Cryptography.Bls.Fp.beq_eq_true_iff]

/-! Spec-level identities for the replaced constant multiplications. -/

theorem two_mul' (a : SFp) : EthLib.Cryptography.Bls.Fp.ofNat 2 * a = a + a := by
  apply toZMod.injective
  simp only [toZMod_mul, toZMod_add, toZMod_ofNat]; push_cast; ring

theorem three_mul' (a : SFp) : EthLib.Cryptography.Bls.Fp.ofNat 3 * a = a + a + a := by
  apply toZMod.injective
  simp only [toZMod_mul, toZMod_add, toZMod_ofNat]; push_cast; ring

theorem eight_mul' (a : SFp) : EthLib.Cryptography.Bls.Fp.ofNat 8 * a = (a + a) + (a + a) + ((a + a) + (a + a)) := by
  apply toZMod.injective
  simp only [toZMod_mul, toZMod_add, toZMod_ofNat]; push_cast; ring


theorem toSpec_mk (x y z : Fp) : toSpec ⟨x, y, z⟩ = ⟨x.val, y.val, z.val⟩ := rfl

theorem canonical_mk {x y z : Fp} : Canonical ⟨x, y, z⟩ ↔ x.Canonical ∧ y.Canonical ∧ z.Canonical :=
  Iff.rfl

section fpsimp

variable {a b : Fp}

theorem mul_c (hb : b.Canonical) : (a * b).Canonical := Fp.mul_canonical a hb
theorem mul_v (hb : b.Canonical) : (a * b).val = a.val * b.val := Fp.val_mul a hb
theorem add_c (ha : a.Canonical) (hb : b.Canonical) : (a + b).Canonical := Fp.add_canonical ha hb
theorem add_v (ha : a.Canonical) (hb : b.Canonical) : (a + b).val = a.val + b.val := Fp.val_add ha hb
theorem sub_c (ha : a.Canonical) (hb : b.Canonical) : (a - b).Canonical := Fp.sub_canonical ha hb
theorem sub_v (ha : a.Canonical) (hb : b.Canonical) : (a - b).val = a.val - b.val := Fp.val_sub ha hb
theorem neg_c (ha : a.Canonical) : (-a).Canonical := Fp.neg_canonical ha
theorem neg_v (ha : a.Canonical) : (-a).val = -a.val := Fp.val_neg ha
theorem sqr_c (ha : a.Canonical) : (a.sqr).Canonical := Fp.sqr_canonical ha
theorem sqr_v (ha : a.Canonical) : (a.sqr).val = a.val * a.val := Fp.val_sqr ha
theorem dbl_c (ha : a.Canonical) : (a.double).Canonical := Fp.double_canonical ha
theorem dbl_v (ha : a.Canonical) : (a.double).val = a.val + a.val := Fp.val_double ha

end fpsimp

theorem toSpec_x (p : G1) : (toSpec p).x = p.x.val := rfl
theorem toSpec_y (p : G1) : (toSpec p).y = p.y.val := rfl
theorem toSpec_z (p : G1) : (toSpec p).z = p.z.val := rfl

private theorem fp_sqr_eq (a : Fp) : a.sqr = Fp.mulI a a := rfl
private theorem fp_mul_eq (a b : Fp) : a * b = Fp.mulI a b := rfl
private theorem fp_add_eq (a b : Fp) : a + b = Fp.addI a b := rfl
private theorem fp_sub_eq (a b : Fp) : a - b = Fp.subI a b := rfl
private theorem fp_double_eq (a : Fp) : a.double = Fp.addI a a := rfl

/-- `double` is the old operator-notation body: its inlined `Fp.mulI`/`Fp.addI`/…
are those operators by definition. -/
theorem double_eq_spec_form (p : G1) : double p =
    if p.z.isZero then p else
      let A := p.x.sqr
      let B := p.y.sqr
      let C := B.sqr
      let D := ((p.x + B).sqr - A - C).double
      let E := A.double + A
      let F := E.sqr
      let x' := F - D.double
      let y' := E * (D - x') - C.double.double.double
      let z' := (p.y * p.z).double
      ⟨x', y', z'⟩ := by
  unfold double
  simp (config := {zeta := false}) only [fp_sqr_eq, fp_mul_eq, fp_add_eq, fp_sub_eq, fp_double_eq, Fp.doubleI]
  rfl

theorem double_spec {p : G1} (hp : Canonical p) :
    Canonical (double p) ∧ toSpec (double p) = EthLib.Cryptography.Bls.G1.double (toSpec p) := by
  have hs : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hp.2.2).symm
  rw [double_eq_spec_form]
  unfold EthLib.Cryptography.Bls.G1.double
  rw [hs]
  by_cases h : p.z.isZero = true
  · rw [if_pos h, if_pos h]
    exact ⟨hp, rfl⟩
  · rw [if_neg h, if_neg h]
    obtain ⟨hx, hy, hz⟩ := hp
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y, toSpec_z, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hx, hy, hz]
    rw [EthLib.Cryptography.Bls.G1.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> apply toZMod.injective <;>
      simp only [toZMod_add, toZMod_sub, toZMod_mul, toZMod_ofNat] <;> push_cast <;> ring


theorem spec_mul_one (a : SFp) : a * 1 = a := by
  apply toZMod.injective
  simp only [toZMod_mul, toZMod_one]; ring

theorem spec_one_mul (a : SFp) : 1 * a = a := by
  apply toZMod.injective
  simp only [toZMod_mul, toZMod_one]; ring

theorem zero_canonical : Canonical zero :=
  ⟨Fp.one_canonical, Fp.one_canonical, Fp.zero_canonical⟩

theorem toSpec_zero : toSpec zero = EthLib.Cryptography.Bls.G1.zero := by
  show (⟨Fp.one.val, Fp.one.val, Fp.zero.val⟩ : SG1) = _
  rw [Fp.val_one, Fp.val_zero]; rfl

theorem add_spec {p q : G1} (hp : Canonical p) (hq : Canonical q) :
    Canonical (add p q) ∧
      toSpec (add p q) = EthLib.Cryptography.Bls.G1.add (toSpec p) (toSpec q) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  have hsp : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hpz).symm
  have hsq : (toSpec q).z.isZero = q.z.isZero := (isZero_eq hqz).symm
  unfold add EthLib.Cryptography.Bls.G1.add
  rw [hsp, hsq]
  by_cases hp0 : p.z.isZero = true
  · rw [if_pos hp0, if_pos hp0]
    exact ⟨⟨hqx, hqy, hqz⟩, rfl⟩
  rw [if_neg hp0, if_neg hp0]
  by_cases hq0 : q.z.isZero = true
  · rw [if_pos hq0, if_pos hq0]
    exact ⟨⟨hpx, hpy, hpz⟩, rfl⟩
  rw [if_neg hq0, if_neg hq0]
  by_cases hq1 : q.z.beq Fp.one = true
  · have hq1v : q.z.val = 1 := by
      rw [← Fp.val_one]; exact (Fp.beq_iff hqz Fp.one_canonical).mp hq1
    simp (config := {maxDischargeDepth := 40}) only [hq1, if_true, toSpec_mk, toSpec_x, toSpec_y, toSpec_z, hq1v, spec_mul_one, spec_one_mul, Fp.val_one, Fp.one_canonical, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
    split_ifs with c1 c2
    · exact double_spec ⟨hpx, hpy, hpz⟩
    · exact ⟨zero_canonical, toSpec_zero⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y, toSpec_z, hq1v, spec_mul_one, spec_one_mul, Fp.val_one, Fp.one_canonical, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
      rw [EthLib.Cryptography.Bls.G1.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> apply toZMod.injective <;>
        simp only [toZMod_add, toZMod_sub, toZMod_mul, toZMod_ofNat, toZMod_one] <;> push_cast <;> ring
  · have hq1' : q.z.beq Fp.one = false := by simpa using hq1
    simp (config := {maxDischargeDepth := 40}) only [hq1', Bool.false_eq_true, if_false, ↓reduceIte, toSpec_mk, toSpec_x, toSpec_y, toSpec_z, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
    split_ifs with c1 c2
    · exact double_spec ⟨hpx, hpy, hpz⟩
    · exact ⟨zero_canonical, toSpec_zero⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y, toSpec_z, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
      rw [EthLib.Cryptography.Bls.G1.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> apply toZMod.injective <;>
        simp only [toZMod_add, toZMod_sub, toZMod_mul, toZMod_ofNat, toZMod_one] <;> push_cast <;> ring


/-- `generator` computes the spec's. -/
theorem generator_spec :
    Canonical generator ∧ toSpec generator = EthLib.Cryptography.Bls.G1.generator := by
  refine ⟨⟨Fp.ofNat_canonical _, Fp.ofNat_canonical _, Fp.one_canonical⟩, ?_⟩
  simp only [toSpec, generator, EthLib.Cryptography.Bls.G1.generator, Fp.val_ofNat, Fp.val_one]
  rfl

/-- `zero` computes the spec's. -/
theorem zero_spec : Canonical zero ∧ toSpec zero = EthLib.Cryptography.Bls.G1.zero :=
  ⟨zero_canonical, toSpec_zero⟩

/-- The infinity test agrees. -/
theorem isInfinity_spec {p : G1} (hp : Canonical p) :
    p.isInfinity = (toSpec p).isInfinity :=
  isZero_eq hp.2.2

/-- `neg` computes the spec's. -/
theorem neg_spec {p : G1} (hp : Canonical p) :
    Canonical (neg p) ∧ toSpec (neg p) = EthLib.Cryptography.Bls.G1.neg (toSpec p) := by
  obtain ⟨hx, hy, hz⟩ := hp
  have e : neg p = ⟨p.x, -p.y, p.z⟩ := rfl
  rw [e]
  refine ⟨canonical_mk.mpr ⟨hx, neg_c hy, hz⟩, ?_⟩
  simp only [EthLib.Cryptography.Bls.G1.neg, toSpec_mk, toSpec_x, toSpec_y, toSpec_z, neg_v hy]

theorem spec_inverse_one : EthLib.Cryptography.Bls.Fp.inverse 1 = 1 := by
  apply toZMod.injective
  unfold EthLib.Cryptography.Bls.Fp.inverse
  rw [EthLib.Cryptography.Bls.Fp.powNat_eq_monoid_pow, toZMod_pow, toZMod_one, one_pow]

/-- `toAffine` computes the spec's, coordinate by coordinate. -/
theorem toAffine_spec {p : G1} (hp : Canonical p) :
    p.toAffine.1.Canonical ∧ p.toAffine.2.Canonical ∧
      (p.toAffine.1.val, p.toAffine.2.val) = (toSpec p).toAffine := by
  obtain ⟨hx, hy, hz⟩ := hp
  have hs : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hz).symm
  unfold toAffine EthLib.Cryptography.Bls.G1.toAffine
  rw [hs]
  by_cases h0 : p.z.isZero = true
  · rw [if_pos h0, if_pos h0]
    exact ⟨Fp.zero_canonical, Fp.zero_canonical, by rw [Fp.val_zero]; rfl⟩
  rw [if_neg h0, if_neg h0]
  by_cases h1 : p.z.beq Fp.one = true
  · have h1v : p.z.val = 1 := by
      rw [← Fp.val_one]; exact (Fp.beq_iff hz Fp.one_canonical).mp h1
    rw [if_pos h1]
    refine ⟨hx, hy, ?_⟩
    simp only [toSpec_z, toSpec_x, toSpec_y, h1v, spec_inverse_one, spec_mul_one, spec_one_mul]
  · rw [if_neg h1]
    have hi := Fp.inverse_canonical hz
    have hi2 := sqr_c hi
    have hi3 := mul_c (a := (p.z.inverse).sqr) hi
    refine ⟨mul_c (a := p.x) hi2, mul_c (a := p.y) hi3, ?_⟩
    simp (config := {maxDischargeDepth := 40}) only [toSpec_z, toSpec_x, toSpec_y, mul_v, sqr_v,
      Fp.val_inverse, hz, hi, hi2, hi3, hx, hy, mul_c, sqr_c]

/-- `mulNat` computes the spec's. -/
theorem mulNat_spec (k : Nat) : ∀ {p : G1}, Canonical p →
    Canonical (mulNat p k) ∧
      toSpec (mulNat p k) = EthLib.Cryptography.Bls.G1.mulNat (toSpec p) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp
    rw [mulNat, EthLib.Cryptography.Bls.G1.mulNat_def]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]; exact zero_spec
    rw [if_neg hk, if_neg hk]
    obtain ⟨hd, hds⟩ := double_spec hp
    obtain ⟨hh, hhs⟩ := ih (k / 2) (by omega) hd
    rw [← hds, ← hhs]
    by_cases hodd : k % 2 = 1
    · rw [if_pos hodd, if_pos hodd]
      exact add_spec hp hh
    · rw [if_neg hodd, if_neg hodd]
      exact ⟨hh, rfl⟩

/-- `mul` computes the spec's. -/
theorem mul_spec {p : G1} (hp : Canonical p) (s : EthLib.Cryptography.Bls.Fr) :
    Canonical (mul p s) ∧
      toSpec (mul p s) = EthLib.Cryptography.Bls.G1.mul (toSpec p) s :=
  mulNat_spec s.val hp


theorem beta_canonical : beta.Canonical := Fp.ofNat_canonical _

theorem val_beta : beta.val = EthLib.Cryptography.Bls.G1.beta := Fp.val_ofNat _

/-- `endo` computes the spec-level endomorphism. -/
theorem endo_spec {p : G1} (hp : Canonical p) :
    Canonical (endo p) ∧ toSpec (endo p) = EthLib.Cryptography.Bls.G1.endo (toSpec p) := by
  obtain ⟨hx, hy, hz⟩ := hp
  have e : endo p = ⟨p.x * beta, p.y, p.z⟩ := rfl
  rw [e]
  refine ⟨canonical_mk.mpr ⟨mul_c beta_canonical, hy, hz⟩, ?_⟩
  simp only [EthLib.Cryptography.Bls.G1.endo, toSpec_mk, toSpec_x, toSpec_y, toSpec_z,
    mul_v beta_canonical, val_beta]

/-- `eqProj` computes the spec-level test. -/
theorem eqProj_spec {p q : G1} (hp : Canonical p) (hq : Canonical q) :
    eqProj p q = EthLib.Cryptography.Bls.G1.eqProj (toSpec p) (toSpec q) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  unfold eqProj EthLib.Cryptography.Bls.G1.eqProj
  have hsp : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hpz).symm
  have hsq : (toSpec q).z.isZero = q.z.isZero := (isZero_eq hqz).symm
  rw [hsp]
  by_cases h0 : p.z.isZero = true
  · rw [if_pos h0, if_pos h0, hsq]
  rw [if_neg h0, if_neg h0, hsq]
  by_cases h1 : q.z.isZero = true
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  dsimp only
  simp (config := {maxDischargeDepth := 40}) only [toSpec_x, toSpec_y, toSpec_z, mul_v, sqr_v,
    mul_c, sqr_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]

theorem bit_spec (k : UInt64) (n : Nat) (hn : n < 64) :
    ((k >>> n.toUInt64) &&& 1 != 0) = k.toNat.testBit n := by
  have h1 : (k >>> n.toUInt64).toNat = k.toNat >>> n := by
    rw [UInt64.toNat_shiftRight]
    have : n.toUInt64.toNat = n := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hn (by decide))]
    rw [this, Nat.mod_eq_of_lt hn]
  have h2 : ((k >>> n.toUInt64) &&& 1).toNat = (k.toNat >>> n) &&& 1 := by
    rw [UInt64.toNat_and, h1]; rfl
  have key : ∀ v : UInt64, (v != 0) = true ↔ v.toNat ≠ 0 := by
    intro v
    rw [bne_iff_ne, ne_eq, ne_eq, ← UInt64.toNat_inj]
    rfl
  rw [Nat.testBit, Bool.eq_iff_iff, key, bne_iff_ne, h2, Nat.and_comm]


/-- The most-significant-bit-first ladder computes the spec-level one, for up to 64 bits. -/
theorem mulMsb_spec {p : G1} (hp : Canonical p) (k : UInt64) (n : Nat) (hn : n ≤ 64) :
    ∀ {acc : G1}, Canonical acc →
      Canonical (mulMsb p k n acc) ∧
        toSpec (mulMsb p k n acc) =
          EthLib.Cryptography.Bls.G1.mulMsb (toSpec p) k.toNat n (toSpec acc) := by
  induction n with
  | zero => intro acc hacc; exact ⟨hacc, rfl⟩
  | succ n ih =>
    intro acc hacc
    have hn' : n ≤ 64 := by omega
    have hb := bit_spec k n (by omega)
    obtain ⟨hd, hds⟩ := double_spec hacc
    have e1 : mulMsb p k (n + 1) acc =
        mulMsb p k n (if (k >>> n.toUInt64) &&& 1 != 0 then add (double acc) p else double acc) := by
      rfl
    have e2 : EthLib.Cryptography.Bls.G1.mulMsb (toSpec p) k.toNat (n + 1) (toSpec acc) =
        EthLib.Cryptography.Bls.G1.mulMsb (toSpec p) k.toNat n
          (if k.toNat.testBit n then
            EthLib.Cryptography.Bls.G1.add (EthLib.Cryptography.Bls.G1.double (toSpec acc)) (toSpec p)
          else EthLib.Cryptography.Bls.G1.double (toSpec acc)) :=
      mulMsb_succ _ _ _ _
    rw [e1, e2, ← hb]
    by_cases hbit : ((k >>> n.toUInt64) &&& 1 != 0) = true
    · rw [if_pos hbit, if_pos hbit]
      obtain ⟨ha, has⟩ := add_spec hd hp
      obtain ⟨h1, h2⟩ := ih hn' ha
      rw [has, hds] at h2
      exact ⟨h1, h2⟩
    · rw [if_neg hbit, if_neg hbit]
      obtain ⟨h1, h2⟩ := ih hn' hd
      rw [hds] at h2
      exact ⟨h1, h2⟩

theorem absXWord_toNat : absXWord.toNat = 0xd201000000010000 := by decide

/-- `mulAbsX` computes the spec-level `[|x|]P`. -/
theorem mulAbsX_spec {p : G1} (hp : Canonical p) :
    Canonical (mulAbsX p) ∧
      toSpec (mulAbsX p) = EthLib.Cryptography.Bls.G1.mulAbsX (toSpec p) := by
  have := mulMsb_spec hp absXWord 63 (by omega) hp
  rw [absXWord_toNat] at this
  exact this


/-! ## `msm`

The implementation's `msm` and the spec's are the same program over two point types. Both are
restated as one generic function `Msm.msmGen`, parametrised by the point type and its operations
(`rfl`), and the generic function is shown to commute with `toSpec`, loop by loop.
-/

theorem forIn_list_sim {α β β' : Type} (l : List α) (inv : β → β' → Prop)
    (f : α → β → Id (ForInStep β)) (f' : α → β' → Id (ForInStep β'))
    (hstep : ∀ a ∈ l, ∀ b b', inv b b' → ∃ x x', f a b = .yield x ∧ f' a b' = .yield x' ∧ inv x x') :
    ∀ (init : β) (init' : β'), inv init init' →
      inv (forIn (m := Id) l init f) (forIn (m := Id) l init' f') := by
  induction l with
  | nil => intro init init' h; simpa using h
  | cons a l ih =>
    intro init init' h
    obtain ⟨x, x', hx, hx', hxx⟩ := hstep a (List.mem_cons_self) init init' h
    rw [List.forIn_cons, List.forIn_cons]
    simp only [hx, hx']
    exact ih (fun a ha => hstep a (List.mem_cons_of_mem _ ha)) x x' hxx

/-- Two `for` loops over `[:n]` in `Id` whose steps (which always continue) preserve a relation
end in related states. -/
theorem forIn_range_sim {β β' : Type} (inv : β → β' → Prop) (n : Nat)
    (f : Nat → β → Id (ForInStep β)) (f' : Nat → β' → Id (ForInStep β'))
    (hstep : ∀ i, i < n → ∀ b b', inv b b' →
      ∃ x x', f i b = .yield x ∧ f' i b' = .yield x' ∧ inv x x')
    (init : β) (init' : β') (h0 : inv init init') :
    inv (forIn (m := Id) [:n] init f) (forIn (m := Id) [:n] init' f') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_list_sim _ inv f f' ?_ init init' h0
  intro a ha
  rw [List.mem_range'_1] at ha
  exact hstep a (by simpa using ha.2)

namespace Msm

section generic
variable {G : Type} [Inhabited G] (zero : G) (dbl : G → G) (add : G → G → G)

def maxBitsOf (scalars : Array EthLib.Cryptography.Bls.Fr) (n : Nat) : Nat := Id.run do
  let mut maxBits : Nat := 0
  for j in [:n] do
    let v := scalars[j]!.val
    if v ≠ 0 then
      let bits := v.log2 + 1
      if bits > maxBits then maxBits := bits
  return maxBits

def fill (points : Array G) (scalars : Array EthLib.Cryptography.Bls.Fr) (n k : Nat) : Array G :=
  Id.run do
  let w := 8
  let bucketCount := 1 <<< w
  let mask : Nat := bucketCount - 1
  let mut buckets : Array G := Array.replicate bucketCount zero
  for j in [:n] do
    let v := (scalars[j]!.val >>> (k * w)) &&& mask
    if v ≠ 0 then
      buckets := buckets.set! v (add buckets[v]! points[j]!)
  return buckets

def windowSum (buckets : Array G) : G := Id.run do
  let w := 8
  let bucketCount := 1 <<< w
  let mut running : G := zero
  let mut partialSum : G := zero
  for vv in [:bucketCount - 1] do
    let v := bucketCount - 1 - vv
    running := add running buckets[v]!
    partialSum := add partialSum running
  return partialSum

def msmGen (points : Array G) (scalars : Array EthLib.Cryptography.Bls.Fr) : G := Id.run do
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  if n = 0 then return zero
  let w := 8
  let maxBits := maxBitsOf scalars n
  if maxBits = 0 then return zero
  let nWindows := (maxBits + w - 1) / w
  let mut acc : G := zero
  for kk in [:nWindows] do
    let k := nWindows - 1 - kk
    if k + 1 < nWindows then
      for _ in [:w] do
        acc := dbl acc
    acc := add acc (windowSum zero add (fill zero add points scalars n k))
  return acc

end generic

theorem msm_eq (points : Array G1) (scalars : Array EthLib.Cryptography.Bls.Fr) :
    G1.msm points scalars = msmGen G1.zero G1.double G1.add points scalars := rfl

theorem spec_msm_eq (points : Array SG1) (scalars : Array EthLib.Cryptography.Bls.Fr) :
    EthLib.Cryptography.Bls.G1.msm points scalars =
      msmGen EthLib.Cryptography.Bls.G1.zero EthLib.Cryptography.Bls.G1.double EthLib.Cryptography.Bls.G1.add points scalars := rfl

/-- Related bucket arrays: 256 canonical points and their images. -/
def BRel (bs : Array G1) (bs' : Array SG1) : Prop :=
  bs.size = 256 ∧ bs' = bs.map toSpec ∧ ∀ x ∈ bs, Canonical x

theorem map_getElem! (bs : Array G1) {i : Nat} (h : i < bs.size) :
    (bs.map toSpec)[i]! = toSpec bs[i]! := by
  rw [getElem!_pos (c := bs.map toSpec) i (by simpa using h), getElem!_pos (c := bs) i h,
    Array.getElem_map]

theorem fill_sim (P : Array G1) (hP : ∀ x ∈ P, Canonical x)
    (scalars : Array EthLib.Cryptography.Bls.Fr) (n k : Nat) (hn : n ≤ P.size) :
    BRel (fill G1.zero G1.add P scalars n k)
      (fill EthLib.Cryptography.Bls.G1.zero EthLib.Cryptography.Bls.G1.add (P.map toSpec) scalars n k) := by
  unfold fill
  simp only [Id.run, bind, pure]
  refine forIn_range_sim BRel n _ _ ?_ _ _ ?_
  · intro j hj b b' hb
    obtain ⟨hs, rfl, hc⟩ := hb
    generalize hv : (scalars[j]!).val >>> (k * 8) &&& 1 <<< 8 - 1 = v
    have hvlt : v < 256 := by
      rw [← hv]
      exact lt_of_le_of_lt (Nat.and_le_right) (by decide)
    by_cases h0 : v ≠ 0
    · simp only [if_pos h0]
      have hvb : v < b.size := hs ▸ hvlt
      have hjP : j < P.size := lt_of_lt_of_le hj hn
      have hcv : Canonical b[v]! := by
        rw [getElem!_pos b v hvb]; exact hc _ (Array.getElem_mem hvb)
      have hcj : Canonical P[j]! := by
        rw [getElem!_pos P j hjP]; exact hP _ (Array.getElem_mem hjP)
      obtain ⟨hac, has⟩ := add_spec hcv hcj
      refine ⟨_, _, rfl, rfl, ?_⟩
      rw [map_getElem! b hvb, map_getElem! P hjP, ← has]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hs
      · simp
      · intro x hx
        simp only [Array.set!_eq_setIfInBounds] at hx
        rcases Array.mem_or_eq_of_mem_setIfInBounds hx with h | h
        · exact hc x h
        · rw [h]; exact hac
    · simp only [if_neg h0]
      exact ⟨_, _, rfl, rfl, hs, rfl, hc⟩
  · refine ⟨by simp, by simp [toSpec_zero], ?_⟩
    intro x hx
    rw [Array.mem_replicate] at hx
    rw [hx.2]; exact zero_canonical

/-- A canonical implementation point and the spec point it stands for. -/
def PRel (p : G1) (q : SG1) : Prop := Canonical p ∧ toSpec p = q

theorem windowSum_sim {bs : Array G1} {bs' : Array SG1} (h : BRel bs bs') :
    PRel (windowSum G1.zero G1.add bs) (windowSum EthLib.Cryptography.Bls.G1.zero
      EthLib.Cryptography.Bls.G1.add bs') := by
  obtain ⟨hs, rfl, hc⟩ := h
  unfold windowSum
  simp only [Id.run, bind, pure]
  have := forIn_range_sim (fun (a : MProd G1 G1) (b : MProd SG1 SG1) => PRel a.fst b.fst ∧ PRel a.snd b.snd)
    (1 <<< 8 - 1) (fun vv r => ForInStep.yield ⟨G1.add r.fst (G1.add r.snd bs[1 <<< 8 - 1 - vv]!), G1.add r.snd bs[1 <<< 8 - 1 - vv]!⟩) (fun vv r => ForInStep.yield ⟨EthLib.Cryptography.Bls.G1.add r.fst (EthLib.Cryptography.Bls.G1.add r.snd (bs.map toSpec)[1 <<< 8 - 1 - vv]!), EthLib.Cryptography.Bls.G1.add r.snd (bs.map toSpec)[1 <<< 8 - 1 - vv]!⟩) ?_ ⟨G1.zero, G1.zero⟩ ⟨EthLib.Cryptography.Bls.G1.zero, EthLib.Cryptography.Bls.G1.zero⟩ ⟨⟨zero_canonical, toSpec_zero⟩, ⟨zero_canonical, toSpec_zero⟩⟩
  · exact this.1
  · intro vv hvv b b' hb
    obtain ⟨⟨hb1c, hb1⟩, ⟨hb2c, hb2⟩⟩ := hb
    have hi : 1 <<< 8 - 1 - vv < bs.size := by rw [hs]; omega
    have hcv : Canonical bs[1 <<< 8 - 1 - vv]! := by
      rw [getElem!_pos bs _ hi]; exact hc _ (Array.getElem_mem hi)
    beta_reduce
    rw [map_getElem! bs hi]
    obtain ⟨hr, hrs⟩ := add_spec hb2c hcv
    obtain ⟨hp, hps⟩ := add_spec hb1c hr
    refine ⟨_, _, rfl, rfl, ⟨hp, ?_⟩, ⟨hr, ?_⟩⟩
    · show toSpec _ = _
      rw [hps, hrs, hb1, hb2]
    · show toSpec _ = _
      rw [hrs, hb2]

theorem msmGen_sim (P : Array G1) (hP : ∀ x ∈ P, Canonical x)
    (scalars : Array EthLib.Cryptography.Bls.Fr) :
    PRel (msmGen G1.zero G1.double G1.add P scalars)
      (msmGen EthLib.Cryptography.Bls.G1.zero EthLib.Cryptography.Bls.G1.double
        EthLib.Cryptography.Bls.G1.add (P.map toSpec) scalars) := by
  unfold msmGen
  simp only [Id.run, bind, pure, Array.size_map]
  obtain ⟨n, hn, hnle⟩ : ∃ n, n = (if P.size ≤ scalars.size then P.size else scalars.size) ∧
      n ≤ P.size := ⟨_, rfl, by split <;> omega⟩
  rw [← hn]
  generalize maxBitsOf scalars n = mb
  by_cases hn0 : n = 0
  · rw [if_pos hn0, if_pos hn0]; exact ⟨zero_canonical, toSpec_zero⟩
  rw [if_neg hn0, if_neg hn0]
  by_cases hm0 : mb = 0
  · rw [if_pos hm0, if_pos hm0]; exact ⟨zero_canonical, toSpec_zero⟩
  rw [if_neg hm0, if_neg hm0]
  refine forIn_range_sim PRel _ _ _ ?_ _ _ ⟨zero_canonical, toSpec_zero⟩
  intro kk hkk b b' hb
  beta_reduce
  have hw := windowSum_sim (fill_sim P hP scalars n ((mb + 8 - 1) / 8 - 1 - kk) hnle)
  split_ifs with hcond
  · have hd : PRel (forIn (m := Id) [:8] b fun _ r => ForInStep.yield r.double) 
        (forIn (m := Id) [:8] b' fun _ r => ForInStep.yield r.double) := by
      refine forIn_range_sim PRel 8 _ _ ?_ _ _ hb
      intro i _ c c' hc
      obtain ⟨hcc, hcs⟩ := hc
      obtain ⟨hd1, hd2⟩ := double_spec hcc
      exact ⟨_, _, rfl, rfl, hd1, by rw [hd2, hcs]⟩
    obtain ⟨ha, has⟩ := add_spec hd.1 hw.1
    exact ⟨_, _, rfl, rfl, ha, by rw [has, hd.2, hw.2]⟩
  · obtain ⟨ha, has⟩ := add_spec hb.1 hw.1
    exact ⟨_, _, rfl, rfl, ha, by rw [has, hb.2, hw.2]⟩

end Msm

/-- `msm` computes the spec's, on the images of the points. -/
theorem msm_spec (points : Array G1) (hp : ∀ p ∈ points, Canonical p)
    (scalars : Array EthLib.Cryptography.Bls.Fr) :
    Canonical (msm points scalars) ∧
      toSpec (msm points scalars) =
        EthLib.Cryptography.Bls.G1.msm (points.map toSpec) scalars := by
  rw [Msm.msm_eq, Msm.spec_msm_eq]
  exact Msm.msmGen_sim points hp scalars

end EthLibImpl.Cryptography.Bls.G1
