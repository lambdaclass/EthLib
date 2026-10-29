import EthLibImpl.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.G2Defs
import EthLibImpl.Cryptography.Proofs.Bls.Fp2
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.G1
import EthLibImpl.Cryptography.Proofs.Bls.Fp

/-!
# Proofs: the implementation's `G2` computes the spec's `G2`

For canonical inputs every operation of `EthLibImpl.Cryptography.Bls.G2` returns the spec's
triple (the spec-level mirror's, for `mulMsb`, `mulAbsX` and `eqProj`), component by component
through `Fp2.toSpec`.

The file also covers the `Fp2` pieces the tower proofs skip: `sqrt` (against the spec-level
`sqrtAlt`), `batchInverse2`, `batchInverse4` (against the mirror's) and `Fp2.signBit`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls.G2

open scoped EthLib.Cryptography.Bls.Fp2

local notation "SFp2" => EthLib.Cryptography.Bls.Fp2
local notation "SG2" => EthLib.Cryptography.Bls.G2

theorem toSpec_mk (x y z : Fp2) : toSpec ⟨x, y, z⟩ = ⟨x.toSpec, y.toSpec, z.toSpec⟩ := rfl

theorem canonical_mk {x y z : Fp2} :
    Canonical ⟨x, y, z⟩ ↔ x.Canonical ∧ y.Canonical ∧ z.Canonical := Iff.rfl

theorem toSpec_x (p : G2) : (toSpec p).x = p.x.toSpec := rfl
theorem toSpec_y (p : G2) : (toSpec p).y = p.y.toSpec := rfl
theorem toSpec_z (p : G2) : (toSpec p).z = p.z.toSpec := rfl

/-! Spec-level identities for the replaced constant multiplications. -/

theorem ofFp_ofNat (n : Nat) : EthLib.Cryptography.Bls.Fp2.ofFp (EthLib.Cryptography.Bls.Fp.ofNat n) = (n : SFp2) := by
  apply EthLib.Cryptography.Bls.Fp2.ext
  · simp [EthLib.Cryptography.Bls.Fp2.natCast_c0]
  · simp [EthLib.Cryptography.Bls.Fp2.natCast_c1]

section fp2simp

variable {a b : Fp2}

theorem mul_c (ha : a.Canonical) (hb : b.Canonical) : (a * b).Canonical := Fp2.canonical_hMul ha hb
theorem mul_v (ha : a.Canonical) (hb : b.Canonical) : (a * b).toSpec = a.toSpec * b.toSpec :=
  Fp2.toSpec_hMul ha hb
theorem add_c (ha : a.Canonical) (hb : b.Canonical) : (a + b).Canonical := Fp2.canonical_hAdd ha hb
theorem add_v (ha : a.Canonical) (hb : b.Canonical) : (a + b).toSpec = a.toSpec + b.toSpec :=
  Fp2.toSpec_hAdd ha hb
theorem sub_c (ha : a.Canonical) (hb : b.Canonical) : (a - b).Canonical := Fp2.canonical_hSub ha hb
theorem sub_v (ha : a.Canonical) (hb : b.Canonical) : (a - b).toSpec = a.toSpec - b.toSpec :=
  Fp2.toSpec_hSub ha hb
theorem neg_c (ha : a.Canonical) : (-a).Canonical := Fp2.canonical_hNeg ha
theorem neg_v (ha : a.Canonical) : (-a).toSpec = -a.toSpec := Fp2.toSpec_hNeg ha
theorem sqr_c (ha : a.Canonical) : (a.sqr).Canonical := Fp2.sqr_canonical ha
theorem sqr_v (ha : a.Canonical) : (a.sqr).toSpec = a.toSpec * a.toSpec := Fp2.toSpec_sqr ha
theorem dbl_c (ha : a.Canonical) : (a.double).Canonical := Fp2.double_canonical ha
theorem dbl_v (ha : a.Canonical) : (a.double).toSpec = a.toSpec + a.toSpec := Fp2.toSpec_double ha

end fp2simp

theorem isZero_eq {a : Fp2} (ha : a.Canonical) : a.isZero = a.toSpec.isZero :=
  (Fp2.isZero_eq ha).symm

theorem beq_eq {a b : Fp2} (ha : a.Canonical) (hb : b.Canonical) :
    a.beq b = a.toSpec.beq b.toSpec := (Fp2.beq_eq ha hb).symm

theorem double_spec {p : G2} (hp : Canonical p) :
    Canonical (double p) ∧ toSpec (double p) = EthLib.Cryptography.Bls.G2.double (toSpec p) := by
  have hs : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hp.2.2).symm
  unfold double EthLib.Cryptography.Bls.G2.double
  rw [hs]
  by_cases h : p.z.isZero = true
  · rw [if_pos h, if_pos h]
    exact ⟨hp, rfl⟩
  · rw [if_neg h, if_neg h]
    obtain ⟨hx, hy, hz⟩ := hp
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    all_goals try dsimp only
    all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y, toSpec_z,
      mul_v, add_v, sub_v, neg_v, sqr_v, dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hx, hy, hz]
    rw [EthLib.Cryptography.Bls.G2.mk.injEq]
    simp only [ofFp_ofNat]
    generalize p.x.toSpec = X
    generalize p.y.toSpec = Y
    generalize p.z.toSpec = Z
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring


theorem spec_mul_one (a : SFp2) : a * EthLib.Cryptography.Bls.Fp2.one = a := by
  rw [EthLib.Cryptography.Bls.Fp2.one_def]; exact mul_one a

theorem spec_one_mul (a : SFp2) : EthLib.Cryptography.Bls.Fp2.one * a = a := by
  rw [EthLib.Cryptography.Bls.Fp2.one_def]; exact one_mul a

theorem zero_canonical : Canonical zero :=
  ⟨Fp2.one_canonical, Fp2.one_canonical, Fp2.zero_canonical⟩

theorem toSpec_zero : toSpec zero = EthLib.Cryptography.Bls.G2.zero := by
  show (⟨Fp2.toSpec Fp2.one, Fp2.toSpec Fp2.one, Fp2.toSpec Fp2.zero⟩ : SG2) = _
  rw [Fp2.toSpec_one, Fp2.toSpec_zero]; rfl

theorem add_spec {p q : G2} (hp : Canonical p) (hq : Canonical q) :
    Canonical (add p q) ∧
      toSpec (add p q) = EthLib.Cryptography.Bls.G2.add (toSpec p) (toSpec q) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  have hsp : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hpz).symm
  have hsq : (toSpec q).z.isZero = q.z.isZero := (isZero_eq hqz).symm
  unfold add EthLib.Cryptography.Bls.G2.add
  rw [hsp, hsq]
  by_cases hp0 : p.z.isZero = true
  · rw [if_pos hp0, if_pos hp0]
    exact ⟨⟨hqx, hqy, hqz⟩, rfl⟩
  rw [if_neg hp0, if_neg hp0]
  by_cases hq0 : q.z.isZero = true
  · rw [if_pos hq0, if_pos hq0]
    exact ⟨⟨hpx, hpy, hpz⟩, rfl⟩
  rw [if_neg hq0, if_neg hq0]
  by_cases hq1 : q.z.beq Fp2.one = true
  · have hq1v : q.z.toSpec = EthLib.Cryptography.Bls.Fp2.one := by
      rw [← Fp2.toSpec_one]; exact (Fp2.beq_iff hqz Fp2.one_canonical).mp hq1
    simp (config := {maxDischargeDepth := 40}) only [hq1, if_true, toSpec_mk, toSpec_x, toSpec_y,
      toSpec_z, hq1v, spec_mul_one, spec_one_mul, mul_v, add_v, sub_v, neg_v, sqr_v, dbl_v, mul_c, add_c, sub_c,
      neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq, Fp2.one_canonical,
      Fp2.toSpec_one]
    split_ifs with c1 c2
    · exact double_spec ⟨hpx, hpy, hpz⟩
    · exact ⟨zero_canonical, toSpec_zero⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y,
        toSpec_z, hq1v, spec_mul_one, spec_one_mul, mul_v, add_v, sub_v, neg_v, sqr_v, dbl_v, mul_c, add_c, sub_c,
        neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq, Fp2.one_canonical,
        Fp2.toSpec_one]
      rw [EthLib.Cryptography.Bls.G2.mk.injEq]
      simp only [ofFp_ofNat, EthLib.Cryptography.Bls.Fp2.one_def]
      generalize p.x.toSpec = X1
      generalize p.y.toSpec = Y1
      generalize p.z.toSpec = Z1
      generalize q.x.toSpec = X2
      generalize q.y.toSpec = Y2
      refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring
  · have hq1' : q.z.beq Fp2.one = false := by simpa using hq1
    simp (config := {maxDischargeDepth := 40}) only [hq1', Bool.false_eq_true, if_false,
      ↓reduceIte, toSpec_mk, toSpec_x, toSpec_y, toSpec_z, mul_v, add_v, sub_v, neg_v, sqr_v,
      dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c, dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
    split_ifs with c1 c2
    · exact double_spec ⟨hpx, hpy, hpz⟩
    · exact ⟨zero_canonical, toSpec_zero⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only
      all_goals try simp (config := {maxDischargeDepth := 40}) only [toSpec_mk, toSpec_x, toSpec_y,
        toSpec_z, mul_v, add_v, sub_v, neg_v, sqr_v, dbl_v, mul_c, add_c, sub_c, neg_c, sqr_c,
        dbl_c, hpx, hpy, hpz, hqx, hqy, hqz, beq_eq]
      rw [EthLib.Cryptography.Bls.G2.mk.injEq]
      simp only [ofFp_ofNat]
      generalize p.x.toSpec = X1
      generalize p.y.toSpec = Y1
      generalize p.z.toSpec = Z1
      generalize q.x.toSpec = X2
      generalize q.y.toSpec = Y2
      generalize q.z.toSpec = Z2
      refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring

/-- `generator` computes the spec's. -/
theorem generator_spec :
    Canonical generator ∧ toSpec generator = EthLib.Cryptography.Bls.G2.generator := by
  refine ⟨⟨Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _),
    Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _), Fp2.one_canonical⟩, ?_⟩
  simp only [generator, EthLib.Cryptography.Bls.G2.generator, toSpec_mk, Fp2.toSpec_mk,
    Fp.val_ofNat, Fp2.toSpec_one]

/-- `zero` computes the spec's. -/
theorem zero_spec : Canonical zero ∧ toSpec zero = EthLib.Cryptography.Bls.G2.zero :=
  ⟨zero_canonical, toSpec_zero⟩

/-- `bTwist` computes the spec's. -/
theorem bTwist_spec :
    bTwist.Canonical ∧ bTwist.toSpec = EthLib.Cryptography.Bls.G2.bTwist :=
  ⟨Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _), by
    simp only [bTwist, EthLib.Cryptography.Bls.G2.bTwist, Fp2.toSpec_mk, Fp.val_ofNat]⟩

/-- The infinity test agrees. -/
theorem isInfinity_spec {p : G2} (hp : Canonical p) :
    p.isInfinity = (toSpec p).isInfinity :=
  isZero_eq hp.2.2

/-- `neg` computes the spec's. -/
theorem neg_spec {p : G2} (hp : Canonical p) :
    Canonical (neg p) ∧ toSpec (neg p) = EthLib.Cryptography.Bls.G2.neg (toSpec p) := by
  obtain ⟨hx, hy, hz⟩ := hp
  have e : neg p = ⟨p.x, -p.y, p.z⟩ := rfl
  rw [e]
  refine ⟨canonical_mk.mpr ⟨hx, neg_c hy, hz⟩, ?_⟩
  simp only [EthLib.Cryptography.Bls.G2.neg, toSpec_mk, toSpec_x, toSpec_y, toSpec_z, neg_v hy]

theorem spec_inverse_one : EthLib.Cryptography.Bls.Fp2.inverse EthLib.Cryptography.Bls.Fp2.one =
    EthLib.Cryptography.Bls.Fp2.one := by
  rw [EthLib.Cryptography.Bls.Fp2.one_def, EthLib.Cryptography.Bls.Fp2.inverse_eq_inv, inv_one]

/-- `toAffine` computes the spec's, coordinate by coordinate. -/
theorem toAffine_spec {p : G2} (hp : Canonical p) :
    p.toAffine.1.Canonical ∧ p.toAffine.2.Canonical ∧
      (p.toAffine.1.toSpec, p.toAffine.2.toSpec) = (toSpec p).toAffine := by
  obtain ⟨hx, hy, hz⟩ := hp
  have hs : (toSpec p).z.isZero = p.z.isZero := (isZero_eq hz).symm
  unfold toAffine EthLib.Cryptography.Bls.G2.toAffine
  rw [hs]
  by_cases h0 : p.z.isZero = true
  · rw [if_pos h0, if_pos h0]
    exact ⟨Fp2.zero_canonical, Fp2.zero_canonical, by rw [Fp2.toSpec_zero]⟩
  rw [if_neg h0, if_neg h0]
  by_cases h1 : p.z.beq Fp2.one = true
  · have h1v : p.z.toSpec = EthLib.Cryptography.Bls.Fp2.one := by
      rw [← Fp2.toSpec_one]; exact (Fp2.beq_iff hz Fp2.one_canonical).mp h1
    rw [if_pos h1]
    refine ⟨hx, hy, ?_⟩
    simp only [toSpec_z, toSpec_x, toSpec_y, h1v, spec_inverse_one, spec_mul_one, spec_one_mul]
  · rw [if_neg h1]
    have hi := Fp2.inverse_canonical hz
    have hi2 := sqr_c hi
    have hi3 := mul_c hi2 hi
    refine ⟨mul_c hx hi2, mul_c hy hi3, ?_⟩
    simp (config := {maxDischargeDepth := 40}) only [toSpec_z, toSpec_x, toSpec_y, mul_v, sqr_v,
      Fp2.toSpec_inverse hz, hz, hi, hi2, hi3, hx, hy, mul_c, sqr_c]

/-- `mulNat` computes the spec's. -/
theorem mulNat_spec (k : Nat) : ∀ {p : G2}, Canonical p →
    Canonical (mulNat p k) ∧
      toSpec (mulNat p k) = EthLib.Cryptography.Bls.G2.mulNat (toSpec p) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp
    rw [mulNat, EthLib.Cryptography.Bls.G2.mulNat]
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
theorem mul_spec {p : G2} (hp : Canonical p) (s : EthLib.Cryptography.Bls.Fr) :
    Canonical (mul p s) ∧
      toSpec (mul p s) = EthLib.Cryptography.Bls.G2.mul (toSpec p) s :=
  mulNat_spec s.val hp

/-- `mulNatW` is `mulNat` at `k.toNat`. -/
theorem mulNatW_spec (n : Nat) : ∀ (k : UInt64), k.toNat = n → ∀ {p : G2}, Canonical p →
    Canonical (mulNatW p k) ∧
      toSpec (mulNatW p k) = EthLib.Cryptography.Bls.G2.mulNat (toSpec p) k.toNat := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hkn p hp
    rw [mulNatW, EthLib.Cryptography.Bls.G2.mulNat]
    have hk0 : (k = 0) ↔ k.toNat = 0 := by
      rw [← UInt64.toNat_inj]; simp
    have hdiv : (k / 2).toNat = k.toNat / 2 := by rw [UInt64.toNat_div]; rfl
    have hmod : (k % 2 = 1) ↔ k.toNat % 2 = 1 := by
      rw [← UInt64.toNat_inj, UInt64.toNat_mod]
      simp
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos (hk0.mp hk)]; exact zero_spec
    have hk' : ¬ k.toNat = 0 := fun h => hk (hk0.mpr h)
    rw [if_neg hk, if_neg hk']
    obtain ⟨hd, hds⟩ := double_spec hp
    obtain ⟨hh, hhs⟩ := ih (n / 2) (by omega) (k / 2) (by rw [hdiv, hkn]) hd
    rw [hdiv] at hhs
    rw [← hds, ← hhs]
    by_cases hodd : k % 2 = 1
    · rw [if_pos hodd, if_pos (hmod.mp hodd)]
      exact add_spec hp hh
    · rw [if_neg hodd, if_neg (fun h => hodd (hmod.mpr h))]
      exact ⟨hh, rfl⟩

/-- `mulNatW` computes the spec's `mulNat` at `k.toNat`. -/
theorem mulNatW_spec' {p : G2} (hp : Canonical p) (k : UInt64) :
    Canonical (mulNatW p k) ∧
      toSpec (mulNatW p k) = EthLib.Cryptography.Bls.G2.mulNat (toSpec p) k.toNat :=
  mulNatW_spec _ k rfl hp

/-- The most-significant-bit-first ladder computes the mirror's, for up to 64 bits. -/
theorem mulMsb_spec {p : G2} (hp : Canonical p) (k : UInt64) (n : Nat) (hn : n ≤ 64) :
    ∀ {acc : G2}, Canonical acc →
      Canonical (mulMsb p k n acc) ∧
        toSpec (mulMsb p k n acc) =
          Mirror.G2.mulMsb (toSpec p) k.toNat n (toSpec acc) := by
  induction n with
  | zero => intro acc hacc; exact ⟨hacc, rfl⟩
  | succ n ih =>
    intro acc hacc
    have hn' : n ≤ 64 := by omega
    have hb := G1.bit_spec k n (by omega)
    obtain ⟨hd, hds⟩ := double_spec hacc
    have e1 : mulMsb p k (n + 1) acc =
        mulMsb p k n (if (k >>> n.toUInt64) &&& 1 != 0 then add (double acc) p else double acc) := by
      rw [mulMsb]
    have e2 : Mirror.G2.mulMsb (toSpec p) k.toNat (n + 1) (toSpec acc) =
        Mirror.G2.mulMsb (toSpec p) k.toNat n
          (if k.toNat.testBit n then
            EthLib.Cryptography.Bls.G2.add (EthLib.Cryptography.Bls.G2.double (toSpec acc)) (toSpec p)
          else EthLib.Cryptography.Bls.G2.double (toSpec acc)) := by
      rw [Mirror.G2.mulMsb]
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

/-- `mulAbsX` computes the mirror's `[|x|]P`. -/
theorem mulAbsX_spec {p : G2} (hp : Canonical p) :
    Canonical (mulAbsX p) ∧ toSpec (mulAbsX p) = Mirror.G2.mulAbsX (toSpec p) := by
  have := mulMsb_spec hp absXWord 63 (by omega) hp
  rw [absXWord_toNat] at this
  exact this

/-- `eqProj` computes the mirror's test. -/
theorem eqProj_spec {p q : G2} (hp : Canonical p) (hq : Canonical q) :
    eqProj p q = Mirror.G2.eqProj (toSpec p) (toSpec q) := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  unfold eqProj Mirror.G2.eqProj
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

end EthLibImpl.Cryptography.Bls.G2

namespace EthLibImpl.Cryptography.Bls.Fp2

theorem halfFp_canonical : halfFp.Canonical := Fp.inverse_canonical (Fp.ofNat_canonical 2)

theorem halfFp_val : halfFp.val = (EthLib.Cryptography.Bls.Fp.ofNat 2).inverse := by
  unfold halfFp; rw [Fp.val_inverse (Fp.ofNat_canonical 2), Fp.val_ofNat]

theorem invSqrtDigits_eq :
    invSqrtDigits = Fp.nibbles ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) := rfl

open EthLib.Cryptography.Bls (BlsError)

/-- `sqrt` with `Fp.sqrt`, `1/2` and the exponent's digits as parameters (the kernel would
otherwise evaluate these concrete constants while checking zeta-reductions). -/
def sqrtP (half : Fp) (dg : ByteArray) (sq : Fp → Except BlsError Fp) (a : Fp2) :
    Except BlsError Fp2 :=
  if a.c1.isZero then
    let d := Fp.powNibbles a.c0 dg
    let s := d * a.c0
    if (d * s).beq Fp.one then .ok (mk s Fp.zero) else .ok (mk Fp.zero s)
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match sq n with
    | .error _ => .error .notASquare
    | .ok s =>
      let t := (a.c0 + s) * half
      let d := Fp.powNibbles t dg
      let dt := d * t
      let hd := a.c1 * d * half
      if (d * dt).beq Fp.one then .ok (mk dt hd) else .ok (mk (-hd) dt)

theorem sqrt_eq_P : sqrt = sqrtP halfFp invSqrtDigits Fp.sqrt := rfl

/-- The part of `sqrtP` after the norm's square root `s` is known. -/
def sqrtOk (half : Fp) (dg : ByteArray) (a : Fp2) (s : Fp) : Except BlsError Fp2 :=
  let t := (a.c0 + s) * half
  let d := Fp.powNibbles t dg
  let dt := d * t
  let hd := a.c1 * d * half
  if (d * dt).beq Fp.one then .ok (mk dt hd) else .ok (mk (-hd) dt)

/-- `sqrtP` with its second branch factored through `sqrtOk`. -/
def sqrtP2 (half : Fp) (dg : ByteArray) (sq : Fp → Except BlsError Fp) (a : Fp2) :
    Except BlsError Fp2 :=
  if a.c1.isZero then
    let d := Fp.powNibbles a.c0 dg
    let s := d * a.c0
    if (d * s).beq Fp.one then .ok (mk s Fp.zero) else .ok (mk Fp.zero s)
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match sq n with
    | .error _ => .error .notASquare
    | .ok s => sqrtOk half dg a s

theorem sqrtP_eq_P2 (half : Fp) (dg : ByteArray) (sq : Fp → Except BlsError Fp) (a : Fp2) :
    sqrtP half dg sq a = sqrtP2 half dg sq a := rfl

theorem sqrt_eq_P2 : sqrt = sqrtP2 halfFp invSqrtDigits Fp.sqrt := by
  rw [sqrt_eq_P]; funext a; exact sqrtP_eq_P2 _ _ _ a

/-- The spec-level `sqrtAlt` with `Fp.sqrt`, `1/2` and the exponent as parameters. -/
def sqrtAltP (half : EthLib.Cryptography.Bls.Fp) (e : Nat)
    (sq : EthLib.Cryptography.Bls.Fp → Except BlsError EthLib.Cryptography.Bls.Fp)
    (a : EthLib.Cryptography.Bls.Fp2) : Except BlsError EthLib.Cryptography.Bls.Fp2 :=
  if a.c1.isZero then
    let d := EthLib.Cryptography.Bls.Fp.powNat a.c0 e
    let s := d * a.c0
    if (d * s).beq EthLib.Cryptography.Bls.Fp.one then .ok ⟨s, EthLib.Cryptography.Bls.Fp.zero⟩
    else .ok ⟨EthLib.Cryptography.Bls.Fp.zero, s⟩
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match sq n with
    | .error _ => .error .notASquare
    | .ok s =>
      let t := (a.c0 + s) * half
      let d := EthLib.Cryptography.Bls.Fp.powNat t e
      let dt := d * t
      let hd := a.c1 * d * half
      if (d * dt).beq EthLib.Cryptography.Bls.Fp.one then .ok ⟨dt, hd⟩ else .ok ⟨-hd, dt⟩

theorem sqrtAlt_eq_P : EthLib.Cryptography.Bls.Fp2.sqrtAlt =
    sqrtAltP (EthLib.Cryptography.Bls.Fp.ofNat 2).inverse
      ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) EthLib.Cryptography.Bls.Fp.sqrt := by
  funext a
  unfold EthLib.Cryptography.Bls.Fp2.sqrtAlt sqrtAltP
  rfl

/-- The spec-level counterpart of `sqrtOk`. -/
def sqrtAltOk (half : EthLib.Cryptography.Bls.Fp) (e : Nat) (a : EthLib.Cryptography.Bls.Fp2)
    (s : EthLib.Cryptography.Bls.Fp) : Except BlsError EthLib.Cryptography.Bls.Fp2 :=
  let t := (a.c0 + s) * half
  let d := EthLib.Cryptography.Bls.Fp.powNat t e
  let dt := d * t
  let hd := a.c1 * d * half
  if (d * dt).beq EthLib.Cryptography.Bls.Fp.one then .ok ⟨dt, hd⟩ else .ok ⟨-hd, dt⟩

/-- `sqrtAltP` with its second branch factored through `sqrtAltOk`. -/
def sqrtAltP2 (half : EthLib.Cryptography.Bls.Fp) (e : Nat)
    (sq : EthLib.Cryptography.Bls.Fp → Except BlsError EthLib.Cryptography.Bls.Fp)
    (a : EthLib.Cryptography.Bls.Fp2) : Except BlsError EthLib.Cryptography.Bls.Fp2 :=
  if a.c1.isZero then
    let d := EthLib.Cryptography.Bls.Fp.powNat a.c0 e
    let s := d * a.c0
    if (d * s).beq EthLib.Cryptography.Bls.Fp.one then .ok ⟨s, EthLib.Cryptography.Bls.Fp.zero⟩
    else .ok ⟨EthLib.Cryptography.Bls.Fp.zero, s⟩
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match sq n with
    | .error _ => .error .notASquare
    | .ok s => sqrtAltOk half e a s

theorem sqrtAltP_eq_P2 (half : EthLib.Cryptography.Bls.Fp) (e : Nat)
    (sq : EthLib.Cryptography.Bls.Fp → Except BlsError EthLib.Cryptography.Bls.Fp)
    (a : EthLib.Cryptography.Bls.Fp2) : sqrtAltP half e sq a = sqrtAltP2 half e sq a := rfl

theorem sqrtAlt_eq_P2 : EthLib.Cryptography.Bls.Fp2.sqrtAlt =
    sqrtAltP2 (EthLib.Cryptography.Bls.Fp.ofNat 2).inverse
      ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) EthLib.Cryptography.Bls.Fp.sqrt := by
  rw [sqrtAlt_eq_P]; funext a; exact sqrtAltP_eq_P2 _ _ _ a

theorem sqrtOk_spec (half : Fp) (half' : EthLib.Cryptography.Bls.Fp) (hh : half.Canonical)
    (hhv : half.val = half') (e : Nat) {x : Fp2} (hx : Canonical x) {s : Fp}
    (hs : s.Canonical) :
    (sqrtOk half (Fp.nibbles e) x s).map toSpec = sqrtAltOk half' e (toSpec x) s.val ∧
      ∀ y, sqrtOk half (Fp.nibbles e) x s = .ok y → Canonical y := by
  subst hhv
  unfold sqrtOk sqrtAltOk
  dsimp only
  have htc : ((x.c0 + s) * half).Canonical := G1.mul_c hh
  have htv : ((x.c0 + s) * half).val = ((toSpec x).c0 + s.val) * half.val := by
    rw [G1.mul_v hh, G1.add_v hx.1 hs]; rfl
  have hD : (Fp.powNibbles ((x.c0 + s) * half) (Fp.nibbles e)).Canonical :=
    Fp.powNibbles_canonical htc _
  have hDs : (Fp.powNibbles ((x.c0 + s) * half) (Fp.nibbles e)).val =
      EthLib.Cryptography.Bls.Fp.powNat (((toSpec x).c0 + s.val) * half.val) e := by
    rw [Fp.val_powNibbles_powNat htc, htv]
  rw [← hDs, ← htv]
  generalize (x.c0 + s) * half = t at htc htv hD hDs ⊢
  generalize Fp.powNibbles t (Fp.nibbles e) = D at hD hDs ⊢
  have hDt : (D * t).Canonical := G1.mul_c htc
  have hDtv : (D * t).val = D.val * t.val := G1.mul_v htc
  have hDDt : (D * (D * t)).Canonical := G1.mul_c hDt
  have hDDtv : (D * (D * t)).val = D.val * (D * t).val := G1.mul_v hDt
  have hh1 : (x.c1 * D * half).Canonical := G1.mul_c hh
  have hh1v : (x.c1 * D * half).val = x.c1.val * D.val * half.val := by
    rw [G1.mul_v hh, G1.mul_v hD]
  have hc : (D * (D * t)).beq Fp.one = EthLib.Cryptography.Bls.Fp.beq
      (D.val * (D.val * t.val)) EthLib.Cryptography.Bls.Fp.one := by
    rw [G1.beq_eq hDDt Fp.one_canonical, hDDtv, hDtv, Fp.val_one]; rfl
  rw [hc]
  split_ifs
  · refine ⟨?_, fun y hy => ?_⟩
    · show Except.ok (toSpec (Fp2.mk (D * t) (x.c1 * D * half))) = _
      rw [toSpec_mk, hDtv, hh1v]; rfl
    · cases hy; exact canonical_mk hDt hh1
  · refine ⟨?_, fun y hy => ?_⟩
    · show Except.ok (toSpec (Fp2.mk (-(x.c1 * D * half)) (D * t))) = _
      rw [toSpec_mk, G1.neg_v hh1, hDtv, hh1v]; rfl
    · cases hy; exact canonical_mk (G1.neg_c hh1) hDt

theorem sqrtP2_spec (half : Fp) (half' : EthLib.Cryptography.Bls.Fp) (hh : half.Canonical)
    (hhv : half.val = half') (e : Nat)
    (sq : Fp → Except BlsError Fp)
    (sq' : EthLib.Cryptography.Bls.Fp → Except BlsError EthLib.Cryptography.Bls.Fp)
    (hsq : ∀ a : Fp, a.Canonical → (sq a).map Fp.val = sq' a.val ∧
      ∀ c, sq a = .ok c → c.Canonical)
    {x : Fp2} (hx : Canonical x) :
    (sqrtP2 half (Fp.nibbles e) sq x).map toSpec = sqrtAltP2 half' e sq' (toSpec x) ∧
      ∀ y, sqrtP2 half (Fp.nibbles e) sq x = .ok y → Canonical y := by
  unfold sqrtP2 sqrtAltP2
  have hz : x.c1.isZero = (toSpec x).c1.isZero := fp_isZero_eq hx.2
  rw [hz]
  by_cases h : (toSpec x).c1.isZero = true
  · rw [if_pos h, if_pos h]
    have hD : (Fp.powNibbles x.c0 (Fp.nibbles e)).Canonical := Fp.powNibbles_canonical hx.1 _
    have hDs : (Fp.powNibbles x.c0 (Fp.nibbles e)).val =
        EthLib.Cryptography.Bls.Fp.powNat (toSpec x).c0 e := Fp.val_powNibbles_powNat hx.1 _
    generalize Fp.powNibbles x.c0 (Fp.nibbles e) = D at hD hDs ⊢
    rw [← hDs]
    dsimp only
    have hS : (D * x.c0).Canonical := G1.mul_c hx.1
    have hSv : (D * x.c0).val = D.val * x.c0.val := G1.mul_v hx.1
    have hDS : (D * (D * x.c0)).Canonical := G1.mul_c hS
    have hDSv : (D * (D * x.c0)).val = D.val * (D * x.c0).val := G1.mul_v hS
    have hc : (D * (D * x.c0)).beq Fp.one = EthLib.Cryptography.Bls.Fp.beq
        (D.val * (D.val * (toSpec x).c0)) EthLib.Cryptography.Bls.Fp.one := by
      rw [G1.beq_eq hDS Fp.one_canonical, hDSv, hSv, Fp.val_one]; rfl
    have hz0 : Fp.zero.val = EthLib.Cryptography.Bls.Fp.zero := by rw [Fp.val_zero]; rfl
    rw [hc]
    split_ifs
    · refine ⟨?_, fun y hy => ?_⟩
      · show Except.ok (toSpec (Fp2.mk (D * x.c0) Fp.zero)) = _
        rw [toSpec_mk, hSv, hz0]; rfl
      · cases hy; exact canonical_mk hS Fp.zero_canonical
    · refine ⟨?_, fun y hy => ?_⟩
      · show Except.ok (toSpec (Fp2.mk Fp.zero (D * x.c0))) = _
        rw [toSpec_mk, hSv, hz0]; rfl
      · cases hy; exact canonical_mk Fp.zero_canonical hS
  · rw [if_neg h, if_neg h]
    have hm0 : (x.c0 * x.c0).Canonical := G1.mul_c hx.1
    have hm1 : (x.c1 * x.c1).Canonical := G1.mul_c hx.2
    have hn : (x.c0 * x.c0 + x.c1 * x.c1).Canonical := G1.add_c hm0 hm1
    have hnv : (x.c0 * x.c0 + x.c1 * x.c1).val =
        (toSpec x).c0 * (toSpec x).c0 + (toSpec x).c1 * (toSpec x).c1 := by
      rw [G1.add_v hm0 hm1, G1.mul_v hx.1, G1.mul_v hx.2]; rfl
    obtain ⟨hsm, hsc⟩ := hsq _ hn
    rw [hnv] at hsm
    dsimp only
    rw [← hsm]
    rcases hs : sq (x.c0 * x.c0 + x.c1 * x.c1) with err | s
    · exact ⟨rfl, fun y hy => nomatch hy⟩
    · exact sqrtOk_spec half half' hh hhv e hx (hsc s hs)

theorem sqrt_spec {x : Fp2} (hx : Canonical x) :
    (sqrt x).map toSpec = EthLib.Cryptography.Bls.Fp2.sqrtAlt (toSpec x) ∧
      ∀ y, sqrt x = .ok y → Canonical y := by
  rw [sqrt_eq_P2, sqrtAlt_eq_P2]
  exact sqrtP2_spec halfFp _ halfFp_canonical halfFp_val ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4)
    Fp.sqrt EthLib.Cryptography.Bls.Fp.sqrt
    (fun a ha => ⟨Fp.sqrt_map_val ha, fun c h => Fp.sqrt_ok_canonical ha h⟩) hx


theorem sel_spec (c : Bool) {a b : Fp2} (ha : Canonical a) (hb : Canonical b) :
    Canonical (if c then a else b) ∧
      toSpec (if c then a else b) = if c then toSpec a else toSpec b := by
  cases c <;> simp [ha, hb]

/-- The value a zero input is replaced by in a batched inversion. -/
theorem sel_one {a : Fp2} (ha : Canonical a) :
    Canonical (if a.isZero then one else a) ∧
      toSpec (if a.isZero then one else a) =
        if (toSpec a).isZero then EthLib.Cryptography.Bls.Fp2.one else toSpec a := by
  obtain ⟨h1, h2⟩ := sel_spec a.isZero one_canonical ha
  refine ⟨h1, ?_⟩
  rw [h2, toSpec_one, isZero_eq ha]

/-- A zero-guarded result of a batched inversion. -/
theorem sel_zero {a r : Fp2} (ha : Canonical a) (hr : Canonical r) :
    Canonical (if a.isZero then zero else r) ∧
      toSpec (if a.isZero then zero else r) =
        if (toSpec a).isZero then EthLib.Cryptography.Bls.Fp2.zero else toSpec r := by
  obtain ⟨h1, h2⟩ := sel_spec a.isZero zero_canonical hr
  refine ⟨h1, ?_⟩
  rw [h2, toSpec_zero, isZero_eq ha]

theorem batchInverse2_spec {a b : Fp2} (ha : Canonical a) (hb : Canonical b) :
    (batchInverse2 a b).1.Canonical ∧ (batchInverse2 a b).2.Canonical ∧
      ((batchInverse2 a b).1.toSpec, (batchInverse2 a b).2.toSpec) =
        Mirror.HashToCurve.batchInverse2 a.toSpec b.toSpec := by
  unfold batchInverse2 Mirror.HashToCurve.batchInverse2
  dsimp only
  obtain ⟨ca, va⟩ := sel_one ha
  obtain ⟨cb, vb⟩ := sel_one hb
  have cab : (_ * _ : Fp2).Canonical := canonical_hMul ca cb
  have ci := inverse_canonical cab
  have vi := toSpec_inverse cab
  rw [toSpec_hMul ca cb] at vi
  generalize (if a.isZero = true then one else a) = a' at ca va cab ci vi ⊢
  generalize (if b.isZero = true then one else b) = b' at cb vb cab ci vi ⊢
  generalize inverse (a' * b') = i at ci vi ⊢
  obtain ⟨c1, v1⟩ := sel_zero (r := i * b') ha (canonical_hMul ci cb)
  obtain ⟨c2, v2⟩ := sel_zero (r := i * a') hb (canonical_hMul ci ca)
  refine ⟨c1, c2, ?_⟩
  rw [v1, v2, toSpec_hMul ci cb, toSpec_hMul ci ca, vi, va, vb]

theorem batchInverse4_spec {a b c d : Fp2} (ha : Canonical a) (hb : Canonical b)
    (hc : Canonical c) (hd : Canonical d) :
    (batchInverse4 a b c d).1.Canonical ∧ (batchInverse4 a b c d).2.1.Canonical ∧
      (batchInverse4 a b c d).2.2.1.Canonical ∧ (batchInverse4 a b c d).2.2.2.Canonical ∧
      ((batchInverse4 a b c d).1.toSpec, (batchInverse4 a b c d).2.1.toSpec,
        (batchInverse4 a b c d).2.2.1.toSpec, (batchInverse4 a b c d).2.2.2.toSpec) =
        Mirror.HashToCurve.batchInverse4 a.toSpec b.toSpec c.toSpec d.toSpec := by
  unfold batchInverse4 Mirror.HashToCurve.batchInverse4
  dsimp only
  obtain ⟨ca, va⟩ := sel_one ha
  obtain ⟨cb, vb⟩ := sel_one hb
  obtain ⟨cc, vc⟩ := sel_one hc
  obtain ⟨cd, vd⟩ := sel_one hd
  generalize (if a.isZero = true then one else a) = a' at ca va ⊢
  generalize (if b.isZero = true then one else b) = b' at cb vb ⊢
  generalize (if c.isZero = true then one else c) = c' at cc vc ⊢
  generalize (if d.isZero = true then one else d) = d' at cd vd ⊢
  have cab : (a' * b').Canonical := canonical_hMul ca cb
  have ccd : (c' * d').Canonical := canonical_hMul cc cd
  have cabcd : (a' * b' * (c' * d')).Canonical := canonical_hMul cab ccd
  have ci := inverse_canonical cabcd
  have vi := toSpec_inverse cabcd
  rw [toSpec_hMul cab ccd, toSpec_hMul ca cb, toSpec_hMul cc cd] at vi
  generalize inverse (a' * b' * (c' * d')) = i at ci vi ⊢
  have ciab : (i * (c' * d')).Canonical := canonical_hMul ci ccd
  have cicd : (i * (a' * b')).Canonical := canonical_hMul ci cab
  have viab : (i * (c' * d')).toSpec = i.toSpec * (c'.toSpec * d'.toSpec) := by
    rw [toSpec_hMul ci ccd, toSpec_hMul cc cd]
  have vicd : (i * (a' * b')).toSpec = i.toSpec * (a'.toSpec * b'.toSpec) := by
    rw [toSpec_hMul ci cab, toSpec_hMul ca cb]
  generalize i * (c' * d') = iab at ciab viab ⊢
  generalize i * (a' * b') = icd at cicd vicd ⊢
  obtain ⟨c1, v1⟩ := sel_zero (r := iab * b') ha (canonical_hMul ciab cb)
  obtain ⟨c2, v2⟩ := sel_zero (r := iab * a') hb (canonical_hMul ciab ca)
  obtain ⟨c3, v3⟩ := sel_zero (r := icd * d') hc (canonical_hMul cicd cd)
  obtain ⟨c4, v4⟩ := sel_zero (r := icd * c') hd (canonical_hMul cicd cc)
  refine ⟨c1, c2, c3, c4, ?_⟩
  rw [v1, v2, v3, v4, toSpec_hMul ciab cb, toSpec_hMul ciab ca, toSpec_hMul cicd cd,
    toSpec_hMul cicd cc, viab, vicd, vi, va, vb, vc, vd]


/-- `Fp2.signBit` computes the spec's. -/
theorem signBit_spec {y : Fp2} (hy : Canonical y) :
    Bls.Fp2.signBit y = EthLib.Cryptography.Bls.Fp2.signBit (toSpec y) := by
  unfold Bls.Fp2.signBit EthLib.Cryptography.Bls.Fp2.signBit
  rw [fp_isZero_eq hy.2, Fp.signBit_eq_spec, Fp.signBit_eq_spec]
  rfl

end EthLibImpl.Cryptography.Bls.Fp2
