import EthLibImpl.Cryptography.Proofs.Bls.MirrorSig
import EthLibImpl.Cryptography.Proofs.Bls.G2Check
import EthLibImpl.Cryptography.Proofs.Bls.G1Endo
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Group

/-!
# Proofs: the implementation's signature functions return the spec's

`EthLibImpl.Cryptography.Bls.Mirror.Signatures` restates the
implementation's signature layer over spec types (see `MirrorSig`). This
file proves that its two public entry points return what the spec's
`EthLib.Cryptography.Bls.Signatures` functions return:

* `ethAggregatePubkeys_eq`: unconditionally.
* `ethFastAggregateVerify_eq`: given that the mirrored pairing check and
  hash-to-curve agree with the spec's (hypotheses `hpair` and `hhash`,
  proven in their own files).

The steps:

1. `g1InSubgroup_eq`: the endomorphism subgroup test is the spec's
   `[r]P = O` on valid points (`G1.inSubgroup_iff_endo`), and
   `G1.valid_of_uncompress`: every decoded point is on the curve.
2. `validatedPubkey_eq`: the implementation's one-pass key validation is
   the spec's `keyValidate` followed by `uncompress`.
3. `pairingCheck_congr_two` and `G1.toAffine_eq_of_toPoint_eq`: the spec's
   pairing check reads a `G1` point only through `isInfinity` and
   `toAffine`, which two valid triples denoting the same group element
   share.
4. `coreVerify_compress`: the spec verifies the *compressed* aggregate key,
   which it decodes back into a different Jacobian triple; the mirror
   verifies the aggregate point directly. They agree when the aggregate is
   a valid point of the `r`-torsion subgroup.
5. The two aggregation loops run the same step function, and every
   accumulator they produce is a sum of subgroup points, which is what 4
   needs.

Step 4 needs the `G1` compression round-trip. EthLib's
`G1.uncompress_compress` uses `bv_decide` and `native_decide`, so this file
re-proves the two halves it needs (`G1.uncompress_compress_of_ne`,
`G1.isInfinity_of_uncompress_infinityBytes`) with kernel `decide`, and the
main theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve.Jacobian
open scoped EthLib.Cryptography.Bls.Fp

/-! ## Decoded points are on the curve -/

private theorem four_ne_zero' : (4 : ZMod Fp.modulus) ≠ 0 := by decide
private theorem three_ne_zero' : (3 : ZMod Fp.modulus) ≠ 0 := by decide
private theorem two_ne_zero'' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-- An affine triple `(x, y, 1)` with `y² = x³ + 4` is a nonsingular point. -/
private theorem nonsingular_affine {x y : ZMod Fp.modulus} (h : y * y = x * x * x + 4) :
    curve.Nonsingular ![x, y, 1] := by
  rw [nonsingular_some, WeierstrassCurve.Affine.nonsingular_iff]
  have heq : curve.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
      show curve.a₆ = (4 : ZMod Fp.modulus) from rfl]
    linear_combination h
  refine ⟨heq, ?_⟩
  by_cases hy : y = 0
  · left
    have hx : x ≠ 0 := by
      rintro rfl
      apply four_ne_zero'
      rw [hy] at h
      linear_combination -h
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₄ = 0 from rfl]
    intro h0
    have : 3 * x ^ 2 = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact three_ne_zero' h1
    · exact hx (pow_eq_zero_iff two_ne_zero |>.mp h1)
  · right
    simp only [show curve.a₁ = 0 from rfl, show curve.a₃ = 0 from rfl]
    intro h0
    have : 2 * y = 0 := by linear_combination h0
    exact (mul_ne_zero two_ne_zero'' hy) this

/-- An affine spec point `(x, y, 1)` with `y² = x³ + 4` is valid. -/
theorem valid_affine {x y : Fp}
    (h : (y : ZMod Fp.modulus) * y = (x : ZMod Fp.modulus) * x * x + 4) :
    Valid ⟨x, y, Fp.one⟩ :=
  nonsingular_affine h

/-- A successful `uncompress` yields a valid curve point. -/
theorem valid_of_uncompress {b : ByteArray} {q : G1} (h : uncompress b = .ok q) :
    Valid q := by
  rw [uncompress] at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact valid_zero
  split at h
  · cases h
  · rename_i x _
    split at h
    · cases h
    · rename_i yPos hsq
      cases h
      have hy : (yPos : ZMod Fp.modulus) * yPos = (x : ZMod Fp.modulus) * x * x + 4 :=
        Fp.sqrt_ok hsq
      apply valid_affine
      split
      · exact hy
      · show ((-yPos : Fp) : ZMod Fp.modulus) * (-yPos : Fp) = _
        rw [show ((-yPos : Fp) : ZMod Fp.modulus) = -(yPos : ZMod Fp.modulus) from rfl,
          neg_mul_neg]
        exact hy

/-! ## Compression round-trip without `bv_decide`/`native_decide`

`G1.uncompress_compress` (in `Proofs/Bls/Compress.lean`) discharges its
flag-byte facts with `bv_decide` and the infinity case with `native_decide`,
so it depends on compiler-trusting axioms. The two pieces this file needs
are re-proven here with kernel `decide` (over the 32 possible top bytes of a
canonical `x`), reusing that file's private plumbing. -/

open private compress_inf compress_noninf uncompress_of_facts ba_size_set! ba_get!_set!_ne
  ba_get!_set!_self ba_ext from EthLib.Cryptography.Proofs.Bls.Compress

/-- Flag-byte facts for a set sign bit (`b` is the top byte of a canonical
`x`, so `b < 0x20`); `decide` over the 32 candidates. -/
private theorem flags_sign (b : UInt8) (hb : b < 0x20) :
    (b ||| 0x80 ||| 0x20) &&& 0x80 ≠ 0 ∧ (b ||| 0x80 ||| 0x20) &&& 0x40 = 0 ∧
    (b ||| 0x80 ||| 0x20) &&& 0x20 ≠ 0 ∧ (b ||| 0x80 ||| 0x20) &&& 0x1f = b := by
  have key : ∀ n, n < 32 → (UInt8.ofNat n ||| 0x80 ||| 0x20) &&& 0x80 ≠ 0 ∧
      (UInt8.ofNat n ||| 0x80 ||| 0x20) &&& 0x40 = 0 ∧
      (UInt8.ofNat n ||| 0x80 ||| 0x20) &&& 0x20 ≠ 0 ∧
      (UInt8.ofNat n ||| 0x80 ||| 0x20) &&& 0x1f = UInt8.ofNat n := by decide
  have hn : b.toNat < 32 := by rw [UInt8.lt_iff_toNat_lt] at hb; exact hb
  have := key b.toNat hn
  rwa [UInt8.ofNat_toNat] at this

/-- Flag-byte facts for a clear sign bit. -/
private theorem flags_nosign (b : UInt8) (hb : b < 0x20) :
    (b ||| 0x80) &&& 0x80 ≠ 0 ∧ (b ||| 0x80) &&& 0x40 = 0 ∧
    (b ||| 0x80) &&& 0x20 = 0 ∧ (b ||| 0x80) &&& 0x1f = b := by
  have key : ∀ n, n < 32 → (UInt8.ofNat n ||| 0x80) &&& 0x80 ≠ 0 ∧
      (UInt8.ofNat n ||| 0x80) &&& 0x40 = 0 ∧
      (UInt8.ofNat n ||| 0x80) &&& 0x20 = 0 ∧
      (UInt8.ofNat n ||| 0x80) &&& 0x1f = UInt8.ofNat n := by decide
  have hn : b.toNat < 32 := by rw [UInt8.lt_iff_toNat_lt] at hb; exact hb
  have := key b.toNat hn
  rwa [UInt8.ofNat_toNat] at this

/-- Compression round-trip off infinity (`uncompress_compress` without
`bv_decide`). -/
theorem uncompress_compress_of_ne {p : G1} (h : Valid p) (hinf : ¬ p.isInfinity = true) :
    ∃ q, uncompress (compress p) = .ok q ∧ toPoint q = toPoint p := by
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  set B0 := (Fp.toBytesBE xa).get! 0 with hB0
  have hb0 : B0 < 0x20 := by
    rw [hB0, UInt8.lt_iff_toNat_lt]; exact Fp.toBytesBE_head_lt xa
  have hsqw : (ya : ZMod Fp.modulus) * ya = xa * xa * xa + Fp.ofNat 4 := by
    have := affine_sqrt_witness h hinf; rw [hpa] at this; exact this
  have hsqrt := Fp.sqrt_complete hsqw
  have hysq : ((Fp.powNat (xa * xa * xa + Fp.ofNat 4)
      ((Fp.modulus + 1) / 4) : Fp) : ZMod Fp.modulus)
      * Fp.powNat (xa * xa * xa + Fp.ofNat 4) ((Fp.modulus + 1) / 4)
      = (ya : ZMod Fp.modulus) * ya := by rw [Fp.sqrt_ok hsqrt, ← hsqw]
  have hsz48 : (Fp.toBytesBE xa).size = 48 := Fp.size_toBytesBE xa
  have hcp := compress_noninf hinf hpa
  have hother : ∀ i, i ≠ 0 → (compress p).get! i = (Fp.toBytesBE xa).get! i := by
    intro i hi0
    rw [hcp]; dsimp only
    by_cases hs : Fp.signBit ya
    · rw [if_pos hs, ba_get!_set!_ne _ _ hi0, ba_get!_set!_ne _ _ hi0]
    · rw [if_neg hs, ba_get!_set!_ne _ _ hi0]
  have hsize : (compress p).size = 48 := by
    rw [hcp]; dsimp only
    by_cases hs : Fp.signBit ya
    · rw [if_pos hs, ba_size_set!, ba_size_set!, hsz48]
    · rw [if_neg hs, ba_size_set!, hsz48]
  refine ⟨⟨xa, ya, Fp.one⟩, ?_, ?_⟩
  · by_cases hs : Fp.signBit ya
    · obtain ⟨f1, f2, f3, f4⟩ := flags_sign B0 hb0
      have hhead : (compress p).get! 0 = B0 ||| 0x80 ||| 0x20 := by
        rw [hcp]; dsimp only
        rw [if_pos hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz48]; decide),
          ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
      refine uncompress_of_facts hsize (by rw [hhead]; exact f1)
        (by rw [hhead]; exact f2) ?_ ?_ hsqrt hysq
      · rw [hhead]
        exact ⟨fun _ => hs, fun _ => f3⟩
      · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
        rw [ba_size_set!, hsize] at hi'
        by_cases hi0 : i = 0
        · subst hi0
          rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]; exact f4
        · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
    · obtain ⟨f1, f2, f3, f4⟩ := flags_nosign B0 hb0
      have hhead : (compress p).get! 0 = B0 ||| 0x80 := by
        rw [hcp]; dsimp only
        rw [if_neg hs, ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
      refine uncompress_of_facts hsize (by rw [hhead]; exact f1)
        (by rw [hhead]; exact f2) ?_ ?_ hsqrt hysq
      · rw [hhead]
        exact ⟨fun hne => absurd f3 hne, fun hh => absurd hh hs⟩
      · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
        rw [ba_size_set!, hsize] at hi'
        by_cases hi0 : i = 0
        · subst hi0
          rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]; exact f4
        · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
  · have := toPoint_affine_normalize (p := p) hinf
    rw [hpa] at this; exact this

private theorem infinityBytes_head : infinityBytes.get! 0 = 0xc0 := by decide

/-- Whatever `uncompress` decodes from the infinity encoding is the point at
infinity (the infinity flag is set, so only that branch can succeed). -/
theorem isInfinity_of_uncompress_infinityBytes {q : G1}
    (h : uncompress infinityBytes = .ok q) : q.isInfinity = true := by
  rw [uncompress] at h
  split at h
  · cases h
  dsimp only at h
  rw [infinityBytes_head] at h
  rw [if_neg (by decide), if_pos (by decide)] at h
  split at h
  · cases h
  · cases h
    rfl

/-- `compress` sends a point at infinity to the infinity encoding. -/
theorem compress_of_isInfinity {p : G1} (h : p.isInfinity = true) :
    compress p = infinityBytes :=
  compress_inf h

/-! ## Affine coordinates -/

private theorem z_mul_inverse' {p : G1} (hz : ¬ p.z.isZero = true) :
    (p.z : ZMod Fp.modulus) * (p.z.inverse : ZMod Fp.modulus) = 1 := by
  rw [Fp.inverse_eq_inv]
  exact mul_inv_cancel₀ (fun hh => hz (isZero_iff.mpr hh))

private theorem affX_aux {x z w : ZMod Fp.modulus} (hw : z * w = 1) :
    x * (w * w) = x / z ^ 2 := by
  have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hw
  rw [eq_div_iff (pow_ne_zero 2 hz)]
  linear_combination x * (z * w + 1) * hw

private theorem affY_aux {y z w : ZMod Fp.modulus} (hw : z * w = 1) :
    y * (w * w * w) = y / z ^ 3 := by
  have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hw
  rw [eq_div_iff (pow_ne_zero 3 hz)]
  linear_combination y * ((z * w) ^ 2 + z * w + 1) * hw

/-- Off infinity, the affine `x` is `x / z²`. -/
theorem toAffine_fst {p : G1} (hz : ¬ p.isInfinity = true) :
    ((p.toAffine).1 : ZMod Fp.modulus) = rep p 0 / rep p 2 ^ 2 := by
  have hz' : ¬ p.z.isZero = true := hz
  simp only [G1.toAffine, if_neg hz']
  exact affX_aux (z_mul_inverse' hz)

/-- Off infinity, the affine `y` is `y / z³`. -/
theorem toAffine_snd {p : G1} (hz : ¬ p.isInfinity = true) :
    ((p.toAffine).2 : ZMod Fp.modulus) = rep p 1 / rep p 2 ^ 3 := by
  have hz' : ¬ p.z.isZero = true := hz
  simp only [G1.toAffine, if_neg hz']
  exact affY_aux (z_mul_inverse' hz)

/-- Two valid triples denoting the same group element agree on everything
the pairing reads: `isInfinity` and `toAffine`. -/
theorem toAffine_eq_of_toPoint_eq {p q : G1} (hp : Valid p) (hq : Valid q)
    (h : toPoint p = toPoint q) :
    p.isInfinity = q.isInfinity ∧ p.toAffine = q.toAffine := by
  by_cases hpi : p.isInfinity = true
  · have hqi : q.isInfinity = true :=
      (isInfinity_iff hq).mpr (h ▸ (isInfinity_iff hp).mp hpi)
    refine ⟨by rw [hpi, hqi], ?_⟩
    have hpi' : p.z.isZero = true := hpi
    have hqi' : q.z.isZero = true := hqi
    simp only [G1.toAffine]
    rw [if_pos hpi', if_pos hqi']
  · have hqi : ¬ q.isInfinity = true := fun hqi =>
      hpi ((isInfinity_iff hp).mpr (h.trans ((isInfinity_iff hq).mp hqi)))
    refine ⟨by rw [Bool.eq_false_iff.mpr hpi, Bool.eq_false_iff.mpr hqi], ?_⟩
    have hpz : rep p 2 ≠ 0 := fun h0 => hpi (isZero_iff.mpr h0)
    have hqz : rep q 2 ≠ 0 := fun h0 => hqi (isZero_iff.mpr h0)
    rw [toPoint, toPoint, Point.toAffine_of_Z_ne_zero hp hpz,
      Point.toAffine_of_Z_ne_zero hq hqz, WeierstrassCurve.Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    refine Prod.ext ?_ ?_
    · have e1 := toAffine_fst hpi
      have e2 := toAffine_fst hqi
      exact e1.trans (hx.trans e2.symm)
    · have e1 := toAffine_snd hpi
      have e2 := toAffine_snd hqi
      exact e1.trans (hy.trans e2.symm)

end EthLib.Cryptography.Bls.G1

namespace EthLib.Cryptography.Bls

/-- `Embedded.ofG1` reads a point only through `isInfinity` and `toAffine`. -/
theorem Embedded.ofG1_congr {p q : G1} (hi : p.isInfinity = q.isInfinity)
    (ha : p.toAffine = q.toAffine) : Embedded.ofG1 p = Embedded.ofG1 q := by
  unfold Embedded.ofG1
  rw [hi, ha]

/-- `pairingCheck` on two pairs reads the second `G1` point only through
`isInfinity` and `Embedded.ofG1`. -/
theorem pairingCheck_congr_two (a : G1 × G2) {p p' : G1} (h : G2)
    (hi : p.isInfinity = p'.isInfinity) (he : Embedded.ofG1 p = Embedded.ofG1 p') :
    pairingCheck #[a, (p, h)] = pairingCheck #[a, (p', h)] := by
  simp only [pairingCheck, List.forIn_toArray, List.forIn_cons, List.forIn_nil]
  rw [hi, he]

end EthLib.Cryptography.Bls

namespace EthLibImpl.Cryptography.Bls.Mirror.Signatures

open EthLib.Cryptography.Bls

/-! ## 1. Subgroup test -/

/-- The endomorphism subgroup test agrees with the spec's `[r]P = O` on
valid points. -/
theorem g1InSubgroup_eq {p : G1} (h : G1.Valid p) : g1InSubgroup p = G1.inSubgroup p := by
  by_cases hinf : p.isInfinity = true
  · rw [g1InSubgroup, G1.inSubgroup, if_pos hinf, if_pos hinf]
  · rw [g1InSubgroup, G1.inSubgroup, if_neg hinf, if_neg hinf]
    exact (G1.inSubgroup_iff_endo h hinf).symm

/-! ## 2. Key validation -/

/-- The implementation's one-pass key validation is the spec's
`keyValidate` followed by `uncompress`. -/
theorem validatedPubkey_eq (b : ByteArray) :
    validatedPubkey b = (G1.keyValidate b >>= fun _ => G1.uncompress b) := by
  cases hu : G1.uncompress b with
  | error e =>
    simp only [validatedPubkey, G1.keyValidate, hu]
    rfl
  | ok p =>
    have hv := G1.valid_of_uncompress hu
    have hb : ∀ {α : Type} (f : G1 → Except BlsError α), (Except.ok p >>= f) = f p :=
      fun _ => rfl
    simp only [validatedPubkey, G1.keyValidate, hu, hb, g1InSubgroup_eq hv]
    by_cases hinf : p.isInfinity = true
    · simp only [hinf, if_true]
      rfl
    · by_cases hs : G1.inSubgroup p = true
      · simp only [hinf, hs]
        rfl
      · simp only [hinf, hs]
        rfl

/-! ## 4. Verifying the compressed aggregate -/

open private coreVerify signatureSubgroupCheck from EthLib.Cryptography.Bls.Signatures

private theorem ok_bind {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- `uncompress` succeeds only on 48-byte inputs. -/
theorem size_of_uncompress {b : ByteArray} {q : G1} (h : G1.uncompress b = .ok q) :
    b.size = 48 := by
  by_contra hne
  rw [G1.uncompress, if_pos hne] at h
  cases h

/-- `keyValidate` accepts a decoded finite point of the `r`-torsion subgroup. -/
theorem keyValidate_ok {b : ByteArray} {q : G1} (hq : G1.uncompress b = .ok q)
    (hqi : ¬ q.isInfinity = true) (hsub : Fr.modulus • G1.toPoint q = 0) :
    G1.keyValidate b = .ok () := by
  have hqv := G1.valid_of_uncompress hq
  have hks : G1.inSubgroup q = true := by
    rw [G1.inSubgroup, if_neg hqi, G1.isInfinity_iff (G1.valid_mulNat hqv _),
      G1.toPoint_mulNat hqv, hsub]
  simp only [G1.keyValidate, hq, ok_bind, hqi, hks]
  rfl

/-- `keyValidate` rejects the point at infinity. -/
theorem keyValidate_inf {b : ByteArray} {q : G1} (hq : G1.uncompress b = .ok q)
    (hqi : q.isInfinity = true) :
    G1.keyValidate b = .error .pointAtInfinity := by
  simp only [G1.keyValidate, hq, ok_bind, hqi]
  rfl

/-- The spec verifies the compressed aggregate key, which it decodes into
another triple for the same group element; the mirror verifies the
aggregate point itself. They agree on a valid point of the `r`-torsion
subgroup. -/
theorem coreVerify_compress {agg : G1} (hv : G1.Valid agg)
    (hsub : Fr.modulus • G1.toPoint agg = 0)
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.HashToCurve.hashToG2 msg dst
      = EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst)
    (msg sig : ByteArray) :
    coreVerify (G1.compress agg) msg sig = coreVerifyPoint agg msg sig := by
  by_cases hinf : agg.isInfinity = true
  · have hko : (G1.keyValidate (G1.compress agg)).isOk = false := by
      rw [G1.compress_of_isInfinity hinf]
      cases hu : G1.uncompress G1.infinityBytes with
      | error e =>
        simp only [G1.keyValidate, hu]
        rfl
      | ok q =>
        rw [keyValidate_inf hu (G1.isInfinity_of_uncompress_infinityBytes hu)]
        rfl
    simp only [coreVerify, coreVerifyPoint, hinf, hko, Bool.not_false, Bool.or_true, if_true]
  · obtain ⟨q, hq, hqp⟩ := G1.uncompress_compress_of_ne hv hinf
    have hqv := G1.valid_of_uncompress hq
    have hsize := size_of_uncompress hq
    have hqi : ¬ q.isInfinity = true := fun h =>
      hinf ((G1.isInfinity_iff hv).mpr (hqp.symm.trans ((G1.isInfinity_iff hqv).mp h)))
    have hko : (Except.ok () : Except BlsError Unit).isOk = true := rfl
    simp only [coreVerify, coreVerifyPoint, hinf, hsize, hq,
      keyValidate_ok hq hqi (hqp ▸ hsub), hko, ne_eq, not_true_eq_false, decide_false,
      Bool.not_true, Bool.or_false, Bool.false_eq_true, if_false]
    by_cases h96 : sig.size ≠ 96
    · rw [if_pos h96, if_pos h96]
    · rw [if_neg h96, if_neg h96]
      cases hs : G2.uncompress sig with
      | error e => rfl
      | ok s =>
        simp only [signatureSubgroupCheck,
          ← Mirror.G2.inSubgroup_eq (G2.valid_of_uncompress hs), hhash]
        by_cases hsg : Mirror.G2.inSubgroup s = true
        · simp only [hsg, Bool.not_true, Bool.false_eq_true, if_false]
          cases hh : EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
              EthLib.Cryptography.Bls.Signatures.DST with
          | error e => rfl
          | ok h =>
            simp only [hpair]
            have hneg : G1.toPoint (G1.neg q) = G1.toPoint (G1.neg agg) := by
              rw [G1.toPoint_neg hqv, G1.toPoint_neg hv, hqp]
            obtain ⟨hi, ha⟩ :=
              G1.toAffine_eq_of_toPoint_eq (G1.valid_neg hqv) (G1.valid_neg hv) hneg
            exact pairingCheck_congr_two _ h hi (Embedded.ofG1_congr hi ha)
        · simp only [hsg, Bool.not_false, if_true]

/-! ## 5. The aggregation loops

Both `fastAggregateVerify`s and both `ethAggregatePubkeys` run a `for` loop
over the keys whose body is, once its `do` sugar is unfolded, one of the
step functions below (`*_unfold` are `rfl`). `stepS_eq_stepM` and
`stepAS_eq_stepAM` show the spec's steps are the mirror's, so the loops
compute the same accumulator; `forIn_id_invariant` then shows that
accumulator is a sum of subgroup points, which `coreVerify_compress` needs. -/

/-- The mirror's `fastAggregateVerify` loop body. -/
def stepM (pk : ByteArray) (r : MProd (Option Bool) G1) :
    Id (ForInStep (MProd (Option Bool) G1)) :=
  if pk.size ≠ 48 then pure (.done ⟨some false, r.snd⟩)
  else match validatedPubkey pk with
    | .error _ => pure (.done ⟨some false, r.snd⟩)
    | .ok p => pure (.yield ⟨none, G1.add r.snd p⟩)

/-- The spec's `fastAggregateVerify` loop body. -/
def stepS (pk : ByteArray) (r : MProd (Option Bool) G1) :
    Id (ForInStep (MProd (Option Bool) G1)) :=
  if (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true then
    pure (.done ⟨some false, r.snd⟩)
  else match G1.uncompress pk with
    | .error _ => pure (.done ⟨some false, r.snd⟩)
    | .ok p => pure (.yield ⟨none, G1.add r.snd p⟩)

theorem fastAggregateVerify_unfold (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig =
      if pks.isEmpty = true then false
      else
        let r := (forIn pks ⟨none, G1.zero⟩ stepM).run
        match r.fst with
        | none => coreVerifyPoint r.snd msg sig
        | some a => a := rfl

theorem spec_fastAggregateVerify_unfold (pks : Array ByteArray) (msg sig : ByteArray) :
    EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg sig =
      if pks.isEmpty = true then false
      else
        let r := (forIn pks ⟨none, G1.zero⟩ stepS).run
        match r.fst with
        | none => coreVerify (G1.compress r.snd) msg sig
        | some a => a := rfl

/-- The mirror's `ethAggregatePubkeys` loop body. -/
def stepAM (pks : Array ByteArray) (i : Nat) (agg : G1) : Except BlsError (ForInStep G1) :=
  if pks[i]!.size ≠ 48 then throw (.badPubkeySize pks[i]!.size)
  else match validatedPubkey pks[i]! with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => pure (.yield (G1.add agg p))

/-- The spec's `ethAggregatePubkeys` loop body. -/
def stepAS (pks : Array ByteArray) (i : Nat) (agg : G1) : Except BlsError (ForInStep G1) :=
  if pks[i]!.size ≠ 48 then throw (.badPubkeySize pks[i]!.size)
  else if (!(G1.keyValidate pks[i]!).isOk) = true then throw (.invalidPubkey (some i))
  else match G1.uncompress pks[i]! with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => pure (.yield (G1.add agg p))

theorem ethAggregatePubkeys_unfold (pks : Array ByteArray) :
    ethAggregatePubkeys pks =
      if pks.isEmpty = true then throw .emptyPubkeyList
      else (forIn [:pks.size] G1.zero (stepAM pks)) >>= fun agg => pure (G1.compress agg) :=
  rfl

theorem spec_ethAggregatePubkeys_unfold (pks : Array ByteArray) :
    EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks =
      if pks.isEmpty = true then throw .emptyPubkeyList
      else (forIn [:pks.size] G1.zero (stepAS pks)) >>= fun agg => pure (G1.compress agg) :=
  rfl

/-- The spec's `fastAggregateVerify` step is the mirror's. -/
theorem stepS_eq_stepM : stepS = stepM := by
  funext pk r
  unfold stepS stepM
  by_cases hsz : pk.size ≠ 48
  · rw [if_pos hsz, if_pos (by simp [hsz])]
  · rw [if_neg hsz, validatedPubkey_eq]
    cases hk : G1.keyValidate pk with
    | error e =>
      rw [if_pos (by simp [hsz]; rfl)]
      rfl
    | ok u =>
      rw [if_neg (by simp [hsz]; rfl)]
      rfl

/-- The spec's `ethAggregatePubkeys` step is the mirror's. -/
theorem stepAS_eq_stepAM (pks : Array ByteArray) : stepAS pks = stepAM pks := by
  funext i agg
  unfold stepAS stepAM
  by_cases hsz : pks[i]!.size ≠ 48
  · rw [if_pos hsz, if_pos hsz]
  · rw [if_neg hsz, if_neg hsz, validatedPubkey_eq]
    cases hk : G1.keyValidate pks[i]! with
    | error e =>
      rw [if_pos (show (!(Except.error e : Except BlsError Unit).isOk) = true from rfl)]
      rfl
    | ok u =>
      rw [if_neg (show ¬ (!(Except.ok u : Except BlsError Unit).isOk) = true from
        fun h => Bool.false_ne_true h)]
      rfl

/-- An invariant of every state an `Id` loop passes through holds of its result. -/
theorem forIn_id_invariant {α β : Type} (xs : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) (I : β → Prop) (h0 : I init)
    (hf : ∀ a b, I b → I (f a b).run.value) : I (forIn xs init f).run := by
  rw [← Array.forIn_toList]
  generalize xs.toList = l
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have ha := hf a init h0
    revert ha
    show I (f a init).run.value → I (match (f a init).run with
      | ForInStep.done b => pure b
      | ForInStep.yield b => forIn l b f).run
    cases (f a init).run with
    | done b => exact id
    | yield b => exact ih b

/-- The accumulator invariant: a valid point of the `r`-torsion subgroup. -/
def Good (g : G1) : Prop := G1.Valid g ∧ Fr.modulus • G1.toPoint g = 0

theorem good_zero : Good G1.zero := by
  refine ⟨G1.valid_zero, ?_⟩
  rw [G1.toPoint_zero, nsmul_zero]

theorem good_add {a b : G1} (ha : Good a) (hb : Good b) : Good (G1.add a b) := by
  refine ⟨G1.valid_add ha.1 hb.1, ?_⟩
  rw [G1.toPoint_add ha.1 hb.1, nsmul_add, ha.2, hb.2, add_zero]

/-- A key accepted by `validatedPubkey` is a valid subgroup point. -/
theorem good_of_validatedPubkey {b : ByteArray} {p : G1} (h : validatedPubkey b = .ok p) :
    Good p := by
  cases hu : G1.uncompress b with
  | error e =>
    rw [validatedPubkey, hu] at h
    cases h
  | ok q =>
    have hv := G1.valid_of_uncompress hu
    simp only [validatedPubkey, hu, ok_bind, g1InSubgroup_eq hv] at h
    by_cases hinf : q.isInfinity = true
    · simp only [hinf, if_true] at h
      cases h
    · by_cases hs : G1.inSubgroup q = true
      · simp only [hinf, hs] at h
        cases h
        refine ⟨hv, ?_⟩
        rw [G1.inSubgroup, if_neg hinf, G1.isInfinity_iff (G1.valid_mulNat hv _),
          G1.toPoint_mulNat hv] at hs
        exact hs
      · simp only [hinf, hs] at h
        cases h

theorem stepM_good (pk : ByteArray) (r : MProd (Option Bool) G1) (hr : Good r.snd) :
    Good (stepM pk r).run.value.snd := by
  unfold stepM
  by_cases hsz : pk.size ≠ 48
  · rw [if_pos hsz]
    exact hr
  · rw [if_neg hsz]
    cases hp : validatedPubkey pk with
    | error e => exact hr
    | ok p => exact good_add hr (good_of_validatedPubkey hp)

/-- **Main theorem (FastAggregateVerify).** The mirrored implementation
returns the spec's answer, given the pairing and hash-to-curve layers. -/
theorem fastAggregateVerify_eq
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.HashToCurve.hashToG2 msg dst
      = EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig
      = EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg sig := by
  rw [fastAggregateVerify_unfold, spec_fastAggregateVerify_unfold, stepS_eq_stepM]
  by_cases he : pks.isEmpty = true
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    have h0 : Good (⟨none, G1.zero⟩ : MProd (Option Bool) G1).snd := good_zero
    have hI := forIn_id_invariant pks (⟨none, G1.zero⟩ : MProd (Option Bool) G1) stepM
      (fun r => Good r.snd) h0 stepM_good
    simp only
    generalize (forIn pks ⟨none, G1.zero⟩ stepM).run = r at hI ⊢
    obtain ⟨o, g⟩ := r
    cases o with
    | none => exact (coreVerify_compress hI.1 hI.2 hpair hhash msg sig).symm
    | some a => rfl

/-- **Main theorem (`eth_fast_aggregate_verify`).** -/
theorem ethFastAggregateVerify_eq
    (hpair : ∀ pairs, Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs)
    (hhash : ∀ msg dst, Mirror.HashToCurve.hashToG2 msg dst
      = EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    ethFastAggregateVerify pks msg sig
      = EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify pks msg sig := by
  unfold ethFastAggregateVerify EthLib.Cryptography.Bls.Signatures.ethFastAggregateVerify
  rw [fastAggregateVerify_eq hpair hhash]

/-- **Main theorem (`eth_aggregate_pubkeys`).** The mirrored implementation
returns the spec's result, errors included. -/
theorem ethAggregatePubkeys_eq (pks : Array ByteArray) :
    ethAggregatePubkeys pks = EthLib.Cryptography.Bls.Signatures.ethAggregatePubkeys pks := by
  rw [ethAggregatePubkeys_unfold, spec_ethAggregatePubkeys_unfold, stepAS_eq_stepAM]

end EthLibImpl.Cryptography.Bls.Mirror.Signatures
