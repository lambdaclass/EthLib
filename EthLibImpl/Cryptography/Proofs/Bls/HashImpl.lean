import EthLibImpl.Cryptography.Proofs.Bls.G2
import EthLibImpl.Cryptography.Proofs.Bls.CompressG2
import EthLibImpl.Cryptography.Bls.HashToCurve
import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.HashMath
import EthLib.Cryptography.Proofs.IdLoops

/-!
# Proofs: the implementation's hash-to-curve computes the spec's

`EthLibImpl.Cryptography.Bls.HashToCurve` against the spec-level mirror
`Mirror.HashToCurve` (and through `Mirror.HashToCurve.hashToG2_eq`, the spec's
`HashToCurve.hashToG2`). The constants and the functions that name the spec's private
definitions live in `EthLibImpl.Cryptography.Bls.HashConst`; everything else is in
`EthLibImpl.Cryptography.Bls.HashToCurve`. `hashToG2_spec` is the main result.

Kernel notes. The implementation's `Fp2.sqrt` is a big computation, so the kernel must never be
asked to compare two differently shaped terms that match on it. `swuG` therefore reuses the
implementation's own matcher and panic term, so that `simpleSwuWith = swuG ...` holds by `rfl`,
and the proofs then run on the parametrised version.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero
set_option linter.unusedSimpArgs false

namespace EthLibImpl.Cryptography.Bls.HashToCurve
open EthLib.Cryptography

theorem foldl_size_preserved {F : ByteArray → Nat → ByteArray}
    (h : ∀ acc j, (F acc j).size = acc.size) (l : List Nat) (init : ByteArray) :
    (l.foldl F init).size = init.size := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, h]

theorem size_set' (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  cases a; simp [ByteArray.set!, ByteArray.size]

theorem sha256_size (m : ByteArray) : (Bls.Sha256.hash m).size = 32 := by
  unfold Bls.Sha256.hash
  simp only [Id.run, bind, pure]
  rw [IdLoops.forIn_range_yield]
  refine (foldl_size_preserved (fun acc j => by simp only [size_set']) _ _).trans ?_
  show (Array.replicate 32 (0:UInt8)).size = 32
  simp

open private sha256OutputSize from EthLib.Cryptography.Bls.HashToCurve

theorem forIn_push_list {ε : Type} (g : Nat → Array ByteArray → ByteArray) (l : List Nat)
    (init : Array ByteArray) :
    forIn (m := Except ε) l init (fun i r => Except.ok (ForInStep.yield (r.push (g i r)))) =
      Except.ok (l.foldl (fun r i => r.push (g i r)) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, List.foldl_cons]; exact ih _

theorem foldl_push_facts (g : Nat → Array ByteArray → ByteArray)
    (hg : ∀ i r, (g i r).size = 32) (l : List Nat) (init : Array ByteArray)
    (hi : ∀ x ∈ init, x.size = 32) :
    (l.foldl (fun r i => r.push (g i r)) init).size = init.size + l.length ∧
      ∀ x ∈ l.foldl (fun r i => r.push (g i r)) init, x.size = 32 := by
  induction l generalizing init with
  | nil => exact ⟨rfl, hi⟩
  | cons a l ih =>
    rw [List.foldl_cons]
    have hi' : ∀ x ∈ init.push (g a init), x.size = 32 := by
      intro x hx
      rw [Array.mem_push] at hx
      rcases hx with hx | hx
      · exact hi x hx
      · rw [hx]; exact hg _ _
    obtain ⟨h1, h2⟩ := ih _ hi'
    refine ⟨?_, h2⟩
    rw [h1]; simp; omega

theorem foldl_append_size (v : List ByteArray) (hv : ∀ x ∈ v, x.size = 32) (acc : ByteArray) :
    (v.foldl (fun x1 x2 => x1 ++ x2) acc).size = acc.size + 32 * v.length := by
  induction v generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))]
    rw [ByteArray.size_append, hv a (List.mem_cons_self)]
    simp; omega

theorem expand_size (msg dst : ByteArray) (n : Nat) (u : ByteArray)
    (h : Bls.HashToCurve.expandMessageXmd msg dst n = .ok u) : u.size = n := by
  have h32 : sha256OutputSize = 32 := rfl
  unfold Bls.HashToCurve.expandMessageXmd at h
  simp only [bind, Except.bind, pure, Except.pure, h32] at h
  have key : ∀ (ell : Nat) (init : Array ByteArray) (g : Nat → Array ByteArray → ByteArray)
      (hg : ∀ i r, (g i r).size = 32) (hi : ∀ x ∈ init, x.size = 32) (hs : init.size = 1)
      (v : Array ByteArray)
      (hf : forIn (m := Except EthLib.Cryptography.Bls.BlsError) [2:ell+1] init
          (fun i r => Except.ok (ForInStep.yield (r.push (g i r)))) = Except.ok v)
      (hn : n ≤ 32 * ell),
      ((Array.foldl (fun x1 x2 => x1 ++ x2) ByteArray.empty v).extract 0 n).size = n := by
    intro ell init g hg hi hs v hf hn
    rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_push_list] at hf
    obtain ⟨hs1, hs2⟩ := foldl_push_facts g hg
      (List.range' [2:ell + 1].start [2:ell + 1].size [2:ell + 1].step) init hi
    have hv : List.foldl (fun r i => r.push (g i r)) init
        (List.range' [2:ell + 1].start [2:ell + 1].size [2:ell + 1].step) = v := Except.ok.inj hf
    rw [hv] at hs1 hs2

    rw [ByteArray.size_extract]
    have hsz : (Array.foldl (fun x1 x2 => x1 ++ x2) ByteArray.empty v).size = 32 * v.size := by
      rw [← Array.foldl_toList, foldl_append_size _ (fun x hx => hs2 x (Array.mem_toList_iff.mp hx))]
      simp
    rw [hsz]
    simp only [List.length_range', Std.Legacy.Range.size] at hs1
    omega
  have h1 : ¬ n > 65535 := fun hc => by rw [if_pos hc] at h; cases h
  have h2 : ¬ (n + 32 - 1) / 32 > 255 := fun hc => by rw [if_neg h1, if_pos hc] at h; cases h
  rw [if_neg h1, if_neg h2] at h
  split at h
  · cases h
  · rename_i v hf
    injection h with h
    rw [← h]
    refine key _ _ _ ?_ ?_ ?_ v hf ?_
    · intro i r; exact sha256_size _
    · intro x hx
      simp at hx
      rw [hx]; exact sha256_size _
    · simp
    · omega

theorem forIn_list_sim_idx {ε β β' : Type} (inv : Nat → β → β' → Prop)
    (f : Nat → β → Except ε (ForInStep β)) (f' : Nat → β' → Except ε (ForInStep β'))
    (n : Nat)
    (hstep : ∀ i, i < n → ∀ b b', inv i b b' →
      ∃ x x', f i b = .ok (.yield x) ∧ f' i b' = .ok (.yield x') ∧ inv (i + 1) x x') :
    ∀ (k s : Nat), s + k ≤ n → ∀ (init : β) (init' : β'), inv s init init' →
      ∃ r r', forIn (m := Except ε) (List.range' s k) init f = .ok r ∧
        forIn (m := Except ε) (List.range' s k) init' f' = .ok r' ∧ inv (s + k) r r' := by
  intro k
  induction k with
  | zero => intro s _ init init' h; exact ⟨init, init', rfl, rfl, h⟩
  | succ k ih =>
    intro s hs init init' h
    obtain ⟨x, x', hx, hx', hxx⟩ := hstep s (by omega) init init' h
    obtain ⟨r, r', hr, hr', hrr⟩ := ih (s + 1) (by omega) x x' hxx
    refine ⟨r, r', ?_, ?_, ?_⟩
    · rw [List.range'_succ, List.forIn_cons, hx]; exact hr
    · rw [List.range'_succ, List.forIn_cons, hx']; exact hr'
    · have : s + (k + 1) = s + 1 + k := by omega
      rw [this]; exact hrr

theorem forIn_range_sim_idx {ε β β' : Type} (inv : Nat → β → β' → Prop)
    (n : Nat) (f : Nat → β → Except ε (ForInStep β)) (f' : Nat → β' → Except ε (ForInStep β'))
    (hstep : ∀ i, i < n → ∀ b b', inv i b b' →
      ∃ x x', f i b = .ok (.yield x) ∧ f' i b' = .ok (.yield x') ∧ inv (i + 1) x x')
    (init : β) (init' : β') (h0 : inv 0 init init') :
    ∃ r r', forIn (m := Except ε) [:n] init f = .ok r ∧
      forIn (m := Except ε) [:n] init' f' = .ok r' ∧ inv n r r' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  have := forIn_list_sim_idx inv f f' n hstep n 0 (by omega) init init' h0
  simpa [Std.Legacy.Range.size] using this



end EthLibImpl.Cryptography.Bls.HashToCurve

namespace EthLibImpl.Cryptography.Bls.HashConst

open private fpFromBytesL sgn0Fp sgn0Fp2 Z Aprime Bprime fp2 k10 k11 k12 k13 k20 k21 k30 k31 k32 k33 k40
  k41 k42 c1Psi c2Psi c1Psi2 mulNegX blsAbsX from EthLib.Cryptography.Bls.HashToCurve

theorem fpFromBytesL_eq (b : ByteArray) :
    fpFromBytesL b = EthLib.Cryptography.Bls.Fp.ofNat (EthLib.Cryptography.Bls.Fp.bytesBEToNat b) :=
  rfl

theorem Z_spec : HashToCurve.Z.Canonical ∧ HashToCurve.Z.toSpec = Z := by
  have h1 := G1.neg_c (a := Fp.ofNat 2) (Fp.ofNat_canonical 2)
  have h2 := G1.neg_c (a := Fp.one) Fp.one_canonical
  refine ⟨Fp2.canonical_mk h1 h2, ?_⟩
  show (Fp2.mk _ _).toSpec = _
  rw [Fp2.toSpec_mk, G1.neg_v (Fp.ofNat_canonical 2), G1.neg_v Fp.one_canonical,
    Fp.val_ofNat, Fp.val_one]
  rfl

theorem Aprime_spec : HashToCurve.Aprime.Canonical ∧ HashToCurve.Aprime.toSpec = Aprime := by
  refine ⟨Fp2.canonical_mk Fp.zero_canonical (Fp.ofNat_canonical _), ?_⟩
  show (Fp2.mk _ _).toSpec = _
  rw [Fp2.toSpec_mk, Fp.val_zero, Fp.val_ofNat]
  rfl

theorem Bprime_spec : HashToCurve.Bprime.Canonical ∧ HashToCurve.Bprime.toSpec = Bprime := by
  refine ⟨Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _), ?_⟩
  show (Fp2.mk _ _).toSpec = _
  rw [Fp2.toSpec_mk]; simp only [Fp.val_ofNat]
  rfl

theorem fp2_spec (c0 c1 : Nat) :
    (HashToCurve.fp2 c0 c1).Canonical ∧ (HashToCurve.fp2 c0 c1).toSpec = fp2 c0 c1 := by
  refine ⟨Fp2.canonical_mk (Fp.ofNat_canonical _) (Fp.ofNat_canonical _), ?_⟩
  show (Fp2.mk _ _).toSpec = _
  rw [Fp2.toSpec_mk]; simp only [Fp.val_ofNat]
  rfl

theorem k10_spec : HashToCurve.k10.Canonical ∧ HashToCurve.k10.toSpec = k10 := fp2_spec _ _
theorem k11_spec : HashToCurve.k11.Canonical ∧ HashToCurve.k11.toSpec = k11 := fp2_spec _ _
theorem k12_spec : HashToCurve.k12.Canonical ∧ HashToCurve.k12.toSpec = k12 := fp2_spec _ _
theorem k13_spec : HashToCurve.k13.Canonical ∧ HashToCurve.k13.toSpec = k13 := fp2_spec _ _
theorem k20_spec : HashToCurve.k20.Canonical ∧ HashToCurve.k20.toSpec = k20 := fp2_spec _ _
theorem k21_spec : HashToCurve.k21.Canonical ∧ HashToCurve.k21.toSpec = k21 := fp2_spec _ _
theorem k30_spec : HashToCurve.k30.Canonical ∧ HashToCurve.k30.toSpec = k30 := fp2_spec _ _
theorem k31_spec : HashToCurve.k31.Canonical ∧ HashToCurve.k31.toSpec = k31 := fp2_spec _ _
theorem k32_spec : HashToCurve.k32.Canonical ∧ HashToCurve.k32.toSpec = k32 := fp2_spec _ _
theorem k33_spec : HashToCurve.k33.Canonical ∧ HashToCurve.k33.toSpec = k33 := fp2_spec _ _
theorem k40_spec : HashToCurve.k40.Canonical ∧ HashToCurve.k40.toSpec = k40 := fp2_spec _ _
theorem k41_spec : HashToCurve.k41.Canonical ∧ HashToCurve.k41.toSpec = k41 := fp2_spec _ _
theorem k42_spec : HashToCurve.k42.Canonical ∧ HashToCurve.k42.toSpec = k42 := fp2_spec _ _

theorem c1Psi_spec : HashToCurve.c1Psi.Canonical ∧ HashToCurve.c1Psi.toSpec = c1Psi := by
  have hx : (Fp2.mk Fp.one Fp.one).Canonical := Fp2.canonical_mk Fp.one_canonical Fp.one_canonical
  have hp := Fp2.powNat_canonical hx ((Fp.modulus - 1) / 3)
  refine ⟨Fp2.inverse_canonical hp, ?_⟩
  show (Fp2.inverse _).toSpec = _
  rw [Fp2.toSpec_inverse hp, Fp2.toSpec_powNat hx, Fp2.toSpec_mk, Fp.val_one]
  rfl

theorem c2Psi_spec : HashToCurve.c2Psi.Canonical ∧ HashToCurve.c2Psi.toSpec = c2Psi := by
  have hx : (Fp2.mk Fp.one Fp.one).Canonical := Fp2.canonical_mk Fp.one_canonical Fp.one_canonical
  have hp := Fp2.powNat_canonical hx ((Fp.modulus - 1) / 2)
  refine ⟨Fp2.inverse_canonical hp, ?_⟩
  show (Fp2.inverse _).toSpec = _
  rw [Fp2.toSpec_inverse hp, Fp2.toSpec_powNat hx, Fp2.toSpec_mk, Fp.val_one]
  rfl

theorem c1Psi2_spec : HashToCurve.c1Psi2.Canonical ∧ HashToCurve.c1Psi2.toSpec = c1Psi2 := by
  have h2 := Fp.ofNat_canonical 2
  have hp := Fp.powNat_canonical h2 ((Fp.modulus - 1) / 3)
  have hi := Fp.inverse_canonical hp
  refine ⟨Fp2.canonical_mk hi Fp.zero_canonical, ?_⟩
  show (Fp2.mk _ _).toSpec = _
  rw [Fp2.toSpec_mk, Fp.val_inverse hp, Fp.val_powNat_powNat h2, Fp.val_ofNat, Fp.val_zero]
  rfl

theorem sgn0Fp2_spec {u : Fp2} (hu : u.Canonical) :
    HashToCurve.sgn0Fp2 u = sgn0Fp2 u.toSpec := by
  unfold HashToCurve.sgn0Fp2 sgn0Fp2 sgn0Fp
  rw [Fp.parity_eq, Fp.parity_eq, Fp2.fp_isZero_eq hu.1]
  rfl

theorem mulNegX_spec {P : G2} (hP : G2.Canonical P) :
    (HashToCurve.mulNegX P).Canonical ∧ G2.toSpec (HashToCurve.mulNegX P) = mulNegX (G2.toSpec P) := by
  obtain ⟨h1, h2⟩ := G2.mulNatW_spec' hP G2.absXWord
  obtain ⟨h3, h4⟩ := G2.neg_spec h1
  refine ⟨h3, ?_⟩
  show G2.toSpec (G2.neg (G2.mulNatW P G2.absXWord)) = _
  rw [h4, h2, G2.absXWord_toNat]
  rfl

open private fpFromBytesL from EthLib.Cryptography.Bls.HashToCurve

/-- `hashToFieldFp2` computes the spec's, and its output has `count` canonical elements. -/
theorem hashToFieldFp2_spec_aux (msg dst : ByteArray) (count : Nat) :
    (HashToCurve.hashToFieldFp2 msg dst count).map (Array.map Fp2.toSpec) =
      EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2 msg dst count ∧
    ∀ us, HashToCurve.hashToFieldFp2 msg dst count = .ok us →
      us.size = count ∧ ∀ x ∈ us, x.Canonical := by
  unfold HashToCurve.hashToFieldFp2 EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2
  dsimp only
  rcases hu : EthLib.Cryptography.Bls.HashToCurve.expandMessageXmd msg dst (count * 2 * 64)
    with e | uniform
  · refine ⟨?_, fun us h => ?_⟩
    · simp only [bind, Except.bind, Except.map]
    · simp only [bind, Except.bind] at h; cases h
  · have hsz := HashToCurve.expand_size _ _ _ _ hu
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨r, r', hr, hr', hinv⟩ := HashToCurve.forIn_range_sim_idx
      (fun (i : Nat) (out : Array Fp2) (out' : Array EthLib.Cryptography.Bls.Fp2) =>
        out' = out.map Fp2.toSpec ∧ out.size = i ∧ ∀ x ∈ out, x.Canonical)
      count
      (fun i r => Except.ok (ForInStep.yield
        (r.push (Fp2.mk (Fp.ofBytes64BE uniform (64 * (i * 2)))
          (Fp.ofBytes64BE uniform (64 * (i * 2 + 1)))))))
      (fun i r => Except.ok (ForInStep.yield
        (r.push { c0 := fpFromBytesL (uniform.extract (64 * (i * 2)) (64 * (i * 2) + 64)),
                  c1 := fpFromBytesL (uniform.extract (64 * (i * 2 + 1)) (64 * (i * 2 + 1) + 64)) })))
      (by
        intro i hi b b' ⟨hb1, hb2, hb3⟩
        have hb0 : 64 * (i * 2) + 64 ≤ uniform.size := by rw [hsz]; omega
        have hb1' : 64 * (i * 2 + 1) + 64 ≤ uniform.size := by rw [hsz]; omega
        obtain ⟨c0, v0⟩ := Fp.ofBytes64BE_spec uniform _ hb0
        obtain ⟨c1, v1⟩ := Fp.ofBytes64BE_spec uniform _ hb1'
        refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
        · have hmk : (⟨fpFromBytesL (uniform.extract (64 * (i * 2)) (64 * (i * 2) + 64)),
              fpFromBytesL (uniform.extract (64 * (i * 2 + 1)) (64 * (i * 2 + 1) + 64))⟩ :
              EthLib.Cryptography.Bls.Fp2) =
              Fp2.toSpec (Fp2.mk (Fp.ofBytes64BE uniform (64 * (i * 2)))
                (Fp.ofBytes64BE uniform (64 * (i * 2 + 1)))) := by
            rw [Fp2.toSpec_mk, v0, v1]
            rfl
          rw [hb1, Array.map_push, hmk]
        · rw [Array.size_push, hb2]
        · intro x hx
          rw [Array.mem_push] at hx
          rcases hx with hx | hx
          · exact hb3 x hx
          · rw [hx]; exact Fp2.canonical_mk c0 c1)
      (Array.mkEmpty count) (Array.mkEmpty count)
      ⟨by simp [Array.mkEmpty], by simp [Array.mkEmpty], fun x hx => by simp [Array.mkEmpty] at hx⟩
    rw [hr, hr']
    refine ⟨?_, fun us h => ?_⟩
    · show Except.ok (Array.map Fp2.toSpec r) = Except.ok r'
      rw [hinv.1]
    · injection h with h
      subst h
      exact ⟨hinv.2.1, hinv.2.2⟩


end EthLibImpl.Cryptography.Bls.HashConst

namespace EthLibImpl.Cryptography.Bls.HashToCurve

open scoped EthLib.Cryptography.Bls.Fp2
open EthLib.Cryptography.Bls (BlsError)

local notation "SFp2" => EthLib.Cryptography.Bls.Fp2
local notation "SG2" => EthLib.Cryptography.Bls.G2

theorem x1Exceptional_spec :
    x1Exceptional.Canonical ∧ x1Exceptional.toSpec = Mirror.HashToCurve.x1Exceptional := by
  obtain ⟨hZ, vZ⟩ := HashConst.Z_spec
  obtain ⟨hA, vA⟩ := HashConst.Aprime_spec
  obtain ⟨hB, vB⟩ := HashConst.Bprime_spec
  have hZA : (Z * Aprime).Canonical := Fp2.canonical_hMul hZ hA
  refine ⟨Fp2.div_canonical hB hZA, ?_⟩
  unfold x1Exceptional Mirror.HashToCurve.x1Exceptional
  rw [Fp2.toSpec_div hB hZA, Fp2.toSpec_hMul hZ hA, vZ, vA, vB]

theorem negBOverA_spec :
    negBOverA.Canonical ∧ negBOverA.toSpec = Mirror.HashToCurve.negBOverA := by
  obtain ⟨hA, vA⟩ := HashConst.Aprime_spec
  obtain ⟨hB, vB⟩ := HashConst.Bprime_spec
  have hnB : (-Bprime).Canonical := Fp2.canonical_hNeg hB
  refine ⟨Fp2.div_canonical hnB hA, ?_⟩
  unfold negBOverA Mirror.HashToCurve.negBOverA
  rw [Fp2.toSpec_div hnB hA, Fp2.toSpec_hNeg hB, vA, vB]

theorem swuDenom_spec {u : Fp2} (hu : u.Canonical) :
    (swuDenom u).1.Canonical ∧ (swuDenom u).2.Canonical ∧
      ((swuDenom u).1.toSpec, (swuDenom u).2.toSpec) = Mirror.HashToCurve.swuDenom u.toSpec := by
  obtain ⟨hZ, vZ⟩ := HashConst.Z_spec
  have hs := Fp2.sqr_canonical hu
  have hzu : (Z * u.sqr).Canonical := Fp2.canonical_hMul hZ hs
  have hzz := Fp2.sqr_canonical hzu
  refine ⟨hzu, Fp2.canonical_hAdd hzz hzu, ?_⟩
  unfold swuDenom Mirror.HashToCurve.swuDenom
  dsimp only
  rw [Fp2.toSpec_hAdd hzz hzu, Fp2.toSpec_sqr hzu, Fp2.toSpec_hMul hZ hs, Fp2.toSpec_sqr hu, vZ]


/-- A pair of implementation elements is canonical and stands for a pair of spec elements. -/
def PRel (p : Fp2 × Fp2) (q : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) : Prop :=
  p.1.Canonical ∧ p.2.Canonical ∧ (p.1.toSpec, p.2.toSpec) = q



def swuG (x1e nBA A B : Fp2) (sq : Fp2 → Except BlsError Fp2) (sgn : Fp2 → Bool)
    (u zu2 denom denomInv : Fp2) : Fp2 × Fp2 :=
  let x1 := if denom.isZero then x1e else nBA * (Fp2.one + denomInv)
  let gx1 := x1.sqr * x1 + A * x1 + B
  simpleSwuWith.match_1 (fun _ => Fp2 × Fp2) (sq gx1)
    (fun y =>
      let y := if sgn u = sgn y then y else -y
      (x1, y))
    (fun _ =>
      let x2 := zu2 * x1
      let gx2 := x2.sqr * x2 + A * x2 + B
      simpleSwuWith.match_1 (fun _ => Fp2 × Fp2) (sq gx2)
        (fun y =>
          let y := if sgn u = sgn y then y else -y
          (x2, y))
        (fun _ =>
          @panicWithPosWithDecl (Fp2 × Fp2) _ "EthLibImpl.Cryptography.Bls.HashToCurve"
            "EthLibImpl.Cryptography.Bls.HashToCurve.simpleSwuWith" 92 18
            "neither gx1 nor gx2 is a square"))

theorem simpleSwuWith_eq_G : simpleSwuWith =
    swuG x1Exceptional negBOverA Aprime Bprime Fp2.sqrt sgn0Fp2 := rfl

theorem match_ok {motive : Except BlsError Fp2 → Sort 1} (y : Fp2)
    (h1 : (y : Fp2) → motive (.ok y)) (h2 : (a : BlsError) → motive (.error a)) :
    simpleSwuWith.match_1 motive (.ok y) h1 h2 = h1 y := rfl

theorem match_error {motive : Except BlsError Fp2 → Sort 1} (e : BlsError)
    (h1 : (y : Fp2) → motive (.ok y)) (h2 : (a : BlsError) → motive (.error a)) :
    simpleSwuWith.match_1 motive (.error e) h1 h2 = h2 e := rfl

/-- The mirror's SSWU with the constants, the square root and `sgn0` as parameters. -/
def swuG' (x1e nBA A B : EthLib.Cryptography.Bls.Fp2)
    (sq : EthLib.Cryptography.Bls.Fp2 → Except BlsError EthLib.Cryptography.Bls.Fp2)
    (sgn : EthLib.Cryptography.Bls.Fp2 → Bool)
    (u zu2 denom denomInv : EthLib.Cryptography.Bls.Fp2) :
    EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2 :=
  let x1 := if denom.isZero then x1e else nBA * (EthLib.Cryptography.Bls.Fp2.one + denomInv)
  let gx1 := x1 * x1 * x1 + A * x1 + B
  Mirror.HashToCurve.simpleSwuWith.match_1
    (fun _ => EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) (sq gx1)
    (fun y =>
      let y := if sgn u = sgn y then y else -y
      (x1, y))
    (fun _ =>
      let x2 := zu2 * x1
      let gx2 := x2 * x2 * x2 + A * x2 + B
      Mirror.HashToCurve.simpleSwuWith.match_1
        (fun _ => EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) (sq gx2)
        (fun y =>
          let y := if sgn u = sgn y then y else -y
          (x2, y))
        (fun _ =>
          @panicWithPosWithDecl (EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) _
            "EthLibImpl.Cryptography.Proofs.Bls.MirrorHash"
            "EthLibImpl.Cryptography.Bls.Mirror.HashToCurve.simpleSwuWith" 67 18
            "neither gx1 nor gx2 is a square"))

theorem match_ok' {motive : Except BlsError EthLib.Cryptography.Bls.Fp2 → Sort 1}
    (y : EthLib.Cryptography.Bls.Fp2)
    (h1 : (y : EthLib.Cryptography.Bls.Fp2) → motive (.ok y))
    (h2 : (a : BlsError) → motive (.error a)) :
    Mirror.HashToCurve.simpleSwuWith.match_1 motive (.ok y) h1 h2 = h1 y := rfl

theorem match_error' {motive : Except BlsError EthLib.Cryptography.Bls.Fp2 → Sort 1}
    (e : BlsError)
    (h1 : (y : EthLib.Cryptography.Bls.Fp2) → motive (.ok y))
    (h2 : (a : BlsError) → motive (.error a)) :
    Mirror.HashToCurve.simpleSwuWith.match_1 motive (.error e) h1 h2 = h2 e := rfl

theorem sel_neg {sgn : Fp2 → Bool} {sgn' : EthLib.Cryptography.Bls.Fp2 → Bool}
    (hsgn : ∀ y : Fp2, y.Canonical → sgn y = sgn' y.toSpec) {u y : Fp2}
    (hu : u.Canonical) (hy : y.Canonical) :
    (if sgn u = sgn y then y else -y).Canonical ∧
      (if sgn u = sgn y then y else -y).toSpec =
        if sgn' u.toSpec = sgn' y.toSpec then y.toSpec else -y.toSpec := by
  rw [hsgn u hu, hsgn y hy]
  by_cases h : sgn' u.toSpec = sgn' y.toSpec
  · rw [if_pos h, if_pos h]; exact ⟨hy, rfl⟩
  · rw [if_neg h, if_neg h]
    exact ⟨Fp2.canonical_hNeg hy, Fp2.toSpec_hNeg hy⟩

theorem swuG_spec (x1e nBA A B : Fp2) (x1e' nBA' A' B' : EthLib.Cryptography.Bls.Fp2)
    (hx : x1e.Canonical) (hxv : x1e.toSpec = x1e')
    (hn : nBA.Canonical) (hnv : nBA.toSpec = nBA')
    (hA : A.Canonical) (hAv : A.toSpec = A') (hB : B.Canonical) (hBv : B.toSpec = B')
    (sq : Fp2 → Except BlsError Fp2)
    (sq' : EthLib.Cryptography.Bls.Fp2 → Except BlsError EthLib.Cryptography.Bls.Fp2)
    (hsq : ∀ a : Fp2, a.Canonical → (sq a).map Fp2.toSpec = sq' a.toSpec ∧
      ∀ c, sq a = .ok c → c.Canonical)
    (sgn : Fp2 → Bool) (sgn' : EthLib.Cryptography.Bls.Fp2 → Bool)
    (hsgn : ∀ y : Fp2, y.Canonical → sgn y = sgn' y.toSpec)
    (hdef : (default : Fp2 × Fp2).1.Canonical ∧ (default : Fp2 × Fp2).2.Canonical ∧
      (((default : Fp2 × Fp2).1.toSpec, (default : Fp2 × Fp2).2.toSpec) =
        (default : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)))
    {u zu2 denom di : Fp2} (hu : u.Canonical) (hz : zu2.Canonical) (hd : denom.Canonical)
    (hi : di.Canonical) :
    PRel (swuG x1e nBA A B sq sgn u zu2 denom di)
      (swuG' x1e' nBA' A' B' sq' sgn' u.toSpec zu2.toSpec denom.toSpec di.toSpec) := by
  unfold swuG swuG'
  dsimp only
  rw [Fp2.isZero_eq hd]
  -- x1
  have hx1 : (if denom.isZero = true then x1e else nBA * (Fp2.one + di)).Canonical ∧
      (if denom.isZero = true then x1e else nBA * (Fp2.one + di)).toSpec =
        if denom.isZero = true then x1e' else nBA' * (EthLib.Cryptography.Bls.Fp2.one + di.toSpec) := by
    by_cases h : denom.isZero = true
    · rw [if_pos h, if_pos h]; exact ⟨hx, hxv⟩
    · rw [if_neg h, if_neg h]
      have h1 := Fp2.canonical_hAdd Fp2.one_canonical hi
      refine ⟨Fp2.canonical_hMul hn h1, ?_⟩
      rw [Fp2.toSpec_hMul hn h1, Fp2.toSpec_hAdd Fp2.one_canonical hi, Fp2.toSpec_one, hnv]
  obtain ⟨hx1c, hx1v⟩ := hx1
  generalize (if denom.isZero = true then x1e else nBA * (Fp2.one + di)) = x1 at hx1c hx1v ⊢
  generalize (if denom.isZero = true then x1e' else nBA' * (EthLib.Cryptography.Bls.Fp2.one + di.toSpec)) = x1' at hx1v ⊢
  subst hx1v
  have hs1 := Fp2.sqr_canonical hx1c
  have hm1 := Fp2.canonical_hMul hs1 hx1c
  have hA1 := Fp2.canonical_hMul hA hx1c
  have hgc : (x1.sqr * x1 + A * x1 + B).Canonical :=
    Fp2.canonical_hAdd (Fp2.canonical_hAdd hm1 hA1) hB
  have hgv : (x1.sqr * x1 + A * x1 + B).toSpec =
      x1.toSpec * x1.toSpec * x1.toSpec + A' * x1.toSpec + B' := by
    rw [Fp2.toSpec_hAdd (Fp2.canonical_hAdd hm1 hA1) hB, Fp2.toSpec_hAdd hm1 hA1,
      Fp2.toSpec_hMul hs1 hx1c, Fp2.toSpec_sqr hx1c, Fp2.toSpec_hMul hA hx1c, hAv, hBv]
  rw [← hgv]
  generalize x1.sqr * x1 + A * x1 + B = G at hgc ⊢
  obtain ⟨hsm, hsc⟩ := hsq G hgc
  rw [← hsm]
  rcases hs : sq G with e | y
  · simp only [Except.map, match_error, match_error']
    have hx2c : (zu2 * x1).Canonical := Fp2.canonical_hMul hz hx1c
    have hx2v : (zu2 * x1).toSpec = zu2.toSpec * x1.toSpec := Fp2.toSpec_hMul hz hx1c
    rw [← hx2v]
    generalize zu2 * x1 = x2 at hx2c hx2v ⊢
    have hs2 := Fp2.sqr_canonical hx2c
    have hm2 := Fp2.canonical_hMul hs2 hx2c
    have hA2 := Fp2.canonical_hMul hA hx2c
    have hgc2 : (x2.sqr * x2 + A * x2 + B).Canonical :=
      Fp2.canonical_hAdd (Fp2.canonical_hAdd hm2 hA2) hB
    have hgv2 : (x2.sqr * x2 + A * x2 + B).toSpec =
        x2.toSpec * x2.toSpec * x2.toSpec + A' * x2.toSpec + B' := by
      rw [Fp2.toSpec_hAdd (Fp2.canonical_hAdd hm2 hA2) hB, Fp2.toSpec_hAdd hm2 hA2,
        Fp2.toSpec_hMul hs2 hx2c, Fp2.toSpec_sqr hx2c, Fp2.toSpec_hMul hA hx2c, hAv, hBv]
    rw [← hgv2]
    generalize x2.sqr * x2 + A * x2 + B = G2 at hgc2 ⊢
    obtain ⟨hsm2, hsc2⟩ := hsq G2 hgc2
    rw [← hsm2]
    rcases hs2' : sq G2 with e2 | y2
    · simp only [Except.map, match_error, match_error', Mirror.HashToCurve.panicWPD_eq]
      exact hdef
    · have hyc2 := hsc2 y2 hs2'
      simp only [Except.map, match_ok, match_ok']
      obtain ⟨c, v⟩ := sel_neg hsgn hu hyc2
      refine ⟨hx2c, c, ?_⟩
      show (x2.toSpec, _) = (x2.toSpec, _)
      rw [v]
  · have hyc := hsc y hs
    simp only [Except.map, match_ok, match_ok']
    obtain ⟨c, v⟩ := sel_neg hsgn hu hyc
    refine ⟨hx1c, c, ?_⟩
    show (x1.toSpec, _) = (x1.toSpec, _)
    rw [v]


end EthLibImpl.Cryptography.Bls.HashToCurve

namespace EthLibImpl.Cryptography.Bls.HashConst

open private sgn0Fp2 Aprime Bprime from EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls (BlsError)

set_option maxRecDepth 100000 in
/-- The mirror's SSWU is the parametrised one. -/
theorem mirror_swu_eq_G : Mirror.HashToCurve.simpleSwuWith =
    HashToCurve.swuG' Mirror.HashToCurve.x1Exceptional Mirror.HashToCurve.negBOverA Aprime Bprime
      EthLib.Cryptography.Bls.Fp2.sqrtAlt sgn0Fp2 := rfl

end EthLibImpl.Cryptography.Bls.HashConst

namespace EthLibImpl.Cryptography.Bls.HashToCurve

open scoped EthLib.Cryptography.Bls.Fp2
open EthLib.Cryptography.Bls (BlsError)

theorem default_spec : (default : Fp2 × Fp2).1.Canonical ∧ (default : Fp2 × Fp2).2.Canonical ∧
    (((default : Fp2 × Fp2).1.toSpec, (default : Fp2 × Fp2).2.toSpec) =
      (default : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)) := by
  have d1 : (default : Fp2) = Fp2.zero := rfl
  have d2 : (default : EthLib.Cryptography.Bls.Fp2) = EthLib.Cryptography.Bls.Fp2.zero := rfl
  show Fp2.Canonical (default : Fp2) ∧ Fp2.Canonical (default : Fp2) ∧ _
  rw [d1]
  refine ⟨Fp2.zero_canonical, Fp2.zero_canonical, ?_⟩
  show (Fp2.toSpec Fp2.zero, Fp2.toSpec Fp2.zero) =
    (default : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)
  rw [Fp2.toSpec_zero]
  show _ = ((default : EthLib.Cryptography.Bls.Fp2), (default : EthLib.Cryptography.Bls.Fp2))
  rw [d2]

/-- `simpleSwuWith` computes the mirror's. -/
theorem simpleSwuWith_spec {u zu2 denom di : Fp2} (hu : u.Canonical) (hz : zu2.Canonical)
    (hd : denom.Canonical) (hi : di.Canonical) :
    PRel (simpleSwuWith u zu2 denom di)
      (Mirror.HashToCurve.simpleSwuWith u.toSpec zu2.toSpec denom.toSpec di.toSpec) := by
  rw [simpleSwuWith_eq_G, HashConst.mirror_swu_eq_G]
  obtain ⟨hx, vx⟩ := x1Exceptional_spec
  obtain ⟨hn, vn⟩ := negBOverA_spec
  obtain ⟨hA, vA⟩ := HashConst.Aprime_spec
  obtain ⟨hB, vB⟩ := HashConst.Bprime_spec
  exact swuG_spec _ _ _ _ _ _ _ _ hx vx hn vn hA vA hB vB Fp2.sqrt
    EthLib.Cryptography.Bls.Fp2.sqrtAlt (fun a ha => Fp2.sqrt_spec ha) _ _
    (fun y hy => HashConst.sgn0Fp2_spec hy) default_spec hu hz hd hi


/-! ## The isogeny -/

theorem poly3_spec {a b c d x x2 x3 : Fp2} (ha : a.Canonical) (hb : b.Canonical)
    (hc : c.Canonical) (hd : d.Canonical) (hx : x.Canonical) (hx2 : x2.Canonical)
    (hx3 : x3.Canonical) :
    (a * x3 + b * x2 + c * x + d).Canonical ∧
      (a * x3 + b * x2 + c * x + d).toSpec =
        a.toSpec * x3.toSpec + b.toSpec * x2.toSpec + c.toSpec * x.toSpec + d.toSpec := by
  have h1 := Fp2.canonical_hMul ha hx3
  have h2 := Fp2.canonical_hMul hb hx2
  have h3 := Fp2.canonical_hMul hc hx
  have h12 := Fp2.canonical_hAdd h1 h2
  have h123 := Fp2.canonical_hAdd h12 h3
  refine ⟨Fp2.canonical_hAdd h123 hd, ?_⟩
  rw [Fp2.toSpec_hAdd h123 hd, Fp2.toSpec_hAdd h12 h3, Fp2.toSpec_hAdd h1 h2,
    Fp2.toSpec_hMul ha hx3, Fp2.toSpec_hMul hb hx2, Fp2.toSpec_hMul hc hx]

theorem isoParts_spec {xp : Fp2} (hx : xp.Canonical) :
    (isoParts xp).1.Canonical ∧ (isoParts xp).2.1.Canonical ∧ (isoParts xp).2.2.1.Canonical ∧
      (isoParts xp).2.2.2.Canonical ∧
      ((isoParts xp).1.toSpec, (isoParts xp).2.1.toSpec, (isoParts xp).2.2.1.toSpec,
        (isoParts xp).2.2.2.toSpec) = Mirror.HashToCurve.isoParts xp.toSpec := by
  obtain ⟨c10, v10⟩ := HashConst.k10_spec
  obtain ⟨c11, v11⟩ := HashConst.k11_spec
  obtain ⟨c12, v12⟩ := HashConst.k12_spec
  obtain ⟨c13, v13⟩ := HashConst.k13_spec
  obtain ⟨c20, v20⟩ := HashConst.k20_spec
  obtain ⟨c21, v21⟩ := HashConst.k21_spec
  obtain ⟨c30, v30⟩ := HashConst.k30_spec
  obtain ⟨c31, v31⟩ := HashConst.k31_spec
  obtain ⟨c32, v32⟩ := HashConst.k32_spec
  obtain ⟨c33, v33⟩ := HashConst.k33_spec
  obtain ⟨c40, v40⟩ := HashConst.k40_spec
  obtain ⟨c41, v41⟩ := HashConst.k41_spec
  obtain ⟨c42, v42⟩ := HashConst.k42_spec
  have hx2 := Fp2.sqr_canonical hx
  have vx2 := Fp2.toSpec_sqr hx
  have hx3 := Fp2.canonical_hMul hx2 hx
  have vx3 := Fp2.toSpec_hMul hx2 hx
  obtain ⟨cn, vn⟩ := poly3_spec c13 c12 c11 c10 hx hx2 hx3
  obtain ⟨cy, vy⟩ := poly3_spec c33 c32 c31 c30 hx hx2 hx3
  have hd1 := Fp2.canonical_hMul c21 hx
  have hd2 := Fp2.canonical_hAdd hx2 hd1
  have hd3 := Fp2.canonical_hAdd hd2 c20
  have hy1 := Fp2.canonical_hMul c42 hx2
  have hy2 := Fp2.canonical_hMul c41 hx
  have hy3 := Fp2.canonical_hAdd (Fp2.canonical_hAdd hx3 hy1) hy2
  have hy4 := Fp2.canonical_hAdd hy3 c40
  unfold isoParts Mirror.HashToCurve.isoParts
  dsimp only
  refine ⟨cn, hd3, cy, hy4, ?_⟩
  rw [vn, vy, Fp2.toSpec_hAdd hd2 c20, Fp2.toSpec_hAdd hx2 hd1, Fp2.toSpec_hMul c21 hx,
    Fp2.toSpec_hAdd hy3 c40, Fp2.toSpec_hAdd (Fp2.canonical_hAdd hx3 hy1) hy2,
    Fp2.toSpec_hAdd hx3 hy1, Fp2.toSpec_hMul c42 hx2, Fp2.toSpec_hMul c41 hx, vx3, vx2,
    v10, v11, v12, v13, v20, v21, v30, v31, v32, v33, v40, v41, v42]

/-- `isoMapJac` computes the mirror's. -/
theorem isoMapJac_spec {xp yp : Fp2} (hx : xp.Canonical) (hy : yp.Canonical) :
    (isoMapJac xp yp).Canonical ∧
      G2.toSpec (isoMapJac xp yp) = Mirror.HashToCurve.isoMapJac xp.toSpec yp.toSpec := by
  obtain ⟨i1, i2, i3, i4, iv⟩ := isoParts_spec hx
  unfold isoMapJac Mirror.HashToCurve.isoMapJac
  generalize isoParts xp = I at i1 i2 i3 i4 iv ⊢
  rw [← iv]
  obtain ⟨xNum, xDen, yNum, yDen⟩ := I
  dsimp only at i1 i2 i3 i4 ⊢
  have hc : (xDen.isZero || yDen.isZero) = (xDen.toSpec.isZero || yDen.toSpec.isZero) := by
    rw [G2.isZero_eq i2, G2.isZero_eq i4]
  by_cases hcond : (xDen.isZero || yDen.isZero) = true
  · have hcs : (xDen.toSpec.isZero || yDen.toSpec.isZero) = true := by rw [← hc]; exact hcond
    rw [if_pos hcond, if_pos hcs]
    have j1 := Fp2.inverse_canonical i2
    have j2 := Fp2.inverse_canonical i4
    have h3 := Fp2.canonical_hMul hy i3
    refine ⟨⟨Fp2.canonical_hMul i1 j1, Fp2.canonical_hMul h3 j2, Fp2.one_canonical⟩, ?_⟩
    show (⟨(xNum * xDen.inverse).toSpec, (yp * yNum * yDen.inverse).toSpec,
      Fp2.one.toSpec⟩ : EthLib.Cryptography.Bls.G2) = _
    rw [Fp2.toSpec_hMul i1 j1, Fp2.toSpec_hMul h3 j2, Fp2.toSpec_hMul hy i3,
      Fp2.toSpec_inverse i2, Fp2.toSpec_inverse i4, Fp2.toSpec_one]
  · have hcs : ¬ (xDen.toSpec.isZero || yDen.toSpec.isZero) = true := by rw [← hc]; exact hcond
    rw [if_neg hcond, if_neg hcs]
    have hz := Fp2.canonical_hMul i2 i4
    have hzy := Fp2.canonical_hMul hz i4
    have hx2 := Fp2.sqr_canonical i2
    have hq := Fp2.canonical_hMul hzy hx2
    have h3 := Fp2.canonical_hMul hy i3
    refine ⟨⟨Fp2.canonical_hMul i1 hzy, Fp2.canonical_hMul h3 hq, hz⟩, ?_⟩
    show (⟨(xNum * (xDen * yDen * yDen)).toSpec, (yp * yNum * (xDen * yDen * yDen * xDen.sqr)).toSpec,
      (xDen * yDen).toSpec⟩ : EthLib.Cryptography.Bls.G2) = _
    rw [Fp2.toSpec_hMul i1 hzy, Fp2.toSpec_hMul h3 hq, Fp2.toSpec_hMul hy i3,
      Fp2.toSpec_hMul hzy hx2, Fp2.toSpec_hMul hz i4, Fp2.toSpec_hMul i2 i4, Fp2.toSpec_sqr i2]


/-! ## Cofactor clearing -/

/-- `psiJac` computes the mirror's. -/
theorem psiJac_spec {P : G2} (hP : G2.Canonical P) :
    (psiJac P).Canonical ∧
      G2.toSpec (psiJac P) = Mirror.HashToCurve.psiJac (G2.toSpec P) := by
  obtain ⟨hx, hy, hz⟩ := hP
  obtain ⟨c1, v1⟩ := HashConst.c1Psi_spec
  obtain ⟨c2, v2⟩ := HashConst.c2Psi_spec
  have hcx := Fp2.conj_canonical hx
  have hcy := Fp2.conj_canonical hy
  refine ⟨⟨Fp2.canonical_hMul c1 hcx, Fp2.canonical_hMul c2 hcy, Fp2.conj_canonical hz⟩, ?_⟩
  show (⟨(c1Psi * P.x.conj).toSpec, (c2Psi * P.y.conj).toSpec, P.z.conj.toSpec⟩ :
    EthLib.Cryptography.Bls.G2) = _
  rw [Fp2.toSpec_hMul c1 hcx, Fp2.toSpec_hMul c2 hcy, Fp2.toSpec_conj hx, Fp2.toSpec_conj hy,
    Fp2.toSpec_conj hz, v1, v2]
  rfl

/-- `psi2Jac` computes the mirror's. -/
theorem psi2Jac_spec {P : G2} (hP : G2.Canonical P) :
    (psi2Jac P).Canonical ∧
      G2.toSpec (psi2Jac P) = Mirror.HashToCurve.psi2Jac (G2.toSpec P) := by
  obtain ⟨hx, hy, hz⟩ := hP
  obtain ⟨c1, v1⟩ := HashConst.c1Psi2_spec
  have e : psi2Jac P = ⟨c1Psi2 * P.x, -P.y, P.z⟩ := rfl
  rw [e]
  refine ⟨G2.canonical_mk.mpr ⟨Fp2.canonical_hMul c1 hx, Fp2.canonical_hNeg hy, hz⟩, ?_⟩
  rw [G2.toSpec_mk, Fp2.toSpec_hMul c1 hx, Fp2.toSpec_hNeg hy, v1]
  simp only [Mirror.HashToCurve.psi2Jac, G2.toSpec_x, G2.toSpec_y, G2.toSpec_z]

theorem add_neg_spec {p q : G2} (hp : G2.Canonical p) (hq : G2.Canonical q) :
    (G2.add p (G2.neg q)).Canonical ∧
      G2.toSpec (G2.add p (G2.neg q)) =
        EthLib.Cryptography.Bls.G2.add (G2.toSpec p) (EthLib.Cryptography.Bls.G2.neg (G2.toSpec q)) := by
  obtain ⟨c1, v1⟩ := G2.neg_spec hq
  obtain ⟨c2, v2⟩ := G2.add_spec hp c1
  exact ⟨c2, by rw [v2, v1]⟩

/-- `clearCofactorJac` computes the mirror's. -/
theorem clearCofactorJac_spec {P : G2} (hP : G2.Canonical P) :
    (clearCofactorJac P).Canonical ∧
      G2.toSpec (clearCofactorJac P) = Mirror.HashToCurve.clearCofactorJac (G2.toSpec P) := by
  obtain ⟨ct1, vt1⟩ := HashConst.mulNegX_spec hP
  obtain ⟨cP2, vP2⟩ := G2.double_spec hP
  unfold clearCofactorJac Mirror.HashToCurve.clearCofactorJac
  dsimp only
  rw [← vt1, ← vP2]
  obtain ⟨cA, vA⟩ := psi2Jac_spec cP2
  obtain ⟨cB, vB⟩ := psiJac_spec hP
  obtain ⟨cC, vC⟩ := add_neg_spec cA cB
  obtain ⟨cD, vD⟩ := G2.add_spec ct1 cB
  obtain ⟨cE, vE⟩ := HashConst.mulNegX_spec cD
  obtain ⟨cF, vF⟩ := G2.add_spec cC cE
  obtain ⟨cG, vG⟩ := add_neg_spec cF ct1
  obtain ⟨cH, vH⟩ := add_neg_spec cG hP
  refine ⟨cH, ?_⟩
  rw [vH, vG, vF, vE, vD, vC, vA, vB]


/-! ## The whole pipeline -/

theorem hashToFieldFp2_spec (msg dst : ByteArray) (count : Nat) :
    (hashToFieldFp2 msg dst count).map (Array.map Fp2.toSpec) =
      EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2 msg dst count ∧
    ∀ us, hashToFieldFp2 msg dst count = .ok us →
      us.size = count ∧ ∀ x ∈ us, x.Canonical :=
  HashConst.hashToFieldFp2_spec_aux msg dst count

theorem map_getElem!' (bs : Array Fp2) {i : Nat} (h : i < bs.size) :
    (bs.map Fp2.toSpec)[i]! = bs[i]!.toSpec := by
  rw [getElem!_pos (c := bs.map Fp2.toSpec) i (by simpa using h), getElem!_pos (c := bs) i h,
    Array.getElem_map]


/-- `hashToG2` with SSWU as a parameter, using the implementation's own matchers. -/
def hashToG2G (sw : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2) (msg dst : ByteArray) :
    Except BlsError G2 :=
  bind (hashToFieldFp2 msg dst 2) fun us =>
    have u0 : Fp2 := us[0]!
    have u1 : Fp2 := us[1]!
    simpleSwu.match_1 (fun _ => Except BlsError G2) (swuDenom u0) fun zu0 den0 =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (swuDenom u1) fun zu1 den1 =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (den0.batchInverse2 den1) fun di0 di1 =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (sw u0 zu0 den0 di0) fun x0 y0 =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (sw u1 zu1 den1 di1) fun x1 y1 =>
    pure (clearCofactorJac (G2.add (isoMapJac x0 y0) (isoMapJac x1 y1)))

theorem hashToG2_eq_G : hashToG2 = hashToG2G simpleSwuWith := rfl


open EthLib.Cryptography.Bls.HashToCurve in
/-- The mirror's `hashToG2` with SSWU as a parameter, using the mirror's own matchers. -/
def mirrorHashToG2G
    (sw : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 →
      EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)
    (msg dst : ByteArray) : Except BlsError EthLib.Cryptography.Bls.G2 :=
  bind (EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2 msg dst 2) fun us =>
    have u0 : EthLib.Cryptography.Bls.Fp2 := us[0]!
    have u1 : EthLib.Cryptography.Bls.Fp2 := us[1]!
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.swuDenom u0)
      fun zu0 den0 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.swuDenom u1)
      fun zu1 den1 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2)
      (Mirror.HashToCurve.batchInverse2 den0 den1) fun di0 di1 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (sw u0 zu0 den0 di0) fun x0 y0 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (sw u1 zu1 den1 di1) fun x1 y1 =>
    pure (Mirror.HashToCurve.clearCofactorJac
      (EthLib.Cryptography.Bls.G2.add (Mirror.HashToCurve.isoMapJac x0 y0)
        (Mirror.HashToCurve.isoMapJac x1 y1)))

theorem mirror_hashToG2_eq_G :
    Mirror.HashToCurve.hashToG2 = mirrorHashToG2G Mirror.HashToCurve.simpleSwuWith := rfl


theorem hashToG2G_spec
    (sw : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2)
    (sw' : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 →
      EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 →
      EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)
    (hsw : ∀ {u zu den di : Fp2}, u.Canonical → zu.Canonical → den.Canonical → di.Canonical →
      PRel (sw u zu den di) (sw' u.toSpec zu.toSpec den.toSpec di.toSpec))
    (msg dst : ByteArray) :
    (hashToG2G sw msg dst).map G2.toSpec = mirrorHashToG2G sw' msg dst ∧
      ∀ q, hashToG2G sw msg dst = .ok q → G2.Canonical q := by
  unfold hashToG2G mirrorHashToG2G
  obtain ⟨hm, hc⟩ := hashToFieldFp2_spec msg dst 2
  rcases hu : hashToFieldFp2 msg dst 2 with e | us
  · rw [hu] at hm
    rw [← hm]
    refine ⟨?_, fun q hq => ?_⟩
    · simp only [bind, Except.bind, Except.map]
    · simp only [bind, Except.bind] at hq; cases hq
  · rw [hu] at hm
    rw [← hm]
    simp only [bind, Except.bind, Except.map]
    obtain ⟨hsz, hcan⟩ := hc us hu
    have h0 : 0 < us.size := by omega
    have h1 : 1 < us.size := by omega
    have e0 := map_getElem!' us h0
    have e1 := map_getElem!' us h1
    have hu0 : us[0]!.Canonical := by
      rw [getElem!_pos us 0 h0]; exact hcan _ (Array.getElem_mem h0)
    have hu1 : us[1]!.Canonical := by
      rw [getElem!_pos us 1 h1]; exact hcan _ (Array.getElem_mem h1)
    rw [e0, e1]
    generalize us[0]! = u0 at hu0 ⊢
    generalize us[1]! = u1 at hu1 ⊢
    obtain ⟨a1, a2, av⟩ := swuDenom_spec hu0
    obtain ⟨a1', a2', av'⟩ := swuDenom_spec hu1
    generalize swuDenom u0 = A0 at a1 a2 av ⊢
    generalize swuDenom u1 = A1 at a1' a2' av' ⊢
    rw [← av, ← av']
    obtain ⟨b1, b2, bv⟩ := Fp2.batchInverse2_spec a2 a2'
    generalize A0.2.batchInverse2 A1.2 = B at b1 b2 bv ⊢
    dsimp only
    rw [← bv]
    dsimp only
    obtain ⟨w1, w2, wv⟩ := hsw hu0 a1 a2 b1
    obtain ⟨w1', w2', wv'⟩ := hsw hu1 a1' a2' b2
    generalize sw u0 A0.1 A0.2 B.1 = W0 at w1 w2 wv ⊢
    generalize sw u1 A1.1 A1.2 B.2 = W1 at w1' w2' wv' ⊢
    rw [← wv, ← wv']
    dsimp only
    obtain ⟨m1, mv⟩ := isoMapJac_spec w1 w2
    obtain ⟨n1, nv⟩ := isoMapJac_spec w1' w2'
    obtain ⟨s1, sv⟩ := G2.add_spec m1 n1
    obtain ⟨t1, tv⟩ := clearCofactorJac_spec s1
    refine ⟨?_, fun q hq => ?_⟩
    · show Except.ok (G2.toSpec _) = Except.ok _
      rw [tv, sv, mv, nv]
    · have hq' := Except.ok.inj hq
      rw [← hq']
      exact t1


/-- The implementation's `hashToG2` computes the mirror's, and its output is a canonical
point. -/
theorem hashToG2_spec (msg dst : ByteArray) :
    (hashToG2 msg dst).map G2.toSpec = Mirror.HashToCurve.hashToG2 msg dst ∧
      ∀ q, hashToG2 msg dst = .ok q → G2.Canonical q := by
  have h := hashToG2G_spec simpleSwuWith Mirror.HashToCurve.simpleSwuWith
    (fun {u zu den di} hu hz hd hi =>
      simpleSwuWith_spec (u := u) (zu2 := zu) (denom := den) (di := di) hu hz hd hi) msg dst
  rw [hashToG2_eq_G, mirror_hashToG2_eq_G]
  exact h

/-- Main result: the implementation's `hashToG2` and the spec's `HashToCurve.hashToG2` fail
with the same error, or both succeed with triples for the same point: the implementation's
result is canonical, and the spec's triple is `G2.ProjEq` to its spec image (they differ by a
Jacobian scaling). -/
theorem hashToG2_rel_spec (msg dst : ByteArray) :
    (∃ e, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst = .error e ∧
        hashToG2 msg dst = .error e) ∨
      ∃ P q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst = .ok P ∧
        hashToG2 msg dst = .ok q ∧ G2.Canonical q ∧
        EthLib.Cryptography.Bls.G2.ProjEq P (G2.toSpec q) := by
  obtain ⟨hm, hc⟩ := hashToG2_spec msg dst
  rcases Mirror.HashToCurve.hashToG2_rel msg dst with ⟨e, hs, hmir⟩ | ⟨P, Q, hs, hmir, hp⟩
  · refine Or.inl ⟨e, hs, ?_⟩
    rw [hmir] at hm
    cases h : hashToG2 msg dst with
    | error e' => rw [h] at hm; exact congrArg Except.error (Except.error.inj hm)
    | ok q => rw [h] at hm; cases hm
  · right
    rw [hmir] at hm
    cases h : hashToG2 msg dst with
    | error e' => rw [h] at hm; cases hm
    | ok q =>
      rw [h] at hm
      have hq : G2.toSpec q = Q := Except.ok.inj hm
      exact ⟨P, q, hs, rfl, hc q h, hq ▸ hp⟩

end EthLibImpl.Cryptography.Bls.HashToCurve
