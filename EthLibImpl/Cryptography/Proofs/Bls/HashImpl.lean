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

namespace EthLibImpl.Cryptography.Bls.Fp2

open EthLib.Cryptography.Bls (BlsError)

/-- `sqrtGivenNorm` with `1/2` and the exponent's digits as parameters (the kernel would
otherwise evaluate these concrete constants while checking zeta-reductions). -/
def sqrtGN (half : Fp) (dg : ByteArray) (a : Fp2) (s : Fp) : Fp2 :=
  let t := (a.c0 + s) * half
  let d := Fp.powNibbles t dg
  let dt := d * t
  let hd := a.c1 * d * half
  if (d * dt).beq Fp.one then mk dt hd else mk (-hd) dt

theorem sqrtGivenNorm_eq_GN : sqrtGivenNorm = sqrtGN halfFp invSqrtDigits := rfl

theorem sqrtOk_eq_ok (half : Fp) (dg : ByteArray) (a : Fp2) (s : Fp) :
    sqrtOk half dg a s = .ok (sqrtGN half dg a s) := by
  unfold sqrtOk sqrtGN
  dsimp only
  split <;> rfl

/-- The spec-level counterpart of `sqrtGN`. -/
def sqrtGN' (half : EthLib.Cryptography.Bls.Fp) (e : Nat) (a : EthLib.Cryptography.Bls.Fp2) (s : EthLib.Cryptography.Bls.Fp) : EthLib.Cryptography.Bls.Fp2 :=
  let t := (a.c0 + s) * half
  let d := EthLib.Cryptography.Bls.Fp.powNat t e
  let dt := d * t
  let hd := a.c1 * d * half
  if (d * dt).beq EthLib.Cryptography.Bls.Fp.one then ⟨dt, hd⟩ else ⟨-hd, dt⟩

theorem sqrtAltOk_eq_ok (half : EthLib.Cryptography.Bls.Fp) (e : Nat) (a : EthLib.Cryptography.Bls.Fp2) (s : EthLib.Cryptography.Bls.Fp) :
    sqrtAltOk half e a s = .ok (sqrtGN' half e a s) := by
  unfold sqrtAltOk sqrtGN'
  dsimp only
  split <;> rfl

theorem mirror_sqrtGivenNorm_eq : Mirror.HashToCurve.sqrtGivenNorm =
    sqrtGN' (EthLib.Cryptography.Bls.Fp.ofNat 2).inverse ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) := rfl

/-- `sqrtGivenNorm` computes the mirror's. -/
theorem sqrtGivenNorm_spec {a : Fp2} {s : Fp} (ha : Canonical a) (hs : s.Canonical) :
    (sqrtGivenNorm a s).Canonical ∧
      (sqrtGivenNorm a s).toSpec = Mirror.HashToCurve.sqrtGivenNorm a.toSpec s.val := by
  rw [sqrtGivenNorm_eq_GN, mirror_sqrtGivenNorm_eq]
  obtain ⟨h1, h2⟩ := sqrtOk_spec halfFp (EthLib.Cryptography.Bls.Fp.ofNat 2).inverse halfFp_canonical halfFp_val
    ((EthLib.Cryptography.Bls.Fp.modulus - 3) / 4) ha hs
  rw [sqrtOk_eq_ok, sqrtAltOk_eq_ok] at h1
  exact ⟨h2 _ (sqrtOk_eq_ok _ _ _ _), Except.ok.inj h1⟩

end EthLibImpl.Cryptography.Bls.Fp2

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



/-- The implementation's slow path (`simpleSwuSlow`) with the constants, the square root and
`sgn0` as parameters. -/
def swuSlowG (A B : Fp2) (sq : Fp2 → Except BlsError Fp2) (sgn : Fp2 → Bool)
    (u zu2 x1 gx1 : Fp2) : Fp2 × Fp2 :=
  simpleSwuSlow.match_1 (fun _ => Fp2 × Fp2) (sq gx1)
    (fun y =>
      let y := if sgn u = sgn y then y else -y
      (x1, y))
    (fun _ =>
      let x2 := zu2 * x1
      let gx2 := x2.sqr * x2 + A * x2 + B
      simpleSwuSlow.match_1 (fun _ => Fp2 × Fp2) (sq gx2)
        (fun y =>
          let y := if sgn u = sgn y then y else -y
          (x2, y))
        (fun _ =>
          swuPanic))

theorem simpleSwuSlow_eq_G : simpleSwuSlow =
    swuSlowG Aprime Bprime Fp2.sqrt sgn0Fp2 := rfl

/-- The implementation's SSWU with its constants, the square root, `sgn0`, the norm's
square-root candidate `cn` and the root from a norm root `gn` as parameters. -/
def swuG (x1e nBA A B : Fp2) (s : Fp) (slow : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2) (sgn : Fp2 → Bool)
    (cn : Fp → Fp) (gn : Fp2 → Fp → Fp2)
    (u zu2 denom denomInv : Fp2) : Fp2 × Fp2 :=
  let x1 := if denom.isZero then x1e else nBA * (Fp2.one + denomInv)
  let gx1 := x1.sqr * x1 + A * x1 + B
  if gx1.c1.isZero || denom.isZero then
    slow u zu2 x1 gx1
  else
    let n1 := gx1.c0 * gx1.c0 + gx1.c1 * gx1.c1
    let c := cn n1
    if (c * c).beq n1 then
      let y := gn gx1 c
      let y := if sgn u = sgn y then y else -y
      (x1, y)
    else
      let x2 := zu2 * x1
      let gx2 := x2.sqr * x2 + A * x2 + B
      if gx2.c1.isZero then
        slow u zu2 x1 gx1
      else
        let nu := u.c0 * u.c0 + u.c1 * u.c1
        let y := gn gx2 (s * (nu * nu * nu) * c)
        let y := if sgn u = sgn y then y else -y
        (x2, y)

theorem simpleSwuWith_eq_G : simpleSwuWith =
    swuG x1Exceptional negBOverA Aprime Bprime s125 simpleSwuSlow sgn0Fp2
      (fun n => Fp.powNibbles n Fp.sqrtDigits) Fp2.sqrtGivenNorm := rfl

theorem match_ok {motive : Except BlsError Fp2 → Sort 1} (y : Fp2)
    (h1 : (y : Fp2) → motive (.ok y)) (h2 : (a : BlsError) → motive (.error a)) :
    simpleSwuSlow.match_1 motive (.ok y) h1 h2 = h1 y := rfl

theorem match_error {motive : Except BlsError Fp2 → Sort 1} (e : BlsError)
    (h1 : (y : Fp2) → motive (.ok y)) (h2 : (a : BlsError) → motive (.error a)) :
    simpleSwuSlow.match_1 motive (.error e) h1 h2 = h2 e := rfl

/-- The mirror's slow path with the constants, the square root and `sgn0` as parameters. -/
def swuSlowG' (A B : EthLib.Cryptography.Bls.Fp2)
    (sq : EthLib.Cryptography.Bls.Fp2 → Except BlsError EthLib.Cryptography.Bls.Fp2) (sgn : EthLib.Cryptography.Bls.Fp2 → Bool)
    (u zu2 x1 gx1 : EthLib.Cryptography.Bls.Fp2) : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2 :=
  Mirror.HashToCurve.simpleSwuSlow.match_1 (fun _ => EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) (sq gx1)
    (fun y =>
      let y := if sgn u = sgn y then y else -y
      (x1, y))
    (fun _ =>
      let x2 := zu2 * x1
      let gx2 := x2 * x2 * x2 + A * x2 + B
      Mirror.HashToCurve.simpleSwuSlow.match_1 (fun _ => EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) (sq gx2)
        (fun y =>
          let y := if sgn u = sgn y then y else -y
          (x2, y))
        (fun _ =>
          Mirror.HashToCurve.swuPanic))

/-- The mirror's SSWU with the constants, the square root, `sgn0`, the candidate and the root
from a norm root as parameters. -/
def swuG' (x1e nBA A B : EthLib.Cryptography.Bls.Fp2) (s : EthLib.Cryptography.Bls.Fp)
    (slow : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2) (sgn : EthLib.Cryptography.Bls.Fp2 → Bool)
    (cn : EthLib.Cryptography.Bls.Fp → EthLib.Cryptography.Bls.Fp) (gn : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp → EthLib.Cryptography.Bls.Fp2)
    (u zu2 denom denomInv : EthLib.Cryptography.Bls.Fp2) : EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2 :=
  let x1 := if denom.isZero then x1e else nBA * (EthLib.Cryptography.Bls.Fp2.one + denomInv)
  let gx1 := x1 * x1 * x1 + A * x1 + B
  if gx1.c1.isZero || denom.isZero then
    slow u zu2 x1 gx1
  else
    let n1 := gx1.c0 * gx1.c0 + gx1.c1 * gx1.c1
    let c := cn n1
    if (c * c).beq n1 then
      let y := gn gx1 c
      let y := if sgn u = sgn y then y else -y
      (x1, y)
    else
      let x2 := zu2 * x1
      let gx2 := x2 * x2 * x2 + A * x2 + B
      if gx2.c1.isZero then
        slow u zu2 x1 gx1
      else
        let nu := u.c0 * u.c0 + u.c1 * u.c1
        let y := gn gx2 (s * (nu * nu * nu) * c)
        let y := if sgn u = sgn y then y else -y
        (x2, y)

theorem match_ok' {motive : Except BlsError EthLib.Cryptography.Bls.Fp2 → Sort 1}
    (y : EthLib.Cryptography.Bls.Fp2)
    (h1 : (y : EthLib.Cryptography.Bls.Fp2) → motive (.ok y))
    (h2 : (a : BlsError) → motive (.error a)) :
    Mirror.HashToCurve.simpleSwuSlow.match_1 motive (.ok y) h1 h2 = h1 y := rfl

theorem match_error' {motive : Except BlsError EthLib.Cryptography.Bls.Fp2 → Sort 1}
    (e : BlsError)
    (h1 : (y : EthLib.Cryptography.Bls.Fp2) → motive (.ok y))
    (h2 : (a : BlsError) → motive (.error a)) :
    Mirror.HashToCurve.simpleSwuSlow.match_1 motive (.error e) h1 h2 = h2 e := rfl

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

theorem gx_spec {x A B : Fp2} {A' B' : EthLib.Cryptography.Bls.Fp2} (hx : x.Canonical)
    (hA : A.Canonical) (hAv : A.toSpec = A') (hB : B.Canonical) (hBv : B.toSpec = B') :
    (x.sqr * x + A * x + B).Canonical ∧
      (x.sqr * x + A * x + B).toSpec = x.toSpec * x.toSpec * x.toSpec + A' * x.toSpec + B' := by
  have hs := Fp2.sqr_canonical hx
  have hm := Fp2.canonical_hMul hs hx
  have hA1 := Fp2.canonical_hMul hA hx
  refine ⟨Fp2.canonical_hAdd (Fp2.canonical_hAdd hm hA1) hB, ?_⟩
  rw [Fp2.toSpec_hAdd (Fp2.canonical_hAdd hm hA1) hB, Fp2.toSpec_hAdd hm hA1,
    Fp2.toSpec_hMul hs hx, Fp2.toSpec_sqr hx, Fp2.toSpec_hMul hA hx, hAv, hBv]

/-- The slow path computes the mirror's. -/
theorem swuSlowG_spec (A B : Fp2) (A' B' : EthLib.Cryptography.Bls.Fp2)
    (hA : A.Canonical) (hAv : A.toSpec = A') (hB : B.Canonical) (hBv : B.toSpec = B')
    (sq : Fp2 → Except BlsError Fp2)
    (sq' : EthLib.Cryptography.Bls.Fp2 → Except BlsError EthLib.Cryptography.Bls.Fp2)
    (hsq : ∀ a : Fp2, a.Canonical → (sq a).map Fp2.toSpec = sq' a.toSpec ∧
      ∀ c, sq a = .ok c → c.Canonical)
    (sgn : Fp2 → Bool) (sgn' : EthLib.Cryptography.Bls.Fp2 → Bool)
    (hsgn : ∀ y : Fp2, y.Canonical → sgn y = sgn' y.toSpec)
    (hpan : PRel swuPanic Mirror.HashToCurve.swuPanic)
    {u zu2 x1 gx1 : Fp2} (hu : u.Canonical) (hz : zu2.Canonical) (hx : x1.Canonical)
    (hg : gx1.Canonical) :
    PRel (swuSlowG A B sq sgn u zu2 x1 gx1)
      (swuSlowG' A' B' sq' sgn' u.toSpec zu2.toSpec x1.toSpec gx1.toSpec) := by
  unfold swuSlowG swuSlowG'
  dsimp only
  obtain ⟨hsm, hsc⟩ := hsq gx1 hg
  rw [← hsm]
  rcases hs : sq gx1 with e | y
  · simp only [Except.map, match_error, match_error']
    have hx2c : (zu2 * x1).Canonical := Fp2.canonical_hMul hz hx
    have hx2v : (zu2 * x1).toSpec = zu2.toSpec * x1.toSpec := Fp2.toSpec_hMul hz hx
    rw [← hx2v]
    generalize zu2 * x1 = x2 at hx2c hx2v ⊢
    obtain ⟨hgc2, hgv2⟩ := gx_spec hx2c hA hAv hB hBv
    rw [← hgv2]
    generalize x2.sqr * x2 + A * x2 + B = G2 at hgc2 ⊢
    obtain ⟨hsm2, hsc2⟩ := hsq G2 hgc2
    rw [← hsm2]
    rcases hs2' : sq G2 with e2 | y2
    · simp only [Except.map, match_error, match_error']
      exact hpan
    · have hyc2 := hsc2 y2 hs2'
      simp only [Except.map, match_ok, match_ok']
      obtain ⟨c, v⟩ := sel_neg hsgn hu hyc2
      refine ⟨hx2c, c, ?_⟩
      show (x2.toSpec, _) = (x2.toSpec, _)
      rw [v]
  · have hyc := hsc y hs
    simp only [Except.map, match_ok, match_ok']
    obtain ⟨c, v⟩ := sel_neg hsgn hu hyc
    refine ⟨hx, c, ?_⟩
    show (x1.toSpec, _) = (x1.toSpec, _)
    rw [v]

theorem t_spec {s nu c : Fp} (hnu : nu.Canonical) (hc : c.Canonical) :
    (s * (nu * nu * nu) * c).Canonical ∧
      (s * (nu * nu * nu) * c).val = s.val * (nu.val * nu.val * nu.val) * c.val := by
  have h1 : (nu * nu).Canonical := G1.mul_c hnu
  have h2 : (nu * nu * nu).Canonical := G1.mul_c hnu
  refine ⟨G1.mul_c hc, ?_⟩
  rw [G1.mul_v hc, G1.mul_v h2, G1.mul_v hnu, G1.mul_v hnu]

theorem norm_spec {a b : Fp} (ha : a.Canonical) (hb : b.Canonical) :
    (a * a + b * b).Canonical ∧ (a * a + b * b).val = a.val * a.val + b.val * b.val := by
  have hm0 : (a * a).Canonical := G1.mul_c ha
  have hm1 : (b * b).Canonical := G1.mul_c hb
  refine ⟨G1.add_c hm0 hm1, ?_⟩
  rw [G1.add_v hm0 hm1, G1.mul_v ha, G1.mul_v hb]

theorem swuG_spec (x1e nBA A B : Fp2) (s : Fp) (x1e' nBA' A' B' : EthLib.Cryptography.Bls.Fp2) (s' : EthLib.Cryptography.Bls.Fp)
    (hx : x1e.Canonical) (hxv : x1e.toSpec = x1e')
    (hn : nBA.Canonical) (hnv : nBA.toSpec = nBA')
    (hA : A.Canonical) (hAv : A.toSpec = A') (hB : B.Canonical) (hBv : B.toSpec = B')
    (hsv : s.val = s')
    (slow : Fp2 → Fp2 → Fp2 → Fp2 → Fp2 × Fp2)
    (slow' : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp2 × EthLib.Cryptography.Bls.Fp2)
    (hslow : ∀ {u zu2 x1 gx1 : Fp2}, u.Canonical → zu2.Canonical → x1.Canonical →
      gx1.Canonical → PRel (slow u zu2 x1 gx1)
        (slow' u.toSpec zu2.toSpec x1.toSpec gx1.toSpec))
    (sgn : Fp2 → Bool) (sgn' : EthLib.Cryptography.Bls.Fp2 → Bool)
    (hsgn : ∀ y : Fp2, y.Canonical → sgn y = sgn' y.toSpec)
    (cn : Fp → Fp) (cn' : EthLib.Cryptography.Bls.Fp → EthLib.Cryptography.Bls.Fp)
    (hcn : ∀ n : Fp, n.Canonical → (cn n).Canonical ∧ (cn n).val = cn' n.val)
    (gn : Fp2 → Fp → Fp2) (gn' : EthLib.Cryptography.Bls.Fp2 → EthLib.Cryptography.Bls.Fp → EthLib.Cryptography.Bls.Fp2)
    (hgn : ∀ (a : Fp2) (t : Fp), a.Canonical → t.Canonical →
      (gn a t).Canonical ∧ (gn a t).toSpec = gn' a.toSpec t.val)
    {u zu2 denom di : Fp2} (hu : u.Canonical) (hz : zu2.Canonical) (hd : denom.Canonical)
    (hi : di.Canonical) :
    PRel (swuG x1e nBA A B s slow sgn cn gn u zu2 denom di)
      (swuG' x1e' nBA' A' B' s' slow' sgn' cn' gn' u.toSpec zu2.toSpec denom.toSpec di.toSpec) := by
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
  generalize (if denom.isZero = true then x1e' else nBA' * (EthLib.Cryptography.Bls.Fp2.one + di.toSpec)) = x1'
    at hx1v ⊢
  subst hx1v
  obtain ⟨hgc, hgv⟩ := gx_spec hx1c hA hAv hB hBv
  rw [← hgv]
  generalize x1.sqr * x1 + A * x1 + B = G at hgc ⊢
  have hcz : G.toSpec.c1.isZero = G.c1.isZero := (Fp2.fp_isZero_eq hgc.2).symm
  rw [hcz]
  by_cases hb : (G.c1.isZero || denom.isZero) = true
  · rw [if_pos hb, if_pos hb]
    exact hslow hu hz hx1c hgc
  · rw [if_neg hb, if_neg hb]
    obtain ⟨hn1c, hn1v⟩ := norm_spec hgc.1 hgc.2
    rw [show G.toSpec.c0 = G.c0.val from rfl, show G.toSpec.c1 = G.c1.val from rfl, ← hn1v]
    obtain ⟨hcc, hcv⟩ := hcn _ hn1c
    rw [← hcv]
    generalize G.c0 * G.c0 + G.c1 * G.c1 = n1 at hn1c hcc ⊢
    generalize cn n1 = c at hcc ⊢
    have hbq : (c * c).beq n1 = EthLib.Cryptography.Bls.Fp.beq (c.val * c.val) n1.val := by
      have hcm : (c * c).Canonical := G1.mul_c hcc
      have hcmv : (c * c).val = c.val * c.val := G1.mul_v hcc
      rw [G1.beq_eq hcm hn1c, hcmv]
    rw [← hbq]
    by_cases hb2 : (c * c).beq n1 = true
    · rw [if_pos hb2, if_pos hb2]
      obtain ⟨hyc, hyv⟩ := hgn G c hgc hcc
      rw [← hyv]
      generalize gn G c = y at hyc ⊢
      obtain ⟨c', v⟩ := sel_neg hsgn hu hyc
      refine ⟨hx1c, c', ?_⟩
      show (x1.toSpec, _) = (x1.toSpec, _)
      rw [v]
    · rw [if_neg hb2, if_neg hb2]
      have hx2c : (zu2 * x1).Canonical := Fp2.canonical_hMul hz hx1c
      have hx2v : (zu2 * x1).toSpec = zu2.toSpec * x1.toSpec := Fp2.toSpec_hMul hz hx1c
      rw [← hx2v]
      generalize zu2 * x1 = x2 at hx2c hx2v ⊢
      obtain ⟨hgc2, hgv2⟩ := gx_spec hx2c hA hAv hB hBv
      rw [← hgv2]
      generalize x2.sqr * x2 + A * x2 + B = G2 at hgc2 ⊢
      have hcz2 : G2.toSpec.c1.isZero = G2.c1.isZero := (Fp2.fp_isZero_eq hgc2.2).symm
      rw [hcz2]
      by_cases hb3 : G2.c1.isZero = true
      · rw [if_pos hb3, if_pos hb3]
        exact hslow hu hz hx1c hgc
      · rw [if_neg hb3, if_neg hb3]
        obtain ⟨hnuc, hnuv⟩ := norm_spec hu.1 hu.2
        rw [show u.toSpec.c0 = u.c0.val from rfl, show u.toSpec.c1 = u.c1.val from rfl, ← hnuv]
        generalize u.c0 * u.c0 + u.c1 * u.c1 = nu at hnuc ⊢
        obtain ⟨hTc, hTv⟩ := t_spec hnuc hcc
        rw [← hsv, ← hTv]
        generalize s * (nu * nu * nu) * c = T at hTc ⊢
        obtain ⟨hyc, hyv⟩ := hgn G2 T hgc2 hTc
        rw [← hyv]
        generalize gn G2 T = y at hyc ⊢
        obtain ⟨c', v⟩ := sel_neg hsgn hu hyc
        refine ⟨hx2c, c', ?_⟩
        show (x2.toSpec, _) = (x2.toSpec, _)
        rw [v]

end EthLibImpl.Cryptography.Bls.HashToCurve

namespace EthLibImpl.Cryptography.Bls.HashConst

open private sgn0Fp2 Aprime Bprime from EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls (BlsError)

set_option maxRecDepth 100000 in
/-- The mirror's SSWU is the parametrised one. -/
theorem mirror_swu_eq_G : Mirror.HashToCurve.simpleSwuWith =
    HashToCurve.swuG' Mirror.HashToCurve.x1Exceptional Mirror.HashToCurve.negBOverA Aprime Bprime
      Mirror.HashToCurve.s125 Mirror.HashToCurve.simpleSwuSlow sgn0Fp2
      (fun n => EthLib.Cryptography.Bls.Fp.powNat n ((EthLib.Cryptography.Bls.Fp.modulus + 1) / 4))
      Mirror.HashToCurve.sqrtGivenNorm := rfl

theorem mirror_slow_eq_G : Mirror.HashToCurve.simpleSwuSlow =
    HashToCurve.swuSlowG' Aprime Bprime EthLib.Cryptography.Bls.Fp2.sqrtAlt sgn0Fp2 := rfl

theorem s125_spec : HashToCurve.s125.Canonical ∧ HashToCurve.s125.val = Mirror.HashToCurve.s125 :=
  ⟨Fp.ofNat_canonical _, Fp.val_ofNat _⟩

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

theorem swuPanic_spec : PRel swuPanic Mirror.HashToCurve.swuPanic := by
  have h1 : swuPanic = default := rfl
  have h2 : Mirror.HashToCurve.swuPanic = default := rfl
  rw [h1, h2]
  exact default_spec

/-- The slow path computes the mirror's, with `Fp2.sqrt` as the mirror's `sqrtAlt`. -/
theorem swuSlow_spec' {u zu2 x1 gx1 : Fp2} (hu : u.Canonical) (hz : zu2.Canonical)
    (hx : x1.Canonical) (hg : gx1.Canonical) :
    PRel (simpleSwuSlow u zu2 x1 gx1)
      (Mirror.HashToCurve.simpleSwuSlow u.toSpec zu2.toSpec x1.toSpec gx1.toSpec) := by
  rw [simpleSwuSlow_eq_G, HashConst.mirror_slow_eq_G]
  obtain ⟨hA, vA⟩ := HashConst.Aprime_spec
  obtain ⟨hB, vB⟩ := HashConst.Bprime_spec
  exact swuSlowG_spec _ _ _ _ hA vA hB vB Fp2.sqrt
    EthLib.Cryptography.Bls.Fp2.sqrtAlt (fun a ha => Fp2.sqrt_spec ha) _ _
    (fun y hy => HashConst.sgn0Fp2_spec hy) swuPanic_spec hu hz hx hg

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
  obtain ⟨_, vs⟩ := HashConst.s125_spec
  exact swuG_spec _ _ _ _ _ _ _ _ _ _ hx vx hn vn hA vA hB vB vs _ _ (fun hu hz hx hg => swuSlow_spec' hu hz hx hg)
    _ _ (fun y hy => HashConst.sgn0Fp2_spec hy) _ _
    (fun n hn => ⟨Fp.powNibbles_canonical hn _, Fp.val_powNibbles_powNat hn _⟩) _ _
    (fun a t ha ht => Fp2.sqrtGivenNorm_spec ha ht) hu hz hd hi


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

theorem isoMapWith_spec {yp xn yn xi yi : Fp2} (hy : yp.Canonical) (hxn : xn.Canonical)
    (hyn : yn.Canonical) (hxi : xi.Canonical) (hyi : yi.Canonical) :
    PRel (isoMapWith yp xn yn xi yi)
      (Mirror.HashToCurve.isoMapWith yp.toSpec xn.toSpec yn.toSpec xi.toSpec yi.toSpec) := by
  have h1 := Fp2.canonical_hMul hxn hxi
  have h2 := Fp2.canonical_hMul hy hyn
  have h3 := Fp2.canonical_hMul h2 hyi
  unfold isoMapWith Mirror.HashToCurve.isoMapWith
  refine ⟨h1, h3, ?_⟩
  show ((xn * xi).toSpec, (yp * yn * yi).toSpec) = _
  rw [Fp2.toSpec_hMul hxn hxi, Fp2.toSpec_hMul h2 hyi, Fp2.toSpec_hMul hy hyn]


/-! ## Cofactor clearing -/

theorem toAffineWith_spec {P : G2} {zi : Fp2} (hP : G2.Canonical P) (hz : zi.Canonical) :
    PRel (toAffineWith P zi)
      (Mirror.HashToCurve.toAffineWith (G2.toSpec P) zi.toSpec) := by
  obtain ⟨hx, hy, _⟩ := hP
  have h2 := Fp2.sqr_canonical hz
  have h3 := Fp2.canonical_hMul h2 hz
  unfold toAffineWith Mirror.HashToCurve.toAffineWith
  refine ⟨Fp2.canonical_hMul hx h2, Fp2.canonical_hMul hy h3, ?_⟩
  show ((P.x * zi.sqr).toSpec, (P.y * (zi.sqr * zi)).toSpec) = _
  rw [Fp2.toSpec_hMul hx h2, Fp2.toSpec_hMul hy h3, Fp2.toSpec_hMul h2 hz, Fp2.toSpec_sqr hz]
  rfl

theorem psiWith_spec {P : G2} {zi : Fp2} (hP : G2.Canonical P) (hz : zi.Canonical) :
    (psiWith P zi).Canonical ∧
      G2.toSpec (psiWith P zi) = Mirror.HashToCurve.psiWith (G2.toSpec P) zi.toSpec := by
  have hs : (G2.toSpec P).z.isZero = P.z.isZero := (G2.isZero_eq hP.2.2).symm
  obtain ⟨hAf1, hAf2, hAf3⟩ := toAffineWith_spec hP hz
  unfold psiWith Mirror.HashToCurve.psiWith
  rw [hs]
  by_cases h : P.z.isZero = true
  · rw [if_pos h, if_pos h]; exact ⟨hP, rfl⟩
  · rw [if_neg h, if_neg h]
    obtain ⟨c1, v1⟩ := HashConst.c1Psi_spec
    obtain ⟨c2, v2⟩ := HashConst.c2Psi_spec
    generalize toAffineWith P zi = pa at hAf1 hAf2 hAf3
    generalize Mirror.HashToCurve.toAffineWith (G2.toSpec P) zi.toSpec = pa' at hAf3
    subst hAf3
    obtain ⟨x, y⟩ := pa
    have hcx := Fp2.conj_canonical hAf1
    have hcy := Fp2.conj_canonical hAf2
    have hx' := Fp2.canonical_hMul c1 hcx
    have hy' := Fp2.canonical_hMul c2 hcy
    refine ⟨⟨hx', hy', Fp2.one_canonical⟩, ?_⟩
    show (⟨(c1Psi * x.conj).toSpec, (c2Psi * y.conj).toSpec, Fp2.one.toSpec⟩ : EthLib.Cryptography.Bls.G2) = _
    rw [Fp2.toSpec_hMul c1 hcx, Fp2.toSpec_hMul c2 hcy, Fp2.toSpec_conj hAf1, Fp2.toSpec_conj hAf2,
      Fp2.toSpec_one, v1, v2]

theorem psi2With_spec {P : G2} {zi : Fp2} (hP : G2.Canonical P) (hz : zi.Canonical) :
    (psi2With P zi).Canonical ∧
      G2.toSpec (psi2With P zi) = Mirror.HashToCurve.psi2With (G2.toSpec P) zi.toSpec := by
  have hs : (G2.toSpec P).z.isZero = P.z.isZero := (G2.isZero_eq hP.2.2).symm
  obtain ⟨hAf1, hAf2, hAf3⟩ := toAffineWith_spec hP hz
  unfold psi2With Mirror.HashToCurve.psi2With
  rw [hs]
  by_cases h : P.z.isZero = true
  · rw [if_pos h, if_pos h]; exact ⟨hP, rfl⟩
  · rw [if_neg h, if_neg h]
    obtain ⟨c1, v1⟩ := HashConst.c1Psi2_spec
    generalize toAffineWith P zi = pa at hAf1 hAf2 hAf3
    generalize Mirror.HashToCurve.toAffineWith (G2.toSpec P) zi.toSpec = pa' at hAf3
    subst hAf3
    obtain ⟨x, y⟩ := pa
    have hx' := Fp2.canonical_hMul c1 hAf1
    have hy' := Fp2.canonical_hNeg hAf2
    refine ⟨⟨hx', hy', Fp2.one_canonical⟩, ?_⟩
    show (⟨(c1Psi2 * x).toSpec, (-y).toSpec, Fp2.one.toSpec⟩ : EthLib.Cryptography.Bls.G2) = _
    rw [Fp2.toSpec_hMul c1 hAf1, Fp2.toSpec_hNeg hAf2, Fp2.toSpec_one, v1]


theorem add_neg_spec {p q : G2} (hp : G2.Canonical p) (hq : G2.Canonical q) :
    (G2.add p (G2.neg q)).Canonical ∧
      G2.toSpec (G2.add p (G2.neg q)) =
        EthLib.Cryptography.Bls.G2.add (G2.toSpec p) (EthLib.Cryptography.Bls.G2.neg (G2.toSpec q)) := by
  obtain ⟨c1, v1⟩ := G2.neg_spec hq
  obtain ⟨c2, v2⟩ := G2.add_spec hp c1
  exact ⟨c2, by rw [v2, v1]⟩

/-- `clearCofactor` computes the mirror's. -/
theorem clearCofactor_spec {P : G2} (hP : G2.Canonical P) :
    (clearCofactor P).Canonical ∧
      G2.toSpec (clearCofactor P) = Mirror.HashToCurve.clearCofactor (G2.toSpec P) := by
  obtain ⟨ct1, vt1⟩ := HashConst.mulNegX_spec hP
  obtain ⟨cP2, vP2⟩ := G2.double_spec hP
  obtain ⟨b1, b2, bv⟩ := Fp2.batchInverse2_spec hP.2.2 cP2.2.2
  unfold clearCofactor Mirror.HashToCurve.clearCofactor
  dsimp only
  rw [← vt1, ← vP2]
  have bv' : (_, _) = Mirror.HashToCurve.batchInverse2 (G2.toSpec P).z
      (G2.toSpec (G2.double P)).z := bv
  generalize Fp2.batchInverse2 P.z (G2.double P).z = br at b1 b2 bv' ⊢
  generalize Mirror.HashToCurve.batchInverse2 (G2.toSpec P).z (G2.toSpec (G2.double P)).z = br'
    at bv' ⊢
  subst bv'
  obtain ⟨zi, zi2⟩ := br
  dsimp only at b1 b2 ⊢
  obtain ⟨cA, vA⟩ := psi2With_spec cP2 b2
  obtain ⟨cB, vB⟩ := psiWith_spec hP b1
  obtain ⟨cC, vC⟩ := add_neg_spec cA cB
  obtain ⟨cD, vD⟩ := G2.add_spec ct1 cB
  obtain ⟨cE, vE⟩ := HashConst.mulNegX_spec cD
  obtain ⟨cF, vF⟩ := G2.add_spec cC cE
  obtain ⟨cG, vG⟩ := add_neg_spec cF ct1
  obtain ⟨cH, vH⟩ := add_neg_spec cG hP
  refine ⟨cH, ?_⟩
  rw [vH, vG, vF, vE, vD, vC, vA, vB, vt1, vP2]


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
    isoMapG2.match_1 (fun _ => Except BlsError G2) (isoParts x0) fun xn0 xd0 yn0 yd0 =>
    isoMapG2.match_1 (fun _ => Except BlsError G2) (isoParts x1) fun xn1 xd1 yn1 yd1 =>
    isoMapG2.match_1 (fun _ => Except BlsError G2) (xd0.batchInverse4 yd0 xd1 yd1)
      fun xi0 yi0 xi1 yi1 =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (isoMapWith y0 xn0 yn0 xi0 yi0) fun xa ya =>
    simpleSwu.match_1 (fun _ => Except BlsError G2) (isoMapWith y1 xn1 yn1 xi1 yi1) fun xb yb =>
    have p0 : G2 := { x := xa, y := ya, z := Fp2.one }
    have p1 : G2 := { x := xb, y := yb, z := Fp2.one }
    pure (clearCofactor (p0.add p1))

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
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.swuDenom u0)
      fun zu0 den0 =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.swuDenom u1)
      fun zu1 den1 =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2)
      (Mirror.HashToCurve.batchInverse2 den0 den1) fun di0 di1 =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (sw u0 zu0 den0 di0) fun x0 y0 =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (sw u1 zu1 den1 di1) fun x1 y1 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.isoParts x0)
      fun xn0 xd0 yn0 yd0 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2) (Mirror.HashToCurve.isoParts x1)
      fun xn1 xd1 yn1 yd1 =>
    Mirror.HashToCurve.hashToG2.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2)
      (Mirror.HashToCurve.batchInverse4 xd0 yd0 xd1 yd1) fun xi0 yi0 xi1 yi1 =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2)
      (Mirror.HashToCurve.isoMapWith y0 xn0 yn0 xi0 yi0) fun xa ya =>
    Mirror.HashToCurve.psiWith.match_1
      (fun _ => Except BlsError EthLib.Cryptography.Bls.G2)
      (Mirror.HashToCurve.isoMapWith y1 xn1 yn1 xi1 yi1) fun xb yb =>
    have p0 : EthLib.Cryptography.Bls.G2 := { x := xa, y := ya, z := EthLib.Cryptography.Bls.Fp2.one }
    have p1 : EthLib.Cryptography.Bls.G2 := { x := xb, y := yb, z := EthLib.Cryptography.Bls.Fp2.one }
    pure (Mirror.HashToCurve.clearCofactor (p0.add p1))

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
    obtain ⟨i1, i2, i3, i4, iv⟩ := isoParts_spec w1
    obtain ⟨j1, j2, j3, j4, jv⟩ := isoParts_spec w1'
    generalize isoParts W0.1 = I0 at i1 i2 i3 i4 iv ⊢
    generalize isoParts W1.1 = I1 at j1 j2 j3 j4 jv ⊢
    rw [← iv, ← jv]
    dsimp only
    obtain ⟨k1, k2, k3, k4, kv⟩ := Fp2.batchInverse4_spec i2 i4 j2 j4
    generalize I0.2.1.batchInverse4 I0.2.2.2 I1.2.1 I1.2.2.2 = C at k1 k2 k3 k4 kv ⊢
    rw [← kv]
    dsimp only
    obtain ⟨m1, m2, mv⟩ := isoMapWith_spec w2 i1 i3 k1 k2
    obtain ⟨n1, n2, nv⟩ := isoMapWith_spec w2' j1 j3 k3 k4
    generalize isoMapWith W0.2 I0.1 I0.2.2.1 C.1 C.2.1 = M0 at m1 m2 mv ⊢
    generalize isoMapWith W1.2 I1.1 I1.2.2.1 C.2.2.1 C.2.2.2 = M1 at n1 n2 nv ⊢
    rw [← mv, ← nv]
    dsimp only
    have p0 : G2.Canonical ⟨M0.1, M0.2, Fp2.one⟩ := ⟨m1, m2, Fp2.one_canonical⟩
    have p1 : G2.Canonical ⟨M1.1, M1.2, Fp2.one⟩ := ⟨n1, n2, Fp2.one_canonical⟩
    obtain ⟨s1, sv⟩ := G2.add_spec p0 p1
    obtain ⟨t1, tv⟩ := clearCofactor_spec s1
    refine ⟨?_, fun q hq => ?_⟩
    · show Except.ok (G2.toSpec _) = Except.ok _
      rw [tv, sv, G2.toSpec_mk, G2.toSpec_mk, Fp2.toSpec_one]
    · have hq' := Except.ok.inj hq
      rw [← hq']
      exact t1


/-- Main result: the implementation's `hashToG2` computes the mirror's, and its output is a
canonical point. -/
theorem hashToG2_spec (msg dst : ByteArray) :
    (hashToG2 msg dst).map G2.toSpec = Mirror.HashToCurve.hashToG2 msg dst ∧
      ∀ q, hashToG2 msg dst = .ok q → G2.Canonical q := by
  have h := hashToG2G_spec simpleSwuWith Mirror.HashToCurve.simpleSwuWith
    (fun {u zu den di} hu hz hd hi =>
      simpleSwuWith_spec (u := u) (zu2 := zu) (denom := den) (di := di) hu hz hd hi) msg dst
  rw [hashToG2_eq_G, mirror_hashToG2_eq_G]
  exact h

/-- The implementation's `hashToG2` computes the spec's `HashToCurve.hashToG2`. -/
theorem hashToG2_eq_spec (msg dst : ByteArray) :
    (hashToG2 msg dst).map G2.toSpec = EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst := by
  rw [(hashToG2_spec msg dst).1, Mirror.HashToCurve.hashToG2_eq]

end EthLibImpl.Cryptography.Bls.HashToCurve
