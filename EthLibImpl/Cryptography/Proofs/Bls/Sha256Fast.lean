import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import EthLibImpl.Cryptography.Bls.Sha256Fast
import EthLib.Cryptography.Bls.Sha256

/-!
# Proofs: `Sha256Fast.hash` computes the spec's `Sha256.hash`

`Sha256Fast` unrolls the compression function over eight `UInt32` registers; the spec
(`EthLib.Cryptography.Bls.Sha256`) keeps arrays and `for` loops. The main result is
`Sha256Fast.hash_eq`.
-/

open private compressBlock big32 smallSigma0 smallSigma1 bigSigma0 bigSigma1 ch maj K padded
  from EthLib.Cryptography.Bls.Sha256

namespace EthLibImpl.Cryptography.Proofs.Sha256Fast
open EthLibImpl.Cryptography.Bls

/-- The fast state as the spec's eight-element array. -/
def toArr (s : Sha256Fast.St) : Array UInt32 := #[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

theorem forIn_range'_yield {β : Type} (r : Std.Legacy.Range) (init : β) (f : Nat → β → β) :
    (forIn (m := Id) r init (fun j acc => ForInStep.yield (f j acc)))
      = (List.range' r.start r.size r.step).foldl (fun acc j => f j acc) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  induction (List.range' r.start r.size r.step) generalizing init with
  | nil => rfl
  | cons x l ih => rw [List.forIn_cons, List.foldl_cons]; exact ih _

theorem bget (b : ByteArray) (i : Nat) : b[i]! = b.get! i := by
  cases b with | mk d =>
  by_cases h : i < d.size
  · have h' : i < (ByteArray.mk d).size := h
    rw [getElem!_pos (ByteArray.mk d) i h']
    simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos d i h]
    rfl
  · have h' : ¬ i < (ByteArray.mk d).size := h
    rw [getElem!_neg (ByteArray.mk d) i h']
    simp [ByteArray.get!, getElem!_neg d i h]

theorem be32_fun : Sha256Fast.be32 = big32 := funext fun b => funext fun o => by
  unfold Sha256Fast.be32 big32
  simp only [bget]
  have h : ∀ x : UInt8, x.toUInt32 = UInt32.ofNat x.toNat := fun x => by simp
  rw [h, h, h, h]

theorem ss0_fun : Sha256Fast.ss0 = smallSigma0 := rfl
theorem ss1_fun : Sha256Fast.ss1 = smallSigma1 := rfl
theorem bs0_fun : Sha256Fast.bs0 = bigSigma0 := rfl
theorem bs1_fun : Sha256Fast.bs1 = bigSigma1 := rfl
theorem ch_fun : Sha256Fast.ch = ch := rfl
theorem maj_fun : Sha256Fast.maj = maj := rfl

abbrev R8 := MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32
  (MProd UInt32 (MProd UInt32 UInt32))))))

/-- The spec's message schedule, as a pair of folds. -/
def sched (m : Nat → UInt32) : Array UInt32 :=
  (List.range' 16 48).foldl
    (fun W t => W.set! t (W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!))
    ((List.range' 0 16).foldl (fun W t => W.set! t (m t)) (Array.replicate 64 0))

/-- One round of the spec's compression loop. -/
def rnd (W : Array UInt32) (r : R8) (t : Nat) : R8 :=
  let T1 := r.snd.snd.snd.snd.snd.snd.snd + bigSigma1 r.snd.snd.snd.snd.fst +
    ch r.snd.snd.snd.snd.fst r.snd.snd.snd.snd.snd.fst r.snd.snd.snd.snd.snd.snd.fst + K[t]! + W[t]!
  let T2 := bigSigma0 r.fst + maj r.fst r.snd.fst r.snd.snd.fst
  ⟨T1 + T2, r.fst, r.snd.fst, r.snd.snd.fst, r.snd.snd.snd.fst + T1, r.snd.snd.snd.snd.fst,
    r.snd.snd.snd.snd.snd.fst, r.snd.snd.snd.snd.snd.snd.fst⟩

/-- The spec's final feed-forward addition. -/
def fin (Hs : Array UInt32) (r : R8) : Array UInt32 :=
  #[Hs[0]! + r.fst, Hs[1]! + r.snd.fst, Hs[2]! + r.snd.snd.fst, Hs[3]! + r.snd.snd.snd.fst,
    Hs[4]! + r.snd.snd.snd.snd.fst, Hs[5]! + r.snd.snd.snd.snd.snd.fst,
    Hs[6]! + r.snd.snd.snd.snd.snd.snd.fst, Hs[7]! + r.snd.snd.snd.snd.snd.snd.snd]

def init8 (Hs : Array UInt32) : R8 :=
  ⟨Hs[0]!, Hs[1]!, Hs[2]!, Hs[3]!, Hs[4]!, Hs[5]!, Hs[6]!, Hs[7]!⟩

theorem compressBlock_eq (H : Array UInt32) (buf : ByteArray) (off : Nat) :
    compressBlock H buf off =
      fin H ((List.range' 0 64).foldl (rnd (sched (fun t => big32 buf (off + 4 * t)))) (init8 H)) := by
  have e1 : forIn (m := Id) [:16] (Array.replicate 64 (0:UInt32))
        (fun (t : Nat) (W : Array UInt32) => ForInStep.yield (W.set! t (big32 buf (off + 4 * t)))) =
      (List.range' 0 16).foldl (fun (W : Array UInt32) t => W.set! t (big32 buf (off + 4 * t)))
        (Array.replicate 64 0) :=
    forIn_range'_yield [:16] _ (fun t (W : Array UInt32) => W.set! t (big32 buf (off + 4 * t)))
  have e2 : forIn (m := Id) [16:64] ((List.range' 0 16).foldl
        (fun (W : Array UInt32) t => W.set! t (big32 buf (off + 4 * t))) (Array.replicate 64 (0:UInt32)))
        (fun (t : Nat) (W : Array UInt32) => ForInStep.yield
          (W.set! t (W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!))) =
      sched (fun t => big32 buf (off + 4 * t)) :=
    forIn_range'_yield [16:64] _ (fun t (W : Array UInt32) =>
      W.set! t (W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!))
  have e3 : ∀ W : Array UInt32, forIn (m := Id) [:64] (init8 H)
      (fun t r => ForInStep.yield (rnd W r t)) = (List.range' 0 64).foldl (rnd W) (init8 H) :=
    fun W => forIn_range'_yield [:64] _ (fun t r => rnd W r t)
  unfold compressBlock
  show fin H (forIn (m := Id) [:64] (init8 H) (fun t r => ForInStep.yield (rnd
      (forIn (m := Id) [16:64] (forIn (m := Id) [:16] (Array.replicate 64 (0:UInt32))
        (fun (t : Nat) (W : Array UInt32) => ForInStep.yield (W.set! t (big32 buf (off + 4 * t)))))
        (fun (t : Nat) (W : Array UInt32) => ForInStep.yield
          (W.set! t (W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!)))) r t))) = _
  rw [e1, e2, e3]

/-! ### The schedule -/

theorem get_set (W : Array UInt32) (i j : Nat) (v : UInt32) (h : j < W.size) :
    (W.set! i v)[j]! = if i = j then v else W[j]! := by
  have h1 : (W.set! i v)[j]? = if i = j then (if i < W.size then some v else none) else W[j]? := by
    simp [Array.getElem?_setIfInBounds]
  have h2 : (W.set! i v)[j]! = ((W.set! i v)[j]?).getD default := by
    rw [getElem!_def]; cases (W.set! i v)[j]? <;> rfl
  have h3 : W[j]! = (W[j]?).getD default := by
    rw [getElem!_def]; cases W[j]? <;> rfl
  rw [h2, h1, h3]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij]

theorem size_set (W : Array UInt32) (i : Nat) (v : UInt32) : (W.set! i v).size = W.size := by simp

theorem sched_base (m : Nat → UInt32) (n : Nat) (hn : n ≤ 16) :
    ((List.range' 0 n).foldl (fun (W : Array UInt32) t => W.set! t (m t)) (Array.replicate 64 0)).size = 64 ∧
    ∀ t, t < n → ((List.range' 0 n).foldl (fun (W : Array UInt32) t => W.set! t (m t))
      (Array.replicate 64 0))[t]! = m t := by
  induction n with
  | zero => exact ⟨by simp, fun t ht => by omega⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    refine ⟨by rw [size_set, ih1], fun t ht => ?_⟩
    rw [get_set _ _ _ _ (by rw [ih1]; omega)]
    by_cases h : n = t
    · simp [h]
    · rw [if_neg h]; exact ih2 t (by omega)

def schedInv (m : Nat → UInt32) (k : Nat) (W : Array UInt32) : Prop :=
  W.size = 64 ∧ (∀ t, t < 16 → W[t]! = m t) ∧
  ∀ t, 16 ≤ t → t < k → W[t]! = W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!

theorem schedInv_step (m : Nat → UInt32) (k : Nat) (W : Array UInt32) (hk : 16 ≤ k) (hk2 : k < 64)
    (h : schedInv m k W) :
    schedInv m (k+1) (W.set! k (W[k-16]! + smallSigma0 W[k-15]! + W[k-7]! + smallSigma1 W[k-2]!)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [size_set, h1], fun t ht => ?_, fun t ht1 ht2 => ?_⟩
  · rw [get_set _ _ _ _ (by rw [h1]; omega), if_neg (by omega)]; exact h2 t ht
  · rw [get_set _ _ _ _ (by rw [h1]; omega)]
    by_cases htk : k = t
    · subst htk
      rw [if_pos rfl, get_set _ _ _ _ (by rw [h1]; omega), get_set _ _ _ _ (by rw [h1]; omega),
        get_set _ _ _ _ (by rw [h1]; omega), get_set _ _ _ _ (by rw [h1]; omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg htk, get_set _ _ _ _ (by rw [h1]; omega), get_set _ _ _ _ (by rw [h1]; omega),
        get_set _ _ _ _ (by rw [h1]; omega), get_set _ _ _ _ (by rw [h1]; omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact h3 t ht1 (by omega)

theorem sched_loop (m : Nat → UInt32) (n : Nat) (hn : n ≤ 48) :
    schedInv m (16 + n) ((List.range' 16 n).foldl
      (fun W t => W.set! t (W[t-16]! + smallSigma0 W[t-15]! + W[t-7]! + smallSigma1 W[t-2]!))
      ((List.range' 0 16).foldl (fun W t => W.set! t (m t)) (Array.replicate 64 0))) := by
  induction n with
  | zero =>
    obtain ⟨b1, b2⟩ := sched_base m 16 le_rfl
    rw [List.range'_zero, List.foldl_nil]
    exact ⟨b1, b2, fun t ht1 ht2 => by omega⟩
  | succ n ih =>
    have hr : List.range' 16 (n+1) = List.range' 16 n ++ [16 + n] := by
      rw [List.range'_concat]; simp
    rw [hr, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact schedInv_step m (16 + n) _ (by omega) (by omega) (ih (by omega))

theorem sched_facts (m : Nat → UInt32) :
    (sched m).size = 64 ∧ (∀ t, t < 16 → (sched m)[t]! = m t) ∧
    ∀ t, 16 ≤ t → t < 64 → (sched m)[t]! =
      (sched m)[t-16]! + smallSigma0 (sched m)[t-15]! + (sched m)[t-7]! + smallSigma1 (sched m)[t-2]! :=
  sched_loop m 48 le_rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The fast compression function equals the spec's, as an eight-element array. -/
theorem compress_eq (H : Sha256Fast.St) (buf : ByteArray) (off : Nat) :
    toArr (Sha256Fast.compress H buf off) = compressBlock (toArr H) buf off := by
  rw [compressBlock_eq]
  obtain ⟨hsz, hb, hr⟩ := sched_facts (fun t => big32 buf (off + 4 * t))
  generalize sched (fun t => big32 buf (off + 4 * t)) = S at hsz hb hr
  unfold Sha256Fast.compress
  rw [be32_fun, ss0_fun, ss1_fun, bs0_fun, bs1_fun, ch_fun, maj_fun]
  extract_lets w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 w60 w61 w62 w63 a_0 b_0 c_0 d_0 e_0 f_0 g_0 h_0 t1_1 t2_1 h_1 g_1 f_1 e_1 d_1 c_1 b_1 a_1 t1_2 t2_2 h_2 g_2 f_2 e_2 d_2 c_2 b_2 a_2 t1_3 t2_3 h_3 g_3 f_3 e_3 d_3 c_3 b_3 a_3 t1_4 t2_4 h_4 g_4 f_4 e_4 d_4 c_4 b_4 a_4 t1_5 t2_5 h_5 g_5 f_5 e_5 d_5 c_5 b_5 a_5 t1_6 t2_6 h_6 g_6 f_6 e_6 d_6 c_6 b_6 a_6 t1_7 t2_7 h_7 g_7 f_7 e_7 d_7 c_7 b_7 a_7 t1_8 t2_8 h_8 g_8 f_8 e_8 d_8 c_8 b_8 a_8 t1_9 t2_9 h_9 g_9 f_9 e_9 d_9 c_9 b_9 a_9 t1_10 t2_10 h_10 g_10 f_10 e_10 d_10 c_10 b_10 a_10 t1_11 t2_11 h_11 g_11 f_11 e_11 d_11 c_11 b_11 a_11 t1_12 t2_12 h_12 g_12 f_12 e_12 d_12 c_12 b_12 a_12 t1_13 t2_13 h_13 g_13 f_13 e_13 d_13 c_13 b_13 a_13 t1_14 t2_14 h_14 g_14 f_14 e_14 d_14 c_14 b_14 a_14 t1_15 t2_15 h_15 g_15 f_15 e_15 d_15 c_15 b_15 a_15 t1_16 t2_16 h_16 g_16 f_16 e_16 d_16 c_16 b_16 a_16 t1_17 t2_17 h_17 g_17 f_17 e_17 d_17 c_17 b_17 a_17 t1_18 t2_18 h_18 g_18 f_18 e_18 d_18 c_18 b_18 a_18 t1_19 t2_19 h_19 g_19 f_19 e_19 d_19 c_19 b_19 a_19 t1_20 t2_20 h_20 g_20 f_20 e_20 d_20 c_20 b_20 a_20 t1_21 t2_21 h_21 g_21 f_21 e_21 d_21 c_21 b_21 a_21 t1_22 t2_22 h_22 g_22 f_22 e_22 d_22 c_22 b_22 a_22 t1_23 t2_23 h_23 g_23 f_23 e_23 d_23 c_23 b_23 a_23 t1_24 t2_24 h_24 g_24 f_24 e_24 d_24 c_24 b_24 a_24 t1_25 t2_25 h_25 g_25 f_25 e_25 d_25 c_25 b_25 a_25 t1_26 t2_26 h_26 g_26 f_26 e_26 d_26 c_26 b_26 a_26 t1_27 t2_27 h_27 g_27 f_27 e_27 d_27 c_27 b_27 a_27 t1_28 t2_28 h_28 g_28 f_28 e_28 d_28 c_28 b_28 a_28 t1_29 t2_29 h_29 g_29 f_29 e_29 d_29 c_29 b_29 a_29 t1_30 t2_30 h_30 g_30 f_30 e_30 d_30 c_30 b_30 a_30 t1_31 t2_31 h_31 g_31 f_31 e_31 d_31 c_31 b_31 a_31 t1_32 t2_32 h_32 g_32 f_32 e_32 d_32 c_32 b_32 a_32 t1_33 t2_33 h_33 g_33 f_33 e_33 d_33 c_33 b_33 a_33 t1_34 t2_34 h_34 g_34 f_34 e_34 d_34 c_34 b_34 a_34 t1_35 t2_35 h_35 g_35 f_35 e_35 d_35 c_35 b_35 a_35 t1_36 t2_36 h_36 g_36 f_36 e_36 d_36 c_36 b_36 a_36 t1_37 t2_37 h_37 g_37 f_37 e_37 d_37 c_37 b_37 a_37 t1_38 t2_38 h_38 g_38 f_38 e_38 d_38 c_38 b_38 a_38 t1_39 t2_39 h_39 g_39 f_39 e_39 d_39 c_39 b_39 a_39 t1_40 t2_40 h_40 g_40 f_40 e_40 d_40 c_40 b_40 a_40 t1_41 t2_41 h_41 g_41 f_41 e_41 d_41 c_41 b_41 a_41 t1_42 t2_42 h_42 g_42 f_42 e_42 d_42 c_42 b_42 a_42 t1_43 t2_43 h_43 g_43 f_43 e_43 d_43 c_43 b_43 a_43 t1_44 t2_44 h_44 g_44 f_44 e_44 d_44 c_44 b_44 a_44 t1_45 t2_45 h_45 g_45 f_45 e_45 d_45 c_45 b_45 a_45 t1_46 t2_46 h_46 g_46 f_46 e_46 d_46 c_46 b_46 a_46 t1_47 t2_47 h_47 g_47 f_47 e_47 d_47 c_47 b_47 a_47 t1_48 t2_48 h_48 g_48 f_48 e_48 d_48 c_48 b_48 a_48 t1_49 t2_49 h_49 g_49 f_49 e_49 d_49 c_49 b_49 a_49 t1_50 t2_50 h_50 g_50 f_50 e_50 d_50 c_50 b_50 a_50 t1_51 t2_51 h_51 g_51 f_51 e_51 d_51 c_51 b_51 a_51 t1_52 t2_52 h_52 g_52 f_52 e_52 d_52 c_52 b_52 a_52 t1_53 t2_53 h_53 g_53 f_53 e_53 d_53 c_53 b_53 a_53 t1_54 t2_54 h_54 g_54 f_54 e_54 d_54 c_54 b_54 a_54 t1_55 t2_55 h_55 g_55 f_55 e_55 d_55 c_55 b_55 a_55 t1_56 t2_56 h_56 g_56 f_56 e_56 d_56 c_56 b_56 a_56 t1_57 t2_57 h_57 g_57 f_57 e_57 d_57 c_57 b_57 a_57 t1_58 t2_58 h_58 g_58 f_58 e_58 d_58 c_58 b_58 a_58 t1_59 t2_59 h_59 g_59 f_59 e_59 d_59 c_59 b_59 a_59 t1_60 t2_60 h_60 g_60 f_60 e_60 d_60 c_60 b_60 a_60 t1_61 t2_61 h_61 g_61 f_61 e_61 d_61 c_61 b_61 a_61 t1_62 t2_62 h_62 g_62 f_62 e_62 d_62 c_62 b_62 a_62 t1_63 t2_63 h_63 g_63 f_63 e_63 d_63 c_63 b_63 a_63 t1_64 t2_64 h_64 g_64 f_64 e_64 d_64 c_64 b_64 a_64
  have hw0 : S[0]! = w0 := hb 0 (by norm_num)
  have hw1 : S[1]! = w1 := hb 1 (by norm_num)
  have hw2 : S[2]! = w2 := hb 2 (by norm_num)
  have hw3 : S[3]! = w3 := hb 3 (by norm_num)
  have hw4 : S[4]! = w4 := hb 4 (by norm_num)
  have hw5 : S[5]! = w5 := hb 5 (by norm_num)
  have hw6 : S[6]! = w6 := hb 6 (by norm_num)
  have hw7 : S[7]! = w7 := hb 7 (by norm_num)
  have hw8 : S[8]! = w8 := hb 8 (by norm_num)
  have hw9 : S[9]! = w9 := hb 9 (by norm_num)
  have hw10 : S[10]! = w10 := hb 10 (by norm_num)
  have hw11 : S[11]! = w11 := hb 11 (by norm_num)
  have hw12 : S[12]! = w12 := hb 12 (by norm_num)
  have hw13 : S[13]! = w13 := hb 13 (by norm_num)
  have hw14 : S[14]! = w14 := hb 14 (by norm_num)
  have hw15 : S[15]! = w15 := hb 15 (by norm_num)
  have hw16 : S[16]! = w16 := by
    have h := hr 16 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw0, hw1, hw9, hw14]
  have hw17 : S[17]! = w17 := by
    have h := hr 17 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw1, hw2, hw10, hw15]
  have hw18 : S[18]! = w18 := by
    have h := hr 18 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw2, hw3, hw11, hw16]
  have hw19 : S[19]! = w19 := by
    have h := hr 19 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw3, hw4, hw12, hw17]
  have hw20 : S[20]! = w20 := by
    have h := hr 20 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw4, hw5, hw13, hw18]
  have hw21 : S[21]! = w21 := by
    have h := hr 21 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw5, hw6, hw14, hw19]
  have hw22 : S[22]! = w22 := by
    have h := hr 22 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw6, hw7, hw15, hw20]
  have hw23 : S[23]! = w23 := by
    have h := hr 23 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw7, hw8, hw16, hw21]
  have hw24 : S[24]! = w24 := by
    have h := hr 24 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw8, hw9, hw17, hw22]
  have hw25 : S[25]! = w25 := by
    have h := hr 25 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw9, hw10, hw18, hw23]
  have hw26 : S[26]! = w26 := by
    have h := hr 26 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw10, hw11, hw19, hw24]
  have hw27 : S[27]! = w27 := by
    have h := hr 27 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw11, hw12, hw20, hw25]
  have hw28 : S[28]! = w28 := by
    have h := hr 28 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw12, hw13, hw21, hw26]
  have hw29 : S[29]! = w29 := by
    have h := hr 29 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw13, hw14, hw22, hw27]
  have hw30 : S[30]! = w30 := by
    have h := hr 30 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw14, hw15, hw23, hw28]
  have hw31 : S[31]! = w31 := by
    have h := hr 31 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw15, hw16, hw24, hw29]
  have hw32 : S[32]! = w32 := by
    have h := hr 32 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw16, hw17, hw25, hw30]
  have hw33 : S[33]! = w33 := by
    have h := hr 33 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw17, hw18, hw26, hw31]
  have hw34 : S[34]! = w34 := by
    have h := hr 34 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw18, hw19, hw27, hw32]
  have hw35 : S[35]! = w35 := by
    have h := hr 35 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw19, hw20, hw28, hw33]
  have hw36 : S[36]! = w36 := by
    have h := hr 36 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw20, hw21, hw29, hw34]
  have hw37 : S[37]! = w37 := by
    have h := hr 37 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw21, hw22, hw30, hw35]
  have hw38 : S[38]! = w38 := by
    have h := hr 38 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw22, hw23, hw31, hw36]
  have hw39 : S[39]! = w39 := by
    have h := hr 39 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw23, hw24, hw32, hw37]
  have hw40 : S[40]! = w40 := by
    have h := hr 40 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw24, hw25, hw33, hw38]
  have hw41 : S[41]! = w41 := by
    have h := hr 41 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw25, hw26, hw34, hw39]
  have hw42 : S[42]! = w42 := by
    have h := hr 42 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw26, hw27, hw35, hw40]
  have hw43 : S[43]! = w43 := by
    have h := hr 43 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw27, hw28, hw36, hw41]
  have hw44 : S[44]! = w44 := by
    have h := hr 44 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw28, hw29, hw37, hw42]
  have hw45 : S[45]! = w45 := by
    have h := hr 45 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw29, hw30, hw38, hw43]
  have hw46 : S[46]! = w46 := by
    have h := hr 46 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw30, hw31, hw39, hw44]
  have hw47 : S[47]! = w47 := by
    have h := hr 47 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw31, hw32, hw40, hw45]
  have hw48 : S[48]! = w48 := by
    have h := hr 48 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw32, hw33, hw41, hw46]
  have hw49 : S[49]! = w49 := by
    have h := hr 49 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw33, hw34, hw42, hw47]
  have hw50 : S[50]! = w50 := by
    have h := hr 50 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw34, hw35, hw43, hw48]
  have hw51 : S[51]! = w51 := by
    have h := hr 51 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw35, hw36, hw44, hw49]
  have hw52 : S[52]! = w52 := by
    have h := hr 52 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw36, hw37, hw45, hw50]
  have hw53 : S[53]! = w53 := by
    have h := hr 53 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw37, hw38, hw46, hw51]
  have hw54 : S[54]! = w54 := by
    have h := hr 54 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw38, hw39, hw47, hw52]
  have hw55 : S[55]! = w55 := by
    have h := hr 55 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw39, hw40, hw48, hw53]
  have hw56 : S[56]! = w56 := by
    have h := hr 56 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw40, hw41, hw49, hw54]
  have hw57 : S[57]! = w57 := by
    have h := hr 57 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw41, hw42, hw50, hw55]
  have hw58 : S[58]! = w58 := by
    have h := hr 58 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw42, hw43, hw51, hw56]
  have hw59 : S[59]! = w59 := by
    have h := hr 59 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw43, hw44, hw52, hw57]
  have hw60 : S[60]! = w60 := by
    have h := hr 60 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw44, hw45, hw53, hw58]
  have hw61 : S[61]! = w61 := by
    have h := hr 61 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw45, hw46, hw54, hw59]
  have hw62 : S[62]! = w62 := by
    have h := hr 62 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw46, hw47, hw55, hw60]
  have hw63 : S[63]! = w63 := by
    have h := hr 63 (by norm_num) (by norm_num)
    simp only [Nat.reduceSub] at h
    rw [h, hw47, hw48, hw56, hw61]
  rw [show List.range' 0 64 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  have q : init8 (toArr H) = (⟨a_0, b_0, c_0, d_0, e_0, f_0, g_0, h_0⟩ : R8) := rfl
  rw [q]
  have q0 : rnd S (⟨a_0, b_0, c_0, d_0, e_0, f_0, g_0, h_0⟩ : R8) 0 = (⟨a_1, b_1, c_1, d_1, e_1, f_1, g_1, h_1⟩ : R8) := by
    unfold rnd; rw [hw0]; rfl
  rw [q0]
  have q1 : rnd S (⟨a_1, b_1, c_1, d_1, e_1, f_1, g_1, h_1⟩ : R8) 1 = (⟨a_2, b_2, c_2, d_2, e_2, f_2, g_2, h_2⟩ : R8) := by
    unfold rnd; rw [hw1]; rfl
  rw [q1]
  have q2 : rnd S (⟨a_2, b_2, c_2, d_2, e_2, f_2, g_2, h_2⟩ : R8) 2 = (⟨a_3, b_3, c_3, d_3, e_3, f_3, g_3, h_3⟩ : R8) := by
    unfold rnd; rw [hw2]; rfl
  rw [q2]
  have q3 : rnd S (⟨a_3, b_3, c_3, d_3, e_3, f_3, g_3, h_3⟩ : R8) 3 = (⟨a_4, b_4, c_4, d_4, e_4, f_4, g_4, h_4⟩ : R8) := by
    unfold rnd; rw [hw3]; rfl
  rw [q3]
  have q4 : rnd S (⟨a_4, b_4, c_4, d_4, e_4, f_4, g_4, h_4⟩ : R8) 4 = (⟨a_5, b_5, c_5, d_5, e_5, f_5, g_5, h_5⟩ : R8) := by
    unfold rnd; rw [hw4]; rfl
  rw [q4]
  have q5 : rnd S (⟨a_5, b_5, c_5, d_5, e_5, f_5, g_5, h_5⟩ : R8) 5 = (⟨a_6, b_6, c_6, d_6, e_6, f_6, g_6, h_6⟩ : R8) := by
    unfold rnd; rw [hw5]; rfl
  rw [q5]
  have q6 : rnd S (⟨a_6, b_6, c_6, d_6, e_6, f_6, g_6, h_6⟩ : R8) 6 = (⟨a_7, b_7, c_7, d_7, e_7, f_7, g_7, h_7⟩ : R8) := by
    unfold rnd; rw [hw6]; rfl
  rw [q6]
  have q7 : rnd S (⟨a_7, b_7, c_7, d_7, e_7, f_7, g_7, h_7⟩ : R8) 7 = (⟨a_8, b_8, c_8, d_8, e_8, f_8, g_8, h_8⟩ : R8) := by
    unfold rnd; rw [hw7]; rfl
  rw [q7]
  have q8 : rnd S (⟨a_8, b_8, c_8, d_8, e_8, f_8, g_8, h_8⟩ : R8) 8 = (⟨a_9, b_9, c_9, d_9, e_9, f_9, g_9, h_9⟩ : R8) := by
    unfold rnd; rw [hw8]; rfl
  rw [q8]
  have q9 : rnd S (⟨a_9, b_9, c_9, d_9, e_9, f_9, g_9, h_9⟩ : R8) 9 = (⟨a_10, b_10, c_10, d_10, e_10, f_10, g_10, h_10⟩ : R8) := by
    unfold rnd; rw [hw9]; rfl
  rw [q9]
  have q10 : rnd S (⟨a_10, b_10, c_10, d_10, e_10, f_10, g_10, h_10⟩ : R8) 10 = (⟨a_11, b_11, c_11, d_11, e_11, f_11, g_11, h_11⟩ : R8) := by
    unfold rnd; rw [hw10]; rfl
  rw [q10]
  have q11 : rnd S (⟨a_11, b_11, c_11, d_11, e_11, f_11, g_11, h_11⟩ : R8) 11 = (⟨a_12, b_12, c_12, d_12, e_12, f_12, g_12, h_12⟩ : R8) := by
    unfold rnd; rw [hw11]; rfl
  rw [q11]
  have q12 : rnd S (⟨a_12, b_12, c_12, d_12, e_12, f_12, g_12, h_12⟩ : R8) 12 = (⟨a_13, b_13, c_13, d_13, e_13, f_13, g_13, h_13⟩ : R8) := by
    unfold rnd; rw [hw12]; rfl
  rw [q12]
  have q13 : rnd S (⟨a_13, b_13, c_13, d_13, e_13, f_13, g_13, h_13⟩ : R8) 13 = (⟨a_14, b_14, c_14, d_14, e_14, f_14, g_14, h_14⟩ : R8) := by
    unfold rnd; rw [hw13]; rfl
  rw [q13]
  have q14 : rnd S (⟨a_14, b_14, c_14, d_14, e_14, f_14, g_14, h_14⟩ : R8) 14 = (⟨a_15, b_15, c_15, d_15, e_15, f_15, g_15, h_15⟩ : R8) := by
    unfold rnd; rw [hw14]; rfl
  rw [q14]
  have q15 : rnd S (⟨a_15, b_15, c_15, d_15, e_15, f_15, g_15, h_15⟩ : R8) 15 = (⟨a_16, b_16, c_16, d_16, e_16, f_16, g_16, h_16⟩ : R8) := by
    unfold rnd; rw [hw15]; rfl
  rw [q15]
  have q16 : rnd S (⟨a_16, b_16, c_16, d_16, e_16, f_16, g_16, h_16⟩ : R8) 16 = (⟨a_17, b_17, c_17, d_17, e_17, f_17, g_17, h_17⟩ : R8) := by
    unfold rnd; rw [hw16]; rfl
  rw [q16]
  have q17 : rnd S (⟨a_17, b_17, c_17, d_17, e_17, f_17, g_17, h_17⟩ : R8) 17 = (⟨a_18, b_18, c_18, d_18, e_18, f_18, g_18, h_18⟩ : R8) := by
    unfold rnd; rw [hw17]; rfl
  rw [q17]
  have q18 : rnd S (⟨a_18, b_18, c_18, d_18, e_18, f_18, g_18, h_18⟩ : R8) 18 = (⟨a_19, b_19, c_19, d_19, e_19, f_19, g_19, h_19⟩ : R8) := by
    unfold rnd; rw [hw18]; rfl
  rw [q18]
  have q19 : rnd S (⟨a_19, b_19, c_19, d_19, e_19, f_19, g_19, h_19⟩ : R8) 19 = (⟨a_20, b_20, c_20, d_20, e_20, f_20, g_20, h_20⟩ : R8) := by
    unfold rnd; rw [hw19]; rfl
  rw [q19]
  have q20 : rnd S (⟨a_20, b_20, c_20, d_20, e_20, f_20, g_20, h_20⟩ : R8) 20 = (⟨a_21, b_21, c_21, d_21, e_21, f_21, g_21, h_21⟩ : R8) := by
    unfold rnd; rw [hw20]; rfl
  rw [q20]
  have q21 : rnd S (⟨a_21, b_21, c_21, d_21, e_21, f_21, g_21, h_21⟩ : R8) 21 = (⟨a_22, b_22, c_22, d_22, e_22, f_22, g_22, h_22⟩ : R8) := by
    unfold rnd; rw [hw21]; rfl
  rw [q21]
  have q22 : rnd S (⟨a_22, b_22, c_22, d_22, e_22, f_22, g_22, h_22⟩ : R8) 22 = (⟨a_23, b_23, c_23, d_23, e_23, f_23, g_23, h_23⟩ : R8) := by
    unfold rnd; rw [hw22]; rfl
  rw [q22]
  have q23 : rnd S (⟨a_23, b_23, c_23, d_23, e_23, f_23, g_23, h_23⟩ : R8) 23 = (⟨a_24, b_24, c_24, d_24, e_24, f_24, g_24, h_24⟩ : R8) := by
    unfold rnd; rw [hw23]; rfl
  rw [q23]
  have q24 : rnd S (⟨a_24, b_24, c_24, d_24, e_24, f_24, g_24, h_24⟩ : R8) 24 = (⟨a_25, b_25, c_25, d_25, e_25, f_25, g_25, h_25⟩ : R8) := by
    unfold rnd; rw [hw24]; rfl
  rw [q24]
  have q25 : rnd S (⟨a_25, b_25, c_25, d_25, e_25, f_25, g_25, h_25⟩ : R8) 25 = (⟨a_26, b_26, c_26, d_26, e_26, f_26, g_26, h_26⟩ : R8) := by
    unfold rnd; rw [hw25]; rfl
  rw [q25]
  have q26 : rnd S (⟨a_26, b_26, c_26, d_26, e_26, f_26, g_26, h_26⟩ : R8) 26 = (⟨a_27, b_27, c_27, d_27, e_27, f_27, g_27, h_27⟩ : R8) := by
    unfold rnd; rw [hw26]; rfl
  rw [q26]
  have q27 : rnd S (⟨a_27, b_27, c_27, d_27, e_27, f_27, g_27, h_27⟩ : R8) 27 = (⟨a_28, b_28, c_28, d_28, e_28, f_28, g_28, h_28⟩ : R8) := by
    unfold rnd; rw [hw27]; rfl
  rw [q27]
  have q28 : rnd S (⟨a_28, b_28, c_28, d_28, e_28, f_28, g_28, h_28⟩ : R8) 28 = (⟨a_29, b_29, c_29, d_29, e_29, f_29, g_29, h_29⟩ : R8) := by
    unfold rnd; rw [hw28]; rfl
  rw [q28]
  have q29 : rnd S (⟨a_29, b_29, c_29, d_29, e_29, f_29, g_29, h_29⟩ : R8) 29 = (⟨a_30, b_30, c_30, d_30, e_30, f_30, g_30, h_30⟩ : R8) := by
    unfold rnd; rw [hw29]; rfl
  rw [q29]
  have q30 : rnd S (⟨a_30, b_30, c_30, d_30, e_30, f_30, g_30, h_30⟩ : R8) 30 = (⟨a_31, b_31, c_31, d_31, e_31, f_31, g_31, h_31⟩ : R8) := by
    unfold rnd; rw [hw30]; rfl
  rw [q30]
  have q31 : rnd S (⟨a_31, b_31, c_31, d_31, e_31, f_31, g_31, h_31⟩ : R8) 31 = (⟨a_32, b_32, c_32, d_32, e_32, f_32, g_32, h_32⟩ : R8) := by
    unfold rnd; rw [hw31]; rfl
  rw [q31]
  have q32 : rnd S (⟨a_32, b_32, c_32, d_32, e_32, f_32, g_32, h_32⟩ : R8) 32 = (⟨a_33, b_33, c_33, d_33, e_33, f_33, g_33, h_33⟩ : R8) := by
    unfold rnd; rw [hw32]; rfl
  rw [q32]
  have q33 : rnd S (⟨a_33, b_33, c_33, d_33, e_33, f_33, g_33, h_33⟩ : R8) 33 = (⟨a_34, b_34, c_34, d_34, e_34, f_34, g_34, h_34⟩ : R8) := by
    unfold rnd; rw [hw33]; rfl
  rw [q33]
  have q34 : rnd S (⟨a_34, b_34, c_34, d_34, e_34, f_34, g_34, h_34⟩ : R8) 34 = (⟨a_35, b_35, c_35, d_35, e_35, f_35, g_35, h_35⟩ : R8) := by
    unfold rnd; rw [hw34]; rfl
  rw [q34]
  have q35 : rnd S (⟨a_35, b_35, c_35, d_35, e_35, f_35, g_35, h_35⟩ : R8) 35 = (⟨a_36, b_36, c_36, d_36, e_36, f_36, g_36, h_36⟩ : R8) := by
    unfold rnd; rw [hw35]; rfl
  rw [q35]
  have q36 : rnd S (⟨a_36, b_36, c_36, d_36, e_36, f_36, g_36, h_36⟩ : R8) 36 = (⟨a_37, b_37, c_37, d_37, e_37, f_37, g_37, h_37⟩ : R8) := by
    unfold rnd; rw [hw36]; rfl
  rw [q36]
  have q37 : rnd S (⟨a_37, b_37, c_37, d_37, e_37, f_37, g_37, h_37⟩ : R8) 37 = (⟨a_38, b_38, c_38, d_38, e_38, f_38, g_38, h_38⟩ : R8) := by
    unfold rnd; rw [hw37]; rfl
  rw [q37]
  have q38 : rnd S (⟨a_38, b_38, c_38, d_38, e_38, f_38, g_38, h_38⟩ : R8) 38 = (⟨a_39, b_39, c_39, d_39, e_39, f_39, g_39, h_39⟩ : R8) := by
    unfold rnd; rw [hw38]; rfl
  rw [q38]
  have q39 : rnd S (⟨a_39, b_39, c_39, d_39, e_39, f_39, g_39, h_39⟩ : R8) 39 = (⟨a_40, b_40, c_40, d_40, e_40, f_40, g_40, h_40⟩ : R8) := by
    unfold rnd; rw [hw39]; rfl
  rw [q39]
  have q40 : rnd S (⟨a_40, b_40, c_40, d_40, e_40, f_40, g_40, h_40⟩ : R8) 40 = (⟨a_41, b_41, c_41, d_41, e_41, f_41, g_41, h_41⟩ : R8) := by
    unfold rnd; rw [hw40]; rfl
  rw [q40]
  have q41 : rnd S (⟨a_41, b_41, c_41, d_41, e_41, f_41, g_41, h_41⟩ : R8) 41 = (⟨a_42, b_42, c_42, d_42, e_42, f_42, g_42, h_42⟩ : R8) := by
    unfold rnd; rw [hw41]; rfl
  rw [q41]
  have q42 : rnd S (⟨a_42, b_42, c_42, d_42, e_42, f_42, g_42, h_42⟩ : R8) 42 = (⟨a_43, b_43, c_43, d_43, e_43, f_43, g_43, h_43⟩ : R8) := by
    unfold rnd; rw [hw42]; rfl
  rw [q42]
  have q43 : rnd S (⟨a_43, b_43, c_43, d_43, e_43, f_43, g_43, h_43⟩ : R8) 43 = (⟨a_44, b_44, c_44, d_44, e_44, f_44, g_44, h_44⟩ : R8) := by
    unfold rnd; rw [hw43]; rfl
  rw [q43]
  have q44 : rnd S (⟨a_44, b_44, c_44, d_44, e_44, f_44, g_44, h_44⟩ : R8) 44 = (⟨a_45, b_45, c_45, d_45, e_45, f_45, g_45, h_45⟩ : R8) := by
    unfold rnd; rw [hw44]; rfl
  rw [q44]
  have q45 : rnd S (⟨a_45, b_45, c_45, d_45, e_45, f_45, g_45, h_45⟩ : R8) 45 = (⟨a_46, b_46, c_46, d_46, e_46, f_46, g_46, h_46⟩ : R8) := by
    unfold rnd; rw [hw45]; rfl
  rw [q45]
  have q46 : rnd S (⟨a_46, b_46, c_46, d_46, e_46, f_46, g_46, h_46⟩ : R8) 46 = (⟨a_47, b_47, c_47, d_47, e_47, f_47, g_47, h_47⟩ : R8) := by
    unfold rnd; rw [hw46]; rfl
  rw [q46]
  have q47 : rnd S (⟨a_47, b_47, c_47, d_47, e_47, f_47, g_47, h_47⟩ : R8) 47 = (⟨a_48, b_48, c_48, d_48, e_48, f_48, g_48, h_48⟩ : R8) := by
    unfold rnd; rw [hw47]; rfl
  rw [q47]
  have q48 : rnd S (⟨a_48, b_48, c_48, d_48, e_48, f_48, g_48, h_48⟩ : R8) 48 = (⟨a_49, b_49, c_49, d_49, e_49, f_49, g_49, h_49⟩ : R8) := by
    unfold rnd; rw [hw48]; rfl
  rw [q48]
  have q49 : rnd S (⟨a_49, b_49, c_49, d_49, e_49, f_49, g_49, h_49⟩ : R8) 49 = (⟨a_50, b_50, c_50, d_50, e_50, f_50, g_50, h_50⟩ : R8) := by
    unfold rnd; rw [hw49]; rfl
  rw [q49]
  have q50 : rnd S (⟨a_50, b_50, c_50, d_50, e_50, f_50, g_50, h_50⟩ : R8) 50 = (⟨a_51, b_51, c_51, d_51, e_51, f_51, g_51, h_51⟩ : R8) := by
    unfold rnd; rw [hw50]; rfl
  rw [q50]
  have q51 : rnd S (⟨a_51, b_51, c_51, d_51, e_51, f_51, g_51, h_51⟩ : R8) 51 = (⟨a_52, b_52, c_52, d_52, e_52, f_52, g_52, h_52⟩ : R8) := by
    unfold rnd; rw [hw51]; rfl
  rw [q51]
  have q52 : rnd S (⟨a_52, b_52, c_52, d_52, e_52, f_52, g_52, h_52⟩ : R8) 52 = (⟨a_53, b_53, c_53, d_53, e_53, f_53, g_53, h_53⟩ : R8) := by
    unfold rnd; rw [hw52]; rfl
  rw [q52]
  have q53 : rnd S (⟨a_53, b_53, c_53, d_53, e_53, f_53, g_53, h_53⟩ : R8) 53 = (⟨a_54, b_54, c_54, d_54, e_54, f_54, g_54, h_54⟩ : R8) := by
    unfold rnd; rw [hw53]; rfl
  rw [q53]
  have q54 : rnd S (⟨a_54, b_54, c_54, d_54, e_54, f_54, g_54, h_54⟩ : R8) 54 = (⟨a_55, b_55, c_55, d_55, e_55, f_55, g_55, h_55⟩ : R8) := by
    unfold rnd; rw [hw54]; rfl
  rw [q54]
  have q55 : rnd S (⟨a_55, b_55, c_55, d_55, e_55, f_55, g_55, h_55⟩ : R8) 55 = (⟨a_56, b_56, c_56, d_56, e_56, f_56, g_56, h_56⟩ : R8) := by
    unfold rnd; rw [hw55]; rfl
  rw [q55]
  have q56 : rnd S (⟨a_56, b_56, c_56, d_56, e_56, f_56, g_56, h_56⟩ : R8) 56 = (⟨a_57, b_57, c_57, d_57, e_57, f_57, g_57, h_57⟩ : R8) := by
    unfold rnd; rw [hw56]; rfl
  rw [q56]
  have q57 : rnd S (⟨a_57, b_57, c_57, d_57, e_57, f_57, g_57, h_57⟩ : R8) 57 = (⟨a_58, b_58, c_58, d_58, e_58, f_58, g_58, h_58⟩ : R8) := by
    unfold rnd; rw [hw57]; rfl
  rw [q57]
  have q58 : rnd S (⟨a_58, b_58, c_58, d_58, e_58, f_58, g_58, h_58⟩ : R8) 58 = (⟨a_59, b_59, c_59, d_59, e_59, f_59, g_59, h_59⟩ : R8) := by
    unfold rnd; rw [hw58]; rfl
  rw [q58]
  have q59 : rnd S (⟨a_59, b_59, c_59, d_59, e_59, f_59, g_59, h_59⟩ : R8) 59 = (⟨a_60, b_60, c_60, d_60, e_60, f_60, g_60, h_60⟩ : R8) := by
    unfold rnd; rw [hw59]; rfl
  rw [q59]
  have q60 : rnd S (⟨a_60, b_60, c_60, d_60, e_60, f_60, g_60, h_60⟩ : R8) 60 = (⟨a_61, b_61, c_61, d_61, e_61, f_61, g_61, h_61⟩ : R8) := by
    unfold rnd; rw [hw60]; rfl
  rw [q60]
  have q61 : rnd S (⟨a_61, b_61, c_61, d_61, e_61, f_61, g_61, h_61⟩ : R8) 61 = (⟨a_62, b_62, c_62, d_62, e_62, f_62, g_62, h_62⟩ : R8) := by
    unfold rnd; rw [hw61]; rfl
  rw [q61]
  have q62 : rnd S (⟨a_62, b_62, c_62, d_62, e_62, f_62, g_62, h_62⟩ : R8) 62 = (⟨a_63, b_63, c_63, d_63, e_63, f_63, g_63, h_63⟩ : R8) := by
    unfold rnd; rw [hw62]; rfl
  rw [q62]
  have q63 : rnd S (⟨a_63, b_63, c_63, d_63, e_63, f_63, g_63, h_63⟩ : R8) 63 = (⟨a_64, b_64, c_64, d_64, e_64, f_64, g_64, h_64⟩ : R8) := by
    unfold rnd; rw [hw63]; rfl
  rw [q63]
  rfl

/-! ### Driver, padding and output -/

theorem hashGo_eq (buf : ByteArray) (n : Nat) : ∀ (H : Sha256Fast.St) (off : Nat),
    off + 64 * n ≤ buf.size →
    toArr (Sha256Fast.hashGo buf H off n) =
      (List.range' off n 64).foldl (fun Hs o => compressBlock Hs buf o) (toArr H) := by
  induction n with
  | zero => intro H off _; rfl
  | succ n ih =>
    intro H off h
    unfold Sha256Fast.hashGo
    rw [if_pos (by omega), List.range'_succ, List.foldl_cons, ← compress_eq]
    exact ih _ _ (by omega)

def H0 : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ### Padding -/

theorem get_set' {α : Type} [Inhabited α] (W : Array α) (i j : Nat) (v : α) (h : j < W.size) :
    (W.set! i v)[j]! = if i = j then v else W[j]! := by
  have h1 : (W.set! i v)[j]? = if i = j then (if i < W.size then some v else none) else W[j]? := by
    simp [Array.getElem?_setIfInBounds]
  have h2 : (W.set! i v)[j]! = ((W.set! i v)[j]?).getD default := by
    rw [getElem!_def]; cases (W.set! i v)[j]? <;> rfl
  have h3 : W[j]! = (W[j]?).getD default := by
    rw [getElem!_def]; cases W[j]? <;> rfl
  rw [h2, h1, h3]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij]

theorem push_get {α : Type} [Inhabited α] (W : Array α) (v : α) (j : Nat) (h : j < W.size + 1) :
    (W.push v)[j]! = if j < W.size then W[j]! else v := by
  have h2 : (W.push v)[j]! = ((W.push v)[j]?).getD default := by
    rw [getElem!_def]; cases (W.push v)[j]? <;> rfl
  have h3 : W[j]! = (W[j]?).getD default := by
    rw [getElem!_def]; cases W[j]? <;> rfl
  rw [h2, h3]
  by_cases hj : j < W.size
  · rw [if_pos hj, Array.getElem?_push_lt hj]
    simp [hj]
  · rw [if_neg hj]
    have : j = W.size := by omega
    subst this
    simp

theorem arr_ext_get {α : Type} [Inhabited α] (a b : Array α) (hs : a.size = b.size)
    (h : ∀ j, j < a.size → a[j]! = b[j]!) : a = b := by
  refine Array.ext hs fun j h1 h2 => ?_
  have := h j h1
  rwa [getElem!_pos a j h1, getElem!_pos b j h2] at this

/-- Byte `r` of the big-endian bit length. -/
def lenByte (bitLen : UInt64) (r : Nat) : UInt8 :=
  UInt8.ofNat (bitLen >>> UInt64.ofNat ((7 - r) * 8)).toNat

/-- Closed form of the padded message, byte by byte. -/
def padFn (msg : ByteArray) (j : Nat) : UInt8 :=
  let len := msg.size
  let z := (56 + 64 - ((len + 1) % 64)) % 64
  if j < len then msg[j]! else if j = len then 0x80 else
  if j < len + 1 + z then 0 else lenByte (UInt64.ofNat (len * 8)) (j - (len + 1 + z))

theorem forIn_zero_yield {β : Type} (n : Nat) (init : β) (f : Nat → β → β) :
    (forIn (m := Id) [:n] init (fun j acc => ForInStep.yield (f j acc)))
      = (List.range' 0 n).foldl (fun acc j => f j acc) init := by
  rw [forIn_range'_yield]
  have : [:n].size = n := by simp [Std.Legacy.Range.size]
  rw [this]

/-- Total length of the padded message. -/
abbrev padTotal (len : Nat) : Nat := len + 1 + (56 + 64 - ((len + 1) % 64)) % 64 + 8

theorem padTotal_facts (len : Nat) :
    len + 1 + 8 ≤ padTotal len ∧ padTotal len % 64 = 0 ∧
    padTotal len - 8 = len + 1 + (56 + 64 - ((len + 1) % 64)) % 64 ∧
    (len + 1 + (56 + 64 - ((len + 1) % 64)) % 64 < padTotal len) := by
  unfold padTotal; omega

/-- The spec's padding as folds. -/
def specPad (msg : ByteArray) : ByteArray :=
  let len := msg.size
  let bitLen : UInt64 := UInt64.ofNat (len * 8)
  let total := padTotal len
  (List.range' 0 8).foldl (fun B i => B.set! (total - 8 + i) (lenByte bitLen i))
    (((List.range' 0 len).foldl (fun (B : ByteArray) i => B.set! i msg[i]!)
      (ByteArray.mk (Array.replicate total 0))).set! len 0x80)

theorem padded_eq_specPad (msg : ByteArray) : padded msg = specPad msg := by
  unfold padded
  show forIn (m := Id) [:8] ((forIn (m := Id) [:msg.size] (ByteArray.mk (Array.replicate (padTotal msg.size) 0))
      (fun (i : Nat) (B : ByteArray) => ForInStep.yield (B.set! i msg[i]!))).set! msg.size 0x80)
      (fun (i : Nat) (B : ByteArray) => ForInStep.yield (B.set!
        (padTotal msg.size - 8 + i)
        (lenByte (UInt64.ofNat (msg.size * 8)) i))) = _
  rw [forIn_zero_yield, forIn_zero_yield]
  rfl

theorem setRange (B : ByteArray) (p : Nat → Nat) (c : Nat) (hp : ∀ i, p i = c + i) (v : Nat → UInt8)
    (n : Nat) (hn : c + n ≤ B.size) :
    ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.set! (p i) (v i)) B).size = B.size ∧
    ∀ j, j < B.size → ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.set! (p i) (v i)) B).data[j]! =
      if c ≤ j ∧ j < c + n then v (j - c) else B.data[j]! := by
  induction n with
  | zero => exact ⟨rfl, fun j hj => by simp⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    have hsz : ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.set! (p i) (v i)) B).data.size = B.size := ih1
    refine ⟨by rw [show ∀ (X : ByteArray) a b, (X.set! a b).size = X.size from fun X a b => by
      cases X; simp [ByteArray.set!, ByteArray.size], ih1], fun j hj => ?_⟩
    show (Array.set! _ _ _)[j]! = _
    rw [get_set' _ _ _ _ (by rw [hsz]; exact hj), hp, ih2 j hj]
    by_cases h : c + n = j
    · rw [if_pos h]; rw [if_pos (by omega)]; congr 1; omega
    · rw [if_neg h]
      by_cases h2 : c ≤ j ∧ j < c + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem pushRange (B : ByteArray) (v : Nat → UInt8) (n : Nat) :
    ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.push (v i)) B).size = B.size + n ∧
    ∀ j, j < B.size + n → ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.push (v i)) B).data[j]! =
      if j < B.size then B.data[j]! else v (j - B.size) := by
  induction n with
  | zero => exact ⟨rfl, fun j hj => by simp; omega⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    have hsz : ((List.range' 0 n).foldl (fun (B : ByteArray) i => B.push (v i)) B).data.size = B.size + n := ih1
    refine ⟨by show (Array.push _ _).size = _; rw [Array.size_push, hsz]; omega, fun j hj => ?_⟩
    show (Array.push _ _)[j]! = _
    rw [push_get _ _ _ (by rw [hsz]; omega), hsz]
    by_cases h : j < B.size + n
    · rw [if_pos h, ih2 j h]
    · rw [if_neg h]
      by_cases h2 : j < B.size
      · omega
      · rw [if_neg h2]; congr 1; omega

theorem rep_get (T j : Nat) (h : j < T) : (Array.replicate T (0 : UInt8))[j]! = 0 := by
  rw [getElem!_pos _ j (by simpa using h)]; simp

theorem specPad_facts (msg : ByteArray) :
    (specPad msg).size = padTotal msg.size ∧
    ∀ j, j < padTotal msg.size → (specPad msg).data[j]! = padFn msg j := by
  obtain ⟨pf1, pf2, pf3, pf4⟩ := padTotal_facts msg.size
  unfold specPad
  simp only []
  have hB0 : (ByteArray.mk (Array.replicate (padTotal msg.size) (0:UInt8))).size = padTotal msg.size := by
    show (Array.replicate _ (0:UInt8)).size = _
    rw [Array.size_replicate]
  obtain ⟨s1, s2⟩ := setRange (ByteArray.mk (Array.replicate (padTotal msg.size) (0:UInt8))) (fun i => i) 0
    (fun i => by simp) (fun i => msg[i]!) msg.size (by rw [hB0]; omega)
  generalize (List.range' 0 msg.size).foldl (fun (B : ByteArray) i => B.set! i msg[i]!)
    (ByteArray.mk (Array.replicate (padTotal msg.size) (0:UInt8))) = B1 at s1 s2
  rw [hB0] at s1 s2
  have hs2 : (B1.set! msg.size 0x80).size = padTotal msg.size := by
    have : ∀ (X : ByteArray) a b, (X.set! a b).size = X.size := fun X a b => by
      cases X; simp [ByteArray.set!, ByteArray.size]
    rw [this, s1]
  obtain ⟨t1, t2⟩ := setRange (B1.set! msg.size 0x80) (fun i => padTotal msg.size - 8 + i)
    (padTotal msg.size - 8) (fun i => rfl) (lenByte (UInt64.ofNat (msg.size * 8))) 8
    (by rw [hs2]; omega)
  refine ⟨by rw [t1, hs2], fun j hj => ?_⟩
  rw [hs2] at t2
  rw [t2 j hj]
  show _ = padFn msg j
  show (if padTotal msg.size - 8 ≤ j ∧ j < padTotal msg.size - 8 + 8 then _ else
    (Array.set! B1.data msg.size 0x80)[j]!) = _
  rw [get_set' _ _ _ _ (by rw [show B1.data.size = B1.size from rfl, s1]; exact hj), s2 j hj]
  unfold padFn
  simp only []
  rw [pf3]
  by_cases h1 : j < msg.size
  · rw [if_neg (by omega), if_neg (by omega), if_pos h1, if_pos (by omega)]
    simp only [Nat.sub_zero]
  · by_cases h2 : j = msg.size
    · subst h2
      rw [if_neg (by omega), if_pos rfl, if_neg h1, if_pos rfl]
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : j < msg.size + 1 + (56 + 64 - ((msg.size + 1) % 64)) % 64
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h3]
        exact rep_get _ _ (by omega)
      · rw [if_pos (by omega), if_neg h3]

theorem padded_size (msg : ByteArray) : (padded msg).size % 64 = 0 := by
  rw [padded_eq_specPad, (specPad_facts msg).1]; exact (padTotal_facts _).2.1

theorem bget2 (b : ByteArray) (j : Nat) : b[j]! = b.data[j]! := by
  rw [bget]
  cases b with | mk d =>
  by_cases h : j < d.size
  · simp [ByteArray.get!, getElem!_pos d j h]
  · simp [ByteArray.get!, getElem!_neg d j h]

/-- The fast padding as folds. -/
def fastPad (msg : ByteArray) : ByteArray :=
  (List.range' 0 8).foldl (fun (B : ByteArray) i => B.push (lenByte (UInt64.ofNat (msg.size * 8)) i))
    ((List.range' 0 ((56 + 64 - ((msg.size + 1) % 64)) % 64)).foldl
      (fun (B : ByteArray) _ => B.push 0) (msg.push 0x80))

theorem fastPad_eq (msg : ByteArray) : Sha256Fast.padded msg = fastPad msg := by
  unfold Sha256Fast.padded
  show forIn (m := Id) (β := ByteArray) [:8] (forIn (m := Id) [:(56 + 64 - ((msg.size + 1) % 64)) % 64] (msg.push 0x80)
      (fun (_ : Nat) (B : ByteArray) => ForInStep.yield (B.push 0)))
      (fun (i : Nat) (B : ByteArray) => ForInStep.yield (B.push (lenByte (UInt64.ofNat (msg.size * 8)) i))) = _
  rw [forIn_zero_yield, forIn_zero_yield]
  rfl

theorem fastPad_facts (msg : ByteArray) :
    (Sha256Fast.padded msg).size = padTotal msg.size ∧
    ∀ j, j < padTotal msg.size → (Sha256Fast.padded msg).data[j]! = padFn msg j := by
  obtain ⟨pf1, pf2, pf3, pf4⟩ := padTotal_facts msg.size
  rw [fastPad_eq]
  unfold fastPad
  have hP : (msg.push 0x80).size = msg.size + 1 := by
    cases msg; simp [ByteArray.push, ByteArray.size]
  obtain ⟨z1, z2⟩ := pushRange (msg.push 0x80) (fun _ => 0) ((56 + 64 - ((msg.size + 1) % 64)) % 64)
  generalize (List.range' 0 ((56 + 64 - ((msg.size + 1) % 64)) % 64)).foldl
    (fun (B : ByteArray) i => B.push ((fun (_ : Nat) => (0:UInt8)) i)) (msg.push 0x80) = Z at z1 z2
  rw [hP] at z1 z2
  obtain ⟨y1, y2⟩ := pushRange Z (fun i => lenByte (UInt64.ofNat (msg.size * 8)) i) 8
  generalize (List.range' 0 8).foldl
    (fun (B : ByteArray) i => B.push ((fun i => lenByte (UInt64.ofNat (msg.size * 8)) i) i)) Z = F at y1 y2
  rw [z1] at y1 y2
  refine ⟨by rw [y1], fun j hj => ?_⟩
  rw [y2 j (by unfold padTotal at hj; omega)]
  have hPd : ∀ i, i < msg.size + 1 → (msg.push 0x80).data[i]! = if i < msg.size then msg[i]! else 0x80 := by
    intro i hi
    show (Array.push msg.data 0x80)[i]! = _
    rw [push_get _ _ _ (by exact hi), bget2]
    rfl
  unfold padFn
  simp only []
  by_cases h1 : j < msg.size
  · rw [if_pos (by omega), z2 j (by omega), if_pos (by omega), hPd j (by omega), if_pos h1, if_pos h1]
  · by_cases h2 : j = msg.size
    · subst h2
      rw [if_pos (by omega), z2 _ (by omega), if_pos (by omega), hPd _ (by omega), if_neg h1, if_neg h1, if_pos rfl]
    · by_cases h3 : j < msg.size + 1 + (56 + 64 - ((msg.size + 1) % 64)) % 64
      · rw [if_pos (by omega), z2 j (by omega), if_neg h1, if_neg h2, if_pos h3]
        rw [if_neg (by omega)]
      · rw [if_neg (by omega), if_neg h1, if_neg h2, if_neg h3]

theorem padded_eq (msg : ByteArray) : Sha256Fast.padded msg = padded msg := by
  rw [padded_eq_specPad]
  obtain ⟨a1, a2⟩ := fastPad_facts msg
  obtain ⟨b1, b2⟩ := specPad_facts msg
  generalize Sha256Fast.padded msg = F at a1 a2 ⊢
  generalize specPad msg = S at b1 b2 ⊢
  apply ByteArray.ext_getElem
  · exact a1.trans b1.symm
  · intro j hj hj'
    have hj2 : j < padTotal msg.size := lt_of_lt_of_eq hj a1
    have e1 := getElem!_pos F j hj
    have e2 := getElem!_pos S j hj'
    rw [bget2] at e1 e2
    rw [← e1, ← e2, a2 j hj2, b2 j hj2]


/-- One iteration of the spec's output-packing loop. -/
def packStep (H : Array UInt32) (out : ByteArray) (i : Nat) : ByteArray :=
  let h := H[i]!
  let out := out.set! (4*i)     (UInt8.ofNat ((h >>> 24).toNat))
  let out := out.set! (4*i + 1) (UInt8.ofNat ((h >>> 16).toNat &&& 0xff))
  let out := out.set! (4*i + 2) (UInt8.ofNat ((h >>>  8).toNat &&& 0xff))
  out.set! (4*i + 3) (UInt8.ofNat (h.toNat &&& 0xff))

/-- The spec's output packing. -/
def packOut (H : Array UInt32) : ByteArray :=
  (List.range' 0 8).foldl (packStep H) (ByteArray.mk (Array.replicate 32 0))

theorem byte0 (w : UInt32) : (w >>> 24).toUInt8 = UInt8.ofNat ((w >>> 24).toNat) := by
  apply UInt8.toNat_inj.mp
  simp

theorem byte1 (w : UInt32) : (w >>> 16).toUInt8 = UInt8.ofNat ((w >>> 16).toNat &&& 0xff) := by
  apply UInt8.toNat_inj.mp
  simp
  have : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  rw [this]; omega

theorem byte2 (w : UInt32) : (w >>> 8).toUInt8 = UInt8.ofNat ((w >>> 8).toNat &&& 0xff) := by
  apply UInt8.toNat_inj.mp
  simp
  have : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  rw [this]; omega

theorem byte3 (w : UInt32) : w.toUInt8 = UInt8.ofNat (w.toNat &&& 0xff) := by
  apply UInt8.toNat_inj.mp
  simp
  have : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  rw [this]; omega

theorem pack_eq (H : Sha256Fast.St) :
    Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE
      (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (ByteArray.emptyWithCapacity 32)
        H.a) H.b) H.c) H.d) H.e) H.f) H.g) H.h = packOut (toArr H) := by
  unfold packOut
  rw [show List.range' 0 8 = [0,1,2,3,4,5,6,7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  have l0 : ByteArray.emptyWithCapacity 32 = (⟨#[]⟩ : ByteArray) := rfl
  rw [l0]
  have l1 : Sha256Fast.pushBE (⟨#[]⟩ : ByteArray) H.a = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.a, byte1 H.a, byte2 H.a, byte3 H.a]; rfl
  rw [l1]
  have l2 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255)]⟩ : ByteArray) H.b = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.b, byte1 H.b, byte2 H.b, byte3 H.b]; rfl
  rw [l2]
  have l3 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255)]⟩ : ByteArray) H.c = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.c, byte1 H.c, byte2 H.c, byte3 H.c]; rfl
  rw [l3]
  have l4 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255)]⟩ : ByteArray) H.d = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.d, byte1 H.d, byte2 H.d, byte3 H.d]; rfl
  rw [l4]
  have l5 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255)]⟩ : ByteArray) H.e = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.e, byte1 H.e, byte2 H.e, byte3 H.e]; rfl
  rw [l5]
  have l6 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255)]⟩ : ByteArray) H.f = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.f, byte1 H.f, byte2 H.f, byte3 H.f]; rfl
  rw [l6]
  have l7 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255)]⟩ : ByteArray) H.g = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.g, byte1 H.g, byte2 H.g, byte3 H.g]; rfl
  rw [l7]
  have l8 : Sha256Fast.pushBE (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255)]⟩ : ByteArray) H.h = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255), UInt8.ofNat ((H.h >>> 24).toNat), UInt8.ofNat ((H.h >>> 16).toNat &&& 255), UInt8.ofNat ((H.h >>> 8).toNat &&& 255), UInt8.ofNat (H.h.toNat &&& 255)]⟩ := by
    unfold Sha256Fast.pushBE; simp only [byte0 H.h, byte1 H.h, byte2 H.h, byte3 H.h]; rfl
  rw [l8]
  have r0 : ByteArray.mk (Array.replicate 32 0) = (⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) := rfl
  rw [r0]
  have s0 : packStep (toArr H) (⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 0 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s0]
  have s1 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 1 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s1]
  have s2 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 2 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s2]
  have s3 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 3 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s3]
  have s4 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 4 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s4]
  have s5 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 5 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0]⟩ := rfl
  rw [s5]
  have s6 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) 6 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255), 0, 0, 0, 0]⟩ := rfl
  rw [s6]
  have s7 : packStep (toArr H) (⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255), 0, 0, 0, 0]⟩ : ByteArray) 7 = ⟨#[UInt8.ofNat ((H.a >>> 24).toNat), UInt8.ofNat ((H.a >>> 16).toNat &&& 255), UInt8.ofNat ((H.a >>> 8).toNat &&& 255), UInt8.ofNat (H.a.toNat &&& 255), UInt8.ofNat ((H.b >>> 24).toNat), UInt8.ofNat ((H.b >>> 16).toNat &&& 255), UInt8.ofNat ((H.b >>> 8).toNat &&& 255), UInt8.ofNat (H.b.toNat &&& 255), UInt8.ofNat ((H.c >>> 24).toNat), UInt8.ofNat ((H.c >>> 16).toNat &&& 255), UInt8.ofNat ((H.c >>> 8).toNat &&& 255), UInt8.ofNat (H.c.toNat &&& 255), UInt8.ofNat ((H.d >>> 24).toNat), UInt8.ofNat ((H.d >>> 16).toNat &&& 255), UInt8.ofNat ((H.d >>> 8).toNat &&& 255), UInt8.ofNat (H.d.toNat &&& 255), UInt8.ofNat ((H.e >>> 24).toNat), UInt8.ofNat ((H.e >>> 16).toNat &&& 255), UInt8.ofNat ((H.e >>> 8).toNat &&& 255), UInt8.ofNat (H.e.toNat &&& 255), UInt8.ofNat ((H.f >>> 24).toNat), UInt8.ofNat ((H.f >>> 16).toNat &&& 255), UInt8.ofNat ((H.f >>> 8).toNat &&& 255), UInt8.ofNat (H.f.toNat &&& 255), UInt8.ofNat ((H.g >>> 24).toNat), UInt8.ofNat ((H.g >>> 16).toNat &&& 255), UInt8.ofNat ((H.g >>> 8).toNat &&& 255), UInt8.ofNat (H.g.toNat &&& 255), UInt8.ofNat ((H.h >>> 24).toNat), UInt8.ofNat ((H.h >>> 16).toNat &&& 255), UInt8.ofNat ((H.h >>> 8).toNat &&& 255), UInt8.ofNat (H.h.toNat &&& 255)]⟩ := rfl
  rw [s7]

theorem hash_spec_form (msg : ByteArray) :
    EthLib.Cryptography.Bls.Sha256.hash msg =
      packOut ((List.range' 0 ((padded msg).size / 64) 64).foldl
        (fun Hs o => compressBlock Hs (padded msg) o) H0) := by
  have hs := padded_size msg
  have e : forIn (m := Id) [0 : (padded msg).size : 64] H0
      (fun (off : Nat) (H : Array UInt32) => ForInStep.yield (compressBlock H (padded msg) off)) =
      (List.range' 0 ((padded msg).size / 64) 64).foldl
        (fun Hs o => compressBlock Hs (padded msg) o) H0 := by
    rw [forIn_range'_yield]
    have : [0 : (padded msg).size : 64].size = (padded msg).size / 64 := by
      simp only [Std.Legacy.Range.size]; omega
    rw [this]
  have e2 : ∀ H : Array UInt32, forIn (m := Id) [:8] (ByteArray.mk (Array.replicate 32 0))
      (fun (i : Nat) (out : ByteArray) => ForInStep.yield (packStep H out i)) = packOut H :=
    fun H => forIn_range'_yield [:8] _ (fun i out => packStep H out i)
  unfold EthLib.Cryptography.Bls.Sha256.hash
  show forIn (m := Id) [:8] (ByteArray.mk (Array.replicate 32 0))
    (fun (i : Nat) (out : ByteArray) => ForInStep.yield (packStep
      (forIn (m := Id) [0 : (padded msg).size : 64] H0
        (fun (off : Nat) (H : Array UInt32) => ForInStep.yield (compressBlock H (padded msg) off))) out i)) = _
  rw [e, e2]

theorem _root_.EthLibImpl.Cryptography.Bls.Sha256Fast.hash_eq (msg : ByteArray) :
    Sha256Fast.hash msg = EthLib.Cryptography.Bls.Sha256.hash msg := by
  rw [hash_spec_form]
  unfold Sha256Fast.hash
  simp only []
  rw [pack_eq, padded_eq]
  congr 1
  exact (hashGo_eq _ _ _ 0 (by have := padded_size msg; omega)).trans rfl

end EthLibImpl.Cryptography.Proofs.Sha256Fast
