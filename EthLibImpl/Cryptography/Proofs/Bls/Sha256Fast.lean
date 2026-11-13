import EthLibImpl.Cryptography.Bls.Sha256Fast
import EthLib.Cryptography.Hash.Sha256

/-!
# Proofs: `Sha256Fast.hash` computes the spec's `Hash.Sha256.hash`

`Sha256Fast` unrolls the compression function over eight `UInt32` registers, names the 64 words
of the message schedule, and pads by pushing bytes onto the message. The spec
(`EthLib.Cryptography.Hash.Sha256`) keeps the working variables in a `State` record, slides a
sixteen-word `Window` once per round constant, and pads by appending byte arrays. The main result
is `Sha256Fast.hash_eq`, which holds for every message.
-/

namespace EthLibImpl.Cryptography.Proofs.Sha256Fast
open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Hash

/-- The fast state as the spec's state. -/
def toState (s : Sha256Fast.St) : Sha256.State := ⟨s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h⟩

/-! ### Words -/

theorem get!_eq (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  cases b with | mk d => exact getElem!_pos d i h

/-- Within the array, the fast big-endian read is the spec's `big32` of the four bytes. -/
theorem be32_eq (b : ByteArray) (i : Nat) (h : i + 3 < b.size) :
    Sha256Fast.be32 b i = Sha256.big32 (b[i]'(by omega)) (b[i + 1]'(by omega))
      (b[i + 2]'(by omega)) (b[i + 3]'h) := by
  unfold Sha256Fast.be32 Sha256.big32
  rw [get!_eq b i (by omega), get!_eq b (i + 1) (by omega), get!_eq b (i + 2) (by omega),
    get!_eq b (i + 3) h]

theorem ss0_fun : Sha256Fast.ss0 = Sha256.smallSigma0 := rfl
theorem ss1_fun : Sha256Fast.ss1 = Sha256.smallSigma1 := rfl
theorem bs0_fun : Sha256Fast.bs0 = Sha256.bigSigma0 := rfl
theorem bs1_fun : Sha256Fast.bs1 = Sha256.bigSigma1 := rfl
theorem ch_fun : Sha256Fast.ch = Sha256.ch := rfl
theorem maj_fun : Sha256Fast.maj = Sha256.maj := rfl

/-- The spec's first window holds the sixteen words the fast code reads from the block. -/
theorem ofBlock_eq (buf : ByteArray) (off : Nat) (whole : off + 64 ≤ buf.size) :
    Sha256.Window.ofBlock buf off whole =
      ⟨Sha256Fast.be32 buf (off + 4 * 0), Sha256Fast.be32 buf (off + 4 * 1),
        Sha256Fast.be32 buf (off + 4 * 2), Sha256Fast.be32 buf (off + 4 * 3),
        Sha256Fast.be32 buf (off + 4 * 4), Sha256Fast.be32 buf (off + 4 * 5),
        Sha256Fast.be32 buf (off + 4 * 6), Sha256Fast.be32 buf (off + 4 * 7),
        Sha256Fast.be32 buf (off + 4 * 8), Sha256Fast.be32 buf (off + 4 * 9),
        Sha256Fast.be32 buf (off + 4 * 10), Sha256Fast.be32 buf (off + 4 * 11),
        Sha256Fast.be32 buf (off + 4 * 12), Sha256Fast.be32 buf (off + 4 * 13),
        Sha256Fast.be32 buf (off + 4 * 14), Sha256Fast.be32 buf (off + 4 * 15)⟩ := by
  rw [be32_eq buf (off + 4 * 0) (by omega), be32_eq buf (off + 4 * 1) (by omega),
    be32_eq buf (off + 4 * 2) (by omega), be32_eq buf (off + 4 * 3) (by omega),
    be32_eq buf (off + 4 * 4) (by omega), be32_eq buf (off + 4 * 5) (by omega),
    be32_eq buf (off + 4 * 6) (by omega), be32_eq buf (off + 4 * 7) (by omega),
    be32_eq buf (off + 4 * 8) (by omega), be32_eq buf (off + 4 * 9) (by omega),
    be32_eq buf (off + 4 * 10) (by omega), be32_eq buf (off + 4 * 11) (by omega),
    be32_eq buf (off + 4 * 12) (by omega), be32_eq buf (off + 4 * 13) (by omega),
    be32_eq buf (off + 4 * 14) (by omega), be32_eq buf (off + 4 * 15) (by omega)]
  rfl

/-! ### One block -/

/-- The round constants as a list, one cons per constant. -/
theorem K_toList : Sha256.K.toList =
    0x428a2f98 :: 0x71374491 :: 0xb5c0fbcf :: 0xe9b5dba5 :: 0x3956c25b :: 0x59f111f1 ::
    0x923f82a4 :: 0xab1c5ed5 :: 0xd807aa98 :: 0x12835b01 :: 0x243185be :: 0x550c7dc3 ::
    0x72be5d74 :: 0x80deb1fe :: 0x9bdc06a7 :: 0xc19bf174 :: 0xe49b69c1 :: 0xefbe4786 ::
    0x0fc19dc6 :: 0x240ca1cc :: 0x2de92c6f :: 0x4a7484aa :: 0x5cb0a9dc :: 0x76f988da ::
    0x983e5152 :: 0xa831c66d :: 0xb00327c8 :: 0xbf597fc7 :: 0xc6e00bf3 :: 0xd5a79147 ::
    0x06ca6351 :: 0x14292967 :: 0x27b70a85 :: 0x2e1b2138 :: 0x4d2c6dfc :: 0x53380d13 ::
    0x650a7354 :: 0x766a0abb :: 0x81c2c92e :: 0x92722c85 :: 0xa2bfe8a1 :: 0xa81a664b ::
    0xc24b8b70 :: 0xc76c51a3 :: 0xd192e819 :: 0xd6990624 :: 0xf40e3585 :: 0x106aa070 ::
    0x19a4c116 :: 0x1e376c08 :: 0x2748774c :: 0x34b0bcb5 :: 0x391c0cb3 :: 0x4ed8aa4a ::
    0x5b9cca4f :: 0x682e6ff3 :: 0x748f82ee :: 0x78a5636f :: 0x84c87814 :: 0x8cc70208 ::
    0x90befffa :: 0xa4506ceb :: 0xbef9a3f7 :: 0xc67178f2 :: [] := rfl

/-- One round of the spec's `rounds`, with the next window and state given. -/
theorem rounds_step (c : UInt32) (rest : List UInt32) (w w' : Sha256.Window) (s s' : Sha256.State)
    (hw : w.next = w') (hs : Sha256.round s c w.w0 = s') :
    Sha256.rounds (c :: rest) w s = Sha256.rounds rest w' s' := by
  subst hw hs; rfl

/-- The window `n` moves on from `w`. -/
def windowAfter : Nat → Sha256.Window → Sha256.Window
  | 0, w => w
  | n + 1, w => (windowAfter n w).next

set_option maxRecDepth 100000 in
/--
The fast compression function equals the spec's on a whole block.

Each round is checked on its own, against the fast code's named words and registers. Up to round
48 the window is written with the named words. From there on it is `windowAfter`, because the
spec keeps sliding it past the 64 words that the rounds read.
-/
theorem compress_eq (H : Sha256Fast.St) (buf : ByteArray) (off : Nat)
    (whole : off + 64 ≤ buf.size) :
    toState (Sha256Fast.compress H buf off) = Sha256.compress (toState H) buf off whole := by
  unfold Sha256Fast.compress
  rw [ss0_fun, ss1_fun, bs0_fun, bs1_fun, ch_fun, maj_fun]
  extract_lets w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
    w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46
    w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 w60 w61 w62 w63 a_0 b_0 c_0 d_0 e_0 f_0 g_0
    h_0 t1_1 t2_1 h_1 g_1 f_1 e_1 d_1 c_1 b_1 a_1 t1_2 t2_2 h_2 g_2 f_2 e_2 d_2 c_2 b_2 a_2 t1_3
    t2_3 h_3 g_3 f_3 e_3 d_3 c_3 b_3 a_3 t1_4 t2_4 h_4 g_4 f_4 e_4 d_4 c_4 b_4 a_4 t1_5 t2_5 h_5 g_5
    f_5 e_5 d_5 c_5 b_5 a_5 t1_6 t2_6 h_6 g_6 f_6 e_6 d_6 c_6 b_6 a_6 t1_7 t2_7 h_7 g_7 f_7 e_7 d_7
    c_7 b_7 a_7 t1_8 t2_8 h_8 g_8 f_8 e_8 d_8 c_8 b_8 a_8 t1_9 t2_9 h_9 g_9 f_9 e_9 d_9 c_9 b_9 a_9
    t1_10 t2_10 h_10 g_10 f_10 e_10 d_10 c_10 b_10 a_10 t1_11 t2_11 h_11 g_11 f_11 e_11 d_11 c_11
    b_11 a_11 t1_12 t2_12 h_12 g_12 f_12 e_12 d_12 c_12 b_12 a_12 t1_13 t2_13 h_13 g_13 f_13 e_13
    d_13 c_13 b_13 a_13 t1_14 t2_14 h_14 g_14 f_14 e_14 d_14 c_14 b_14 a_14 t1_15 t2_15 h_15 g_15
    f_15 e_15 d_15 c_15 b_15 a_15 t1_16 t2_16 h_16 g_16 f_16 e_16 d_16 c_16 b_16 a_16 t1_17 t2_17
    h_17 g_17 f_17 e_17 d_17 c_17 b_17 a_17 t1_18 t2_18 h_18 g_18 f_18 e_18 d_18 c_18 b_18 a_18
    t1_19 t2_19 h_19 g_19 f_19 e_19 d_19 c_19 b_19 a_19 t1_20 t2_20 h_20 g_20 f_20 e_20 d_20 c_20
    b_20 a_20 t1_21 t2_21 h_21 g_21 f_21 e_21 d_21 c_21 b_21 a_21 t1_22 t2_22 h_22 g_22 f_22 e_22
    d_22 c_22 b_22 a_22 t1_23 t2_23 h_23 g_23 f_23 e_23 d_23 c_23 b_23 a_23 t1_24 t2_24 h_24 g_24
    f_24 e_24 d_24 c_24 b_24 a_24 t1_25 t2_25 h_25 g_25 f_25 e_25 d_25 c_25 b_25 a_25 t1_26 t2_26
    h_26 g_26 f_26 e_26 d_26 c_26 b_26 a_26 t1_27 t2_27 h_27 g_27 f_27 e_27 d_27 c_27 b_27 a_27
    t1_28 t2_28 h_28 g_28 f_28 e_28 d_28 c_28 b_28 a_28 t1_29 t2_29 h_29 g_29 f_29 e_29 d_29 c_29
    b_29 a_29 t1_30 t2_30 h_30 g_30 f_30 e_30 d_30 c_30 b_30 a_30 t1_31 t2_31 h_31 g_31 f_31 e_31
    d_31 c_31 b_31 a_31 t1_32 t2_32 h_32 g_32 f_32 e_32 d_32 c_32 b_32 a_32 t1_33 t2_33 h_33 g_33
    f_33 e_33 d_33 c_33 b_33 a_33 t1_34 t2_34 h_34 g_34 f_34 e_34 d_34 c_34 b_34 a_34 t1_35 t2_35
    h_35 g_35 f_35 e_35 d_35 c_35 b_35 a_35 t1_36 t2_36 h_36 g_36 f_36 e_36 d_36 c_36 b_36 a_36
    t1_37 t2_37 h_37 g_37 f_37 e_37 d_37 c_37 b_37 a_37 t1_38 t2_38 h_38 g_38 f_38 e_38 d_38 c_38
    b_38 a_38 t1_39 t2_39 h_39 g_39 f_39 e_39 d_39 c_39 b_39 a_39 t1_40 t2_40 h_40 g_40 f_40 e_40
    d_40 c_40 b_40 a_40 t1_41 t2_41 h_41 g_41 f_41 e_41 d_41 c_41 b_41 a_41 t1_42 t2_42 h_42 g_42
    f_42 e_42 d_42 c_42 b_42 a_42 t1_43 t2_43 h_43 g_43 f_43 e_43 d_43 c_43 b_43 a_43 t1_44 t2_44
    h_44 g_44 f_44 e_44 d_44 c_44 b_44 a_44 t1_45 t2_45 h_45 g_45 f_45 e_45 d_45 c_45 b_45 a_45
    t1_46 t2_46 h_46 g_46 f_46 e_46 d_46 c_46 b_46 a_46 t1_47 t2_47 h_47 g_47 f_47 e_47 d_47 c_47
    b_47 a_47 t1_48 t2_48 h_48 g_48 f_48 e_48 d_48 c_48 b_48 a_48 t1_49 t2_49 h_49 g_49 f_49 e_49
    d_49 c_49 b_49 a_49 t1_50 t2_50 h_50 g_50 f_50 e_50 d_50 c_50 b_50 a_50 t1_51 t2_51 h_51 g_51
    f_51 e_51 d_51 c_51 b_51 a_51 t1_52 t2_52 h_52 g_52 f_52 e_52 d_52 c_52 b_52 a_52 t1_53 t2_53
    h_53 g_53 f_53 e_53 d_53 c_53 b_53 a_53 t1_54 t2_54 h_54 g_54 f_54 e_54 d_54 c_54 b_54 a_54
    t1_55 t2_55 h_55 g_55 f_55 e_55 d_55 c_55 b_55 a_55 t1_56 t2_56 h_56 g_56 f_56 e_56 d_56 c_56
    b_56 a_56 t1_57 t2_57 h_57 g_57 f_57 e_57 d_57 c_57 b_57 a_57 t1_58 t2_58 h_58 g_58 f_58 e_58
    d_58 c_58 b_58 a_58 t1_59 t2_59 h_59 g_59 f_59 e_59 d_59 c_59 b_59 a_59 t1_60 t2_60 h_60 g_60
    f_60 e_60 d_60 c_60 b_60 a_60 t1_61 t2_61 h_61 g_61 f_61 e_61 d_61 c_61 b_61 a_61 t1_62 t2_62
    h_62 g_62 f_62 e_62 d_62 c_62 b_62 a_62 t1_63 t2_63 h_63 g_63 f_63 e_63 d_63 c_63 b_63 a_63
    t1_64 t2_64 h_64 g_64 f_64 e_64 d_64 c_64 b_64 a_64
  have hW : Sha256.Window.ofBlock buf off whole =
      ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    ofBlock_eq buf off whole
  have hS : toState H = (⟨a_0, b_0, c_0, d_0, e_0, f_0, g_0, h_0⟩ : Sha256.State) := rfl
  have hR : Sha256.rounds Sha256.K.toList (Sha256.Window.ofBlock buf off whole) (toState H) =
      (⟨a_64, b_64, c_64, d_64, e_64, f_64, g_64, h_64⟩ : Sha256.State) := by
    rw [K_toList, hW, hS]
    refine Eq.trans (rounds_step 0x428a2f98 _
      ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩
      ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16⟩
      ⟨a_0, b_0, c_0, d_0, e_0, f_0, g_0, h_0⟩
      ⟨a_1, b_1, c_1, d_1, e_1, f_1, g_1, h_1⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x71374491 _
      ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16⟩
      ⟨w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17⟩
      ⟨a_1, b_1, c_1, d_1, e_1, f_1, g_1, h_1⟩
      ⟨a_2, b_2, c_2, d_2, e_2, f_2, g_2, h_2⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xb5c0fbcf _
      ⟨w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17⟩
      ⟨w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18⟩
      ⟨a_2, b_2, c_2, d_2, e_2, f_2, g_2, h_2⟩
      ⟨a_3, b_3, c_3, d_3, e_3, f_3, g_3, h_3⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xe9b5dba5 _
      ⟨w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18⟩
      ⟨w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19⟩
      ⟨a_3, b_3, c_3, d_3, e_3, f_3, g_3, h_3⟩
      ⟨a_4, b_4, c_4, d_4, e_4, f_4, g_4, h_4⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x3956c25b _
      ⟨w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19⟩
      ⟨w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20⟩
      ⟨a_4, b_4, c_4, d_4, e_4, f_4, g_4, h_4⟩
      ⟨a_5, b_5, c_5, d_5, e_5, f_5, g_5, h_5⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x59f111f1 _
      ⟨w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20⟩
      ⟨w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21⟩
      ⟨a_5, b_5, c_5, d_5, e_5, f_5, g_5, h_5⟩
      ⟨a_6, b_6, c_6, d_6, e_6, f_6, g_6, h_6⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x923f82a4 _
      ⟨w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21⟩
      ⟨w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22⟩
      ⟨a_6, b_6, c_6, d_6, e_6, f_6, g_6, h_6⟩
      ⟨a_7, b_7, c_7, d_7, e_7, f_7, g_7, h_7⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xab1c5ed5 _
      ⟨w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22⟩
      ⟨w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23⟩
      ⟨a_7, b_7, c_7, d_7, e_7, f_7, g_7, h_7⟩
      ⟨a_8, b_8, c_8, d_8, e_8, f_8, g_8, h_8⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xd807aa98 _
      ⟨w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23⟩
      ⟨w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24⟩
      ⟨a_8, b_8, c_8, d_8, e_8, f_8, g_8, h_8⟩
      ⟨a_9, b_9, c_9, d_9, e_9, f_9, g_9, h_9⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x12835b01 _
      ⟨w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24⟩
      ⟨w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25⟩
      ⟨a_9, b_9, c_9, d_9, e_9, f_9, g_9, h_9⟩
      ⟨a_10, b_10, c_10, d_10, e_10, f_10, g_10, h_10⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x243185be _
      ⟨w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25⟩
      ⟨w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩
      ⟨a_10, b_10, c_10, d_10, e_10, f_10, g_10, h_10⟩
      ⟨a_11, b_11, c_11, d_11, e_11, f_11, g_11, h_11⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x550c7dc3 _
      ⟨w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩
      ⟨w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27⟩
      ⟨a_11, b_11, c_11, d_11, e_11, f_11, g_11, h_11⟩
      ⟨a_12, b_12, c_12, d_12, e_12, f_12, g_12, h_12⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x72be5d74 _
      ⟨w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27⟩
      ⟨w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28⟩
      ⟨a_12, b_12, c_12, d_12, e_12, f_12, g_12, h_12⟩
      ⟨a_13, b_13, c_13, d_13, e_13, f_13, g_13, h_13⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x80deb1fe _
      ⟨w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28⟩
      ⟨w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29⟩
      ⟨a_13, b_13, c_13, d_13, e_13, f_13, g_13, h_13⟩
      ⟨a_14, b_14, c_14, d_14, e_14, f_14, g_14, h_14⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x9bdc06a7 _
      ⟨w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29⟩
      ⟨w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
      ⟨a_14, b_14, c_14, d_14, e_14, f_14, g_14, h_14⟩
      ⟨a_15, b_15, c_15, d_15, e_15, f_15, g_15, h_15⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xc19bf174 _
      ⟨w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
      ⟨w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩
      ⟨a_15, b_15, c_15, d_15, e_15, f_15, g_15, h_15⟩
      ⟨a_16, b_16, c_16, d_16, e_16, f_16, g_16, h_16⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xe49b69c1 _
      ⟨w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩
      ⟨w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32⟩
      ⟨a_16, b_16, c_16, d_16, e_16, f_16, g_16, h_16⟩
      ⟨a_17, b_17, c_17, d_17, e_17, f_17, g_17, h_17⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xefbe4786 _
      ⟨w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32⟩
      ⟨w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33⟩
      ⟨a_17, b_17, c_17, d_17, e_17, f_17, g_17, h_17⟩
      ⟨a_18, b_18, c_18, d_18, e_18, f_18, g_18, h_18⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x0fc19dc6 _
      ⟨w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33⟩
      ⟨w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34⟩
      ⟨a_18, b_18, c_18, d_18, e_18, f_18, g_18, h_18⟩
      ⟨a_19, b_19, c_19, d_19, e_19, f_19, g_19, h_19⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x240ca1cc _
      ⟨w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34⟩
      ⟨w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35⟩
      ⟨a_19, b_19, c_19, d_19, e_19, f_19, g_19, h_19⟩
      ⟨a_20, b_20, c_20, d_20, e_20, f_20, g_20, h_20⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x2de92c6f _
      ⟨w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35⟩
      ⟨w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36⟩
      ⟨a_20, b_20, c_20, d_20, e_20, f_20, g_20, h_20⟩
      ⟨a_21, b_21, c_21, d_21, e_21, f_21, g_21, h_21⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x4a7484aa _
      ⟨w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36⟩
      ⟨w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37⟩
      ⟨a_21, b_21, c_21, d_21, e_21, f_21, g_21, h_21⟩
      ⟨a_22, b_22, c_22, d_22, e_22, f_22, g_22, h_22⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x5cb0a9dc _
      ⟨w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37⟩
      ⟨w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38⟩
      ⟨a_22, b_22, c_22, d_22, e_22, f_22, g_22, h_22⟩
      ⟨a_23, b_23, c_23, d_23, e_23, f_23, g_23, h_23⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x76f988da _
      ⟨w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38⟩
      ⟨w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39⟩
      ⟨a_23, b_23, c_23, d_23, e_23, f_23, g_23, h_23⟩
      ⟨a_24, b_24, c_24, d_24, e_24, f_24, g_24, h_24⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x983e5152 _
      ⟨w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39⟩
      ⟨w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40⟩
      ⟨a_24, b_24, c_24, d_24, e_24, f_24, g_24, h_24⟩
      ⟨a_25, b_25, c_25, d_25, e_25, f_25, g_25, h_25⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xa831c66d _
      ⟨w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40⟩
      ⟨w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41⟩
      ⟨a_25, b_25, c_25, d_25, e_25, f_25, g_25, h_25⟩
      ⟨a_26, b_26, c_26, d_26, e_26, f_26, g_26, h_26⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xb00327c8 _
      ⟨w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41⟩
      ⟨w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42⟩
      ⟨a_26, b_26, c_26, d_26, e_26, f_26, g_26, h_26⟩
      ⟨a_27, b_27, c_27, d_27, e_27, f_27, g_27, h_27⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xbf597fc7 _
      ⟨w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42⟩
      ⟨w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43⟩
      ⟨a_27, b_27, c_27, d_27, e_27, f_27, g_27, h_27⟩
      ⟨a_28, b_28, c_28, d_28, e_28, f_28, g_28, h_28⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xc6e00bf3 _
      ⟨w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43⟩
      ⟨w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44⟩
      ⟨a_28, b_28, c_28, d_28, e_28, f_28, g_28, h_28⟩
      ⟨a_29, b_29, c_29, d_29, e_29, f_29, g_29, h_29⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xd5a79147 _
      ⟨w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44⟩
      ⟨w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45⟩
      ⟨a_29, b_29, c_29, d_29, e_29, f_29, g_29, h_29⟩
      ⟨a_30, b_30, c_30, d_30, e_30, f_30, g_30, h_30⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x06ca6351 _
      ⟨w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45⟩
      ⟨w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46⟩
      ⟨a_30, b_30, c_30, d_30, e_30, f_30, g_30, h_30⟩
      ⟨a_31, b_31, c_31, d_31, e_31, f_31, g_31, h_31⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x14292967 _
      ⟨w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46⟩
      ⟨w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47⟩
      ⟨a_31, b_31, c_31, d_31, e_31, f_31, g_31, h_31⟩
      ⟨a_32, b_32, c_32, d_32, e_32, f_32, g_32, h_32⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x27b70a85 _
      ⟨w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47⟩
      ⟨w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48⟩
      ⟨a_32, b_32, c_32, d_32, e_32, f_32, g_32, h_32⟩
      ⟨a_33, b_33, c_33, d_33, e_33, f_33, g_33, h_33⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x2e1b2138 _
      ⟨w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48⟩
      ⟨w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49⟩
      ⟨a_33, b_33, c_33, d_33, e_33, f_33, g_33, h_33⟩
      ⟨a_34, b_34, c_34, d_34, e_34, f_34, g_34, h_34⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x4d2c6dfc _
      ⟨w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49⟩
      ⟨w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50⟩
      ⟨a_34, b_34, c_34, d_34, e_34, f_34, g_34, h_34⟩
      ⟨a_35, b_35, c_35, d_35, e_35, f_35, g_35, h_35⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x53380d13 _
      ⟨w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50⟩
      ⟨w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51⟩
      ⟨a_35, b_35, c_35, d_35, e_35, f_35, g_35, h_35⟩
      ⟨a_36, b_36, c_36, d_36, e_36, f_36, g_36, h_36⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x650a7354 _
      ⟨w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51⟩
      ⟨w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52⟩
      ⟨a_36, b_36, c_36, d_36, e_36, f_36, g_36, h_36⟩
      ⟨a_37, b_37, c_37, d_37, e_37, f_37, g_37, h_37⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x766a0abb _
      ⟨w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52⟩
      ⟨w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53⟩
      ⟨a_37, b_37, c_37, d_37, e_37, f_37, g_37, h_37⟩
      ⟨a_38, b_38, c_38, d_38, e_38, f_38, g_38, h_38⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x81c2c92e _
      ⟨w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53⟩
      ⟨w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54⟩
      ⟨a_38, b_38, c_38, d_38, e_38, f_38, g_38, h_38⟩
      ⟨a_39, b_39, c_39, d_39, e_39, f_39, g_39, h_39⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x92722c85 _
      ⟨w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54⟩
      ⟨w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55⟩
      ⟨a_39, b_39, c_39, d_39, e_39, f_39, g_39, h_39⟩
      ⟨a_40, b_40, c_40, d_40, e_40, f_40, g_40, h_40⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xa2bfe8a1 _
      ⟨w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55⟩
      ⟨w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56⟩
      ⟨a_40, b_40, c_40, d_40, e_40, f_40, g_40, h_40⟩
      ⟨a_41, b_41, c_41, d_41, e_41, f_41, g_41, h_41⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xa81a664b _
      ⟨w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56⟩
      ⟨w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57⟩
      ⟨a_41, b_41, c_41, d_41, e_41, f_41, g_41, h_41⟩
      ⟨a_42, b_42, c_42, d_42, e_42, f_42, g_42, h_42⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xc24b8b70 _
      ⟨w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57⟩
      ⟨w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58⟩
      ⟨a_42, b_42, c_42, d_42, e_42, f_42, g_42, h_42⟩
      ⟨a_43, b_43, c_43, d_43, e_43, f_43, g_43, h_43⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xc76c51a3 _
      ⟨w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58⟩
      ⟨w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59⟩
      ⟨a_43, b_43, c_43, d_43, e_43, f_43, g_43, h_43⟩
      ⟨a_44, b_44, c_44, d_44, e_44, f_44, g_44, h_44⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xd192e819 _
      ⟨w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59⟩
      ⟨w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60⟩
      ⟨a_44, b_44, c_44, d_44, e_44, f_44, g_44, h_44⟩
      ⟨a_45, b_45, c_45, d_45, e_45, f_45, g_45, h_45⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xd6990624 _
      ⟨w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60⟩
      ⟨w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61⟩
      ⟨a_45, b_45, c_45, d_45, e_45, f_45, g_45, h_45⟩
      ⟨a_46, b_46, c_46, d_46, e_46, f_46, g_46, h_46⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xf40e3585 _
      ⟨w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61⟩
      ⟨w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62⟩
      ⟨a_46, b_46, c_46, d_46, e_46, f_46, g_46, h_46⟩
      ⟨a_47, b_47, c_47, d_47, e_47, f_47, g_47, h_47⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x106aa070 _
      ⟨w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62⟩
      ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩
      ⟨a_47, b_47, c_47, d_47, e_47, f_47, g_47, h_47⟩
      ⟨a_48, b_48, c_48, d_48, e_48, f_48, g_48, h_48⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x19a4c116 _
      ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩
      (windowAfter 1
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_48, b_48, c_48, d_48, e_48, f_48, g_48, h_48⟩
      ⟨a_49, b_49, c_49, d_49, e_49, f_49, g_49, h_49⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x1e376c08 _
      (windowAfter 1
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 2
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_49, b_49, c_49, d_49, e_49, f_49, g_49, h_49⟩
      ⟨a_50, b_50, c_50, d_50, e_50, f_50, g_50, h_50⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x2748774c _
      (windowAfter 2
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 3
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_50, b_50, c_50, d_50, e_50, f_50, g_50, h_50⟩
      ⟨a_51, b_51, c_51, d_51, e_51, f_51, g_51, h_51⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x34b0bcb5 _
      (windowAfter 3
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 4
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_51, b_51, c_51, d_51, e_51, f_51, g_51, h_51⟩
      ⟨a_52, b_52, c_52, d_52, e_52, f_52, g_52, h_52⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x391c0cb3 _
      (windowAfter 4
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 5
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_52, b_52, c_52, d_52, e_52, f_52, g_52, h_52⟩
      ⟨a_53, b_53, c_53, d_53, e_53, f_53, g_53, h_53⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x4ed8aa4a _
      (windowAfter 5
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 6
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_53, b_53, c_53, d_53, e_53, f_53, g_53, h_53⟩
      ⟨a_54, b_54, c_54, d_54, e_54, f_54, g_54, h_54⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x5b9cca4f _
      (windowAfter 6
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 7
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_54, b_54, c_54, d_54, e_54, f_54, g_54, h_54⟩
      ⟨a_55, b_55, c_55, d_55, e_55, f_55, g_55, h_55⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x682e6ff3 _
      (windowAfter 7
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 8
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_55, b_55, c_55, d_55, e_55, f_55, g_55, h_55⟩
      ⟨a_56, b_56, c_56, d_56, e_56, f_56, g_56, h_56⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x748f82ee _
      (windowAfter 8
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 9
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_56, b_56, c_56, d_56, e_56, f_56, g_56, h_56⟩
      ⟨a_57, b_57, c_57, d_57, e_57, f_57, g_57, h_57⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x78a5636f _
      (windowAfter 9
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 10
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_57, b_57, c_57, d_57, e_57, f_57, g_57, h_57⟩
      ⟨a_58, b_58, c_58, d_58, e_58, f_58, g_58, h_58⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x84c87814 _
      (windowAfter 10
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 11
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_58, b_58, c_58, d_58, e_58, f_58, g_58, h_58⟩
      ⟨a_59, b_59, c_59, d_59, e_59, f_59, g_59, h_59⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x8cc70208 _
      (windowAfter 11
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 12
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_59, b_59, c_59, d_59, e_59, f_59, g_59, h_59⟩
      ⟨a_60, b_60, c_60, d_60, e_60, f_60, g_60, h_60⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0x90befffa _
      (windowAfter 12
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 13
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_60, b_60, c_60, d_60, e_60, f_60, g_60, h_60⟩
      ⟨a_61, b_61, c_61, d_61, e_61, f_61, g_61, h_61⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xa4506ceb _
      (windowAfter 13
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 14
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_61, b_61, c_61, d_61, e_61, f_61, g_61, h_61⟩
      ⟨a_62, b_62, c_62, d_62, e_62, f_62, g_62, h_62⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xbef9a3f7 _
      (windowAfter 14
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 15
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_62, b_62, c_62, d_62, e_62, f_62, g_62, h_62⟩
      ⟨a_63, b_63, c_63, d_63, e_63, f_63, g_63, h_63⟩ rfl rfl) ?_
    refine Eq.trans (rounds_step 0xc67178f2 _
      (windowAfter 15
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      (windowAfter 16
        ⟨w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63⟩)
      ⟨a_63, b_63, c_63, d_63, e_63, f_63, g_63, h_63⟩
      ⟨a_64, b_64, c_64, d_64, e_64, f_64, g_64, h_64⟩ rfl rfl) ?_
    rfl
  rw [Sha256.compress, hR]
  rfl

/-! ### Driver, padding and output -/

/-- The fast driver runs the spec's chain of compressions over the same blocks. -/
theorem hashGo_eq (buf : ByteArray) (n : Nat) : ∀ (H : Sha256Fast.St) (off : Nat)
    (whole : off + 64 * n ≤ buf.size),
    toState (Sha256Fast.hashGo buf H off n) =
      Sha256.chain Sha256.compress buf n off whole (toState H) := by
  induction n with
  | zero => intro H off _; rfl
  | succ n ih =>
    intro H off whole
    unfold Sha256Fast.hashGo
    split
    · rw [Sha256.chain, ← compress_eq H buf off (by omega)]
      exact ih _ _ _
    · omega

/-- The zero run is one bulk copy of `n ≤ 64` zero bytes. -/
theorem padZero_data (b : ByteArray) (n : Nat) (hn : n ≤ 64) :
    (Sha256Fast.padZero b n).data = b.data ++ Array.replicate n 0 := by
  unfold Sha256Fast.padZero ByteArray.copySlice
  have e1 : b.data.extract 0 b.size = b.data := by
    rw [← ByteArray.size_data]; exact Array.extract_size
  have e3 : Sha256Fast.zeros64.data.extract 0 n = Array.replicate n 0 := by
    show (Array.replicate 64 (0:UInt8)).extract 0 n = _
    rw [Array.extract_replicate]; congr 1; omega
  have e4 :
      b.data.extract (b.size + min n (Sha256Fast.zeros64.data.size - 0)) b.data.size = #[] := by
    apply Array.extract_eq_empty_of_le
    rw [ByteArray.size_data]; omega
  show b.data.extract 0 b.size ++ Sha256Fast.zeros64.data.extract 0 (0 + n) ++
    b.data.extract (b.size + min n (Sha256Fast.zeros64.data.size - 0)) b.data.size = _
  rw [e1, Nat.zero_add, e3, e4]; simp

/-- The spec's eight length bytes, in the form the fast code pushes them. -/
theorem lengthBytes_data (size : Nat) : (Sha256.lengthBytes size).data =
    #[UInt8.ofNat (UInt64.ofNat (size * 8) >>> 56).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 48).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 40).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 32).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 24).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 16).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8) >>> 8).toNat,
      UInt8.ofNat (UInt64.ofNat (size * 8)).toNat] := by
  have bits : UInt64.ofNat size * 8 = UInt64.ofNat (size * 8) := by
    simp [UInt64.ofNat_mul]
  simp only [Sha256.lengthBytes, bits]
  apply Array.toList_inj.mp
  simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, Fin.val_succ, Fin.val_zero]
  rfl

/-- The fast padding is the spec's, for every message. -/
theorem padded_eq (msg : ByteArray) : Sha256Fast.padded msg = Sha256.pad msg := by
  have zeros : (56 + 64 - ((msg.size + 1) % 64)) % 64 = Sha256.paddingZeros msg.size := by
    unfold Sha256.paddingZeros; omega
  have small : Sha256.paddingZeros msg.size ≤ 64 :=
    Nat.le_of_lt (Nat.mod_lt _ (by decide) : Sha256.paddingZeros msg.size < 64)
  apply ByteArray.ext
  simp only [Sha256Fast.padded, Sha256Fast.pushLen, Sha256.pad, ByteArray.data_push,
    ByteArray.data_append, zeros, padZero_data _ _ small, lengthBytes_data]
  apply Array.toList_inj.mp
  simp

/-- The fast output packing is the spec's digest. -/
theorem pack_eq (H : Sha256Fast.St) :
    Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE
      (Sha256Fast.pushBE (Sha256Fast.pushBE (Sha256Fast.pushBE (ByteArray.emptyWithCapacity 32)
        H.a) H.b) H.c) H.d) H.e) H.f) H.g) H.h = Sha256.digest (toState H) := by
  apply ByteArray.ext
  simp only [Sha256Fast.pushBE, ByteArray.data_push, Sha256.digest, Sha256.byteAt, toState,
    UInt32.shiftRight_zero]
  have empty : (ByteArray.emptyWithCapacity 32).data = #[] := rfl
  rw [empty]
  simp

/-- The fast SHA-256 is the spec's, on every message. -/
theorem _root_.EthLibImpl.Cryptography.Bls.Sha256Fast.hash_eq (msg : ByteArray) :
    Sha256Fast.hash msg = EthLib.Cryptography.Hash.Sha256.hash msg := by
  unfold Sha256Fast.hash Sha256.hash
  simp only []
  rw [pack_eq, padded_eq,
    hashGo_eq _ _ _ 0 (by have := Nat.mul_div_le (Sha256.pad msg).size 64; omega)]
  rfl

end EthLibImpl.Cryptography.Proofs.Sha256Fast
