import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm
import Surreal.CommGroup
import Surreal.NewProof

namespace Game

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y

/-
  Strategy:
  1. Use wf_T induction on the triple (a,b,c).
  2. Prove equivalence by `Game.eq_of_equiv_options`.
  3. Match left/right options of `((a ⊗ b) ⊗ c)` with left/right options of `a ⊗ (b ⊗ c)`.
  4. Reduce each branch to one algebraic rewrite lemma on `mulOpt4`.
  5. In that rewrite lemma, use:
       - `conway_B` for multiplicative congruence,
       - `mul_distrib`, `mul_distrib_right`,
       - quotient-additive normalization (`GameQ` + `abel`).
-/

/-! ### Small wrappers -/

private def AssocPred (a b c : Game) : Prop :=
  ((a ⊗ b) ⊗ c) ∼ (a ⊗ (b ⊗ c))

private lemma mul_congr_right
    {x₁ x₂ y : Game}
    (sx₁ : IsSurreal x₁) (sx₂ : IsSurreal x₂) (sy : IsSurreal y)
    (h : x₁ ∼ x₂) :
    (x₁ ⊗ y) ∼ (x₂ ⊗ y) := by
  exact Conway.conway_B sx₁ sx₂ sy h

private lemma mul_congr_left
    {x y₁ y₂ : Game}
    (sx : IsSurreal x) (sy₁ : IsSurreal y₁) (sy₂ : IsSurreal y₂)
    (h : y₁ ∼ y₂) :
    (x ⊗ y₁) ∼ (x ⊗ y₂) := by
  exact Game.eq_trans ⟨Game.mul_comm,
    Game.eq_trans ⟨Conway.conway_B sy₁ sy₂ sx h, Game.mul_comm⟩⟩

lemma mul_congr
    {x₁ x₂ y₁ y₂ : Game}
    (sx₁ : IsSurreal x₁) (sx₂ : IsSurreal x₂)
    (sy₁ : IsSurreal y₁) (sy₂ : IsSurreal y₂)
    (hx : x₁ ∼ x₂) (hy : y₁ ∼ y₂) :
    (x₁ ⊗ y₁) ∼ (x₂ ⊗ y₂) := by
  exact Game.eq_trans ⟨mul_congr_right sx₁ sx₂ sy₁ hx,
    mul_congr_left sx₂ sy₁ sy₂ hy⟩

private lemma mulOpt4_neg_right_aux
    {xOpt Y X yOpt : Game}
    (h₁ : (xOpt ⊗ Y.neg) ∼ (xOpt ⊗ Y).neg)
    (h₂ : (X ⊗ yOpt.neg) ∼ (X ⊗ yOpt).neg)
    (h₃ : (xOpt ⊗ yOpt.neg) ∼ (xOpt ⊗ yOpt).neg) :
    Game.mulOpt4 xOpt Y.neg X yOpt.neg ∼
      (Game.mulOpt4 xOpt Y X yOpt).neg := by
  refine Game.eq_of_q_eq ?_
  simp only [Game.q_mulOpt4, Game.q_neg]
  rw [Game.q_sound h₁, Game.q_sound h₂, Game.q_sound h₃]
  simp only [Game.q_neg]
  abel

private abbrev MulNegIH (x y : Game) : Prop :=
  ∀ z : Game.BiGame, Game.B z ⟨x, y⟩ →
    (z.a ⊗ z.b.neg) ∼ (z.a ⊗ z.b).neg

private lemma mulOpt4_neg_right_of_IH
    {x y xOpt yOpt : Game}
    (IH : MulNegIH x y)
    (hxOpt : xOpt ∈ x.left ∨ xOpt ∈ x.right)
    (hyOpt : yOpt ∈ y.left ∨ yOpt ∈ y.right) :
    Game.mulOpt4 xOpt y.neg x yOpt.neg ∼
      (Game.mulOpt4 xOpt y x yOpt).neg := by
  exact mulOpt4_neg_right_aux
    (IH ⟨xOpt, y⟩ (Game.B_of_mem_option_fst hxOpt))
    (IH ⟨x, yOpt⟩ (Game.B_of_mem_option_snd hyOpt))
    (IH ⟨xOpt, yOpt⟩ (Game.B_of_mem_options hxOpt hyOpt))

private lemma Game.mul_neg {x y : Game} :
    (x ⊗ y.neg) ∼ (x ⊗ y).neg := by
  let P : Game.BiGame → Prop :=
    fun z => (z.a ⊗ z.b.neg) ∼ (z.a ⊗ z.b).neg
  have hP : ∀ z : Game.BiGame, P z := by
    intro z
    refine Game.wf_B.induction (C := P) z ?_
    rintro ⟨x, y⟩ IH
    dsimp [P]
    change MulNegIH x y at IH
    refine Game.eq_of_equiv_options ?_ ?_ ?_ ?_
    · intro L hL
      rw [mem_mul_left] at hL
      rcases hL with
        ⟨xL, hxL, ynL, hynL, rfl⟩ | ⟨xR, hxR, ynR, hynR, rfl⟩
      · rcases (mem_neg_left_iff.mp hynL) with ⟨yR, hyR, rfl⟩
        refine
          ⟨(Game.mulOpt4 xL y x yR).neg,
            mem_neg_left_of_right (mem_mul_right_lr hxL hyR), ?_⟩
        exact mulOpt4_neg_right_of_IH IH (Or.inl hxL) (Or.inr hyR)
      · rcases (mem_neg_right_iff.mp hynR) with ⟨yL, hyL, rfl⟩
        refine
          ⟨(Game.mulOpt4 xR y x yL).neg,
            mem_neg_left_of_right (mem_mul_right_rl hxR hyL), ?_⟩
        exact mulOpt4_neg_right_of_IH IH (Or.inr hxR) (Or.inl hyL)
    · intro L hL
      rw [mem_neg_left_iff] at hL
      rcases hL with ⟨R, hR, rfl⟩
      rw [mem_mul_right] at hR
      rcases hR with
        ⟨xL, hxL, yR, hyR, rfl⟩ | ⟨xR, hxR, yL, hyL, rfl⟩
      · refine
          ⟨Game.mulOpt4 xL y.neg x yR.neg,
            mem_mul_left_ll hxL (mem_neg_left_of_right hyR), ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_of_IH IH (Or.inl hxL) (Or.inr hyR)
      · refine
          ⟨Game.mulOpt4 xR y.neg x yL.neg,
            mem_mul_left_rr hxR (mem_neg_right_of_left hyL), ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_of_IH IH (Or.inr hxR) (Or.inl hyL)
    · intro R hR
      rw [mem_mul_right] at hR
      rcases hR with
        ⟨xL, hxL, ynR, hynR, rfl⟩ | ⟨xR, hxR, ynL, hynL, rfl⟩
      · rcases (mem_neg_right_iff.mp hynR) with ⟨yL, hyL, rfl⟩
        refine
          ⟨(Game.mulOpt4 xL y x yL).neg,
            mem_neg_right_of_left (mem_mul_left_ll hxL hyL), ?_⟩
        exact mulOpt4_neg_right_of_IH IH (Or.inl hxL) (Or.inl hyL)
      · rcases (mem_neg_left_iff.mp hynL) with ⟨yR, hyR, rfl⟩
        refine
          ⟨(Game.mulOpt4 xR y x yR).neg,
            mem_neg_right_of_left (mem_mul_left_rr hxR hyR), ?_⟩
        exact mulOpt4_neg_right_of_IH IH (Or.inr hxR) (Or.inr hyR)
    · intro R hR
      rw [mem_neg_right_iff] at hR
      rcases hR with ⟨L, hL, rfl⟩
      rw [mem_mul_left] at hL
      rcases hL with
        ⟨xL, hxL, yL, hyL, rfl⟩ | ⟨xR, hxR, yR, hyR, rfl⟩
      · refine
          ⟨Game.mulOpt4 xL y.neg x yL.neg,
            mem_mul_right_lr hxL (mem_neg_right_of_left hyL), ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_of_IH IH (Or.inl hxL) (Or.inl hyL)
      · refine
          ⟨Game.mulOpt4 xR y.neg x yR.neg,
            mem_mul_right_rl hxR (mem_neg_left_of_right hyR), ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_of_IH IH (Or.inr hxR) (Or.inr hyR)
  exact hP ⟨x, y⟩

private lemma neg_mul_from_mul_neg {x y : Game} :
    (x.neg ⊗ y) ∼ (x ⊗ y).neg := by
  exact Game.eq_trans ⟨Game.mul_comm,
    Game.eq_trans ⟨Game.mul_neg, Game.neg_congr_left Game.mul_comm⟩⟩

private lemma q_mulOpt4_mul_right
    {xOpt Y X yOpt z A B C : Game}
    (h₁ : ((xOpt ⊗ Y) ⊗ z) ∼ A)
    (h₂ : ((X ⊗ yOpt) ⊗ z) ∼ B)
    (h₃ : ((xOpt ⊗ yOpt) ⊗ z) ∼ C) :
    (Game.q ((Game.mulOpt4 xOpt Y X yOpt) ⊗ z) : Game.GameQ) =
      Game.q A + Game.q B - Game.q C := by
  dsimp [Game.mulOpt4]
  rw [Game.q_sound (Game.mul_distrib_right
    (a := (xOpt ⊗ Y) ⊕ (X ⊗ yOpt)) (b := (xOpt ⊗ yOpt).neg) (c := z))]
  simp only [Game.q_add]
  rw [Game.q_sound (Game.mul_distrib_right
    (a := xOpt ⊗ Y) (b := X ⊗ yOpt) (c := z))]
  simp only [Game.q_add]
  rw [Game.q_sound (neg_mul_from_mul_neg (x := xOpt ⊗ yOpt) (y := z))]
  simp only [Game.q_neg]
  rw [Game.q_sound h₁, Game.q_sound h₂, Game.q_sound h₃]
  abel

private lemma q_mul_mulOpt4
    (x xOpt Y X yOpt : Game) :
    (Game.q (x ⊗ Game.mulOpt4 xOpt Y X yOpt) : Game.GameQ) =
      Game.q (x ⊗ (xOpt ⊗ Y)) +
        Game.q (x ⊗ (X ⊗ yOpt)) -
          Game.q (x ⊗ (xOpt ⊗ yOpt)) := by
  dsimp [Game.mulOpt4]
  rw [Game.q_sound (Game.mul_distrib
    (a := x) (b := (xOpt ⊗ Y) ⊕ (X ⊗ yOpt)) (c := (xOpt ⊗ yOpt).neg))]
  simp only [Game.q_add]
  rw [Game.q_sound (Game.mul_distrib
    (a := x) (b := xOpt ⊗ Y) (c := X ⊗ yOpt))]
  simp only [Game.q_add]
  rw [Game.q_sound Game.mul_neg]
  simp only [Game.q_neg]
  abel

private lemma mulOpt4_assoc_rewrite
    {a b c a₀ b₀ c₀ : Game}
    (h₁ : ((a₀ ⊗ b) ⊗ c) ∼ (a₀ ⊗ (b ⊗ c)))
    (h₂ : ((a ⊗ b₀) ⊗ c) ∼ (a ⊗ (b₀ ⊗ c)))
    (h₃ : ((a₀ ⊗ b₀) ⊗ c) ∼ (a₀ ⊗ (b₀ ⊗ c)))
    (h₄ : ((a ⊗ b) ⊗ c₀) ∼ (a ⊗ (b ⊗ c₀)))
    (h₅ : ((a₀ ⊗ b) ⊗ c₀) ∼ (a₀ ⊗ (b ⊗ c₀)))
    (h₆ : ((a ⊗ b₀) ⊗ c₀) ∼ (a ⊗ (b₀ ⊗ c₀)))
    (h₇ : ((a₀ ⊗ b₀) ⊗ c₀) ∼ (a₀ ⊗ (b₀ ⊗ c₀))) :
    Game.mulOpt4 (Game.mulOpt4 a₀ b a b₀) c (a ⊗ b) c₀ ∼
    Game.mulOpt4 a₀ (b ⊗ c) a (Game.mulOpt4 b₀ c b c₀) := by
  refine Game.eq_of_q_eq ?_
  simp only [Game.q_mulOpt4]
  rw [q_mulOpt4_mul_right h₁ h₂ h₃, Game.q_sound h₄,
    q_mulOpt4_mul_right h₅ h₆ h₇, q_mul_mulOpt4, q_mul_mulOpt4]
  abel

private structure AssocContext (a b c : Game) : Prop where
  sa : IsSurreal a
  sb : IsSurreal b
  sc : IsSurreal c
  ih : ∀ t, T t ⟨a, b, c⟩ →
    IsSurreal t.a → IsSurreal t.b → IsSurreal t.c → AssocPred t.a t.b t.c

private lemma AssocContext.mulOpt4_assoc
    {a b c a₀ b₀ c₀ : Game}
    (ctx : AssocContext a b c)
    (ha₀ : a₀ ∈ a.left ∨ a₀ ∈ a.right)
    (hb₀ : b₀ ∈ b.left ∨ b₀ ∈ b.right)
    (hc₀ : c₀ ∈ c.left ∨ c₀ ∈ c.right) :
    Game.mulOpt4 (Game.mulOpt4 a₀ b a b₀) c (a ⊗ b) c₀ ∼
      Game.mulOpt4 a₀ (b ⊗ c) a (Game.mulOpt4 b₀ c b c₀) := by
  have ha₀' := Game.birthday_lt_of_isOption ha₀
  have hb₀' := Game.birthday_lt_of_isOption hb₀
  have hc₀' := Game.birthday_lt_of_isOption hc₀
  have sa₀ := IsSurreal.isSurreal_option ctx.sa ha₀
  have sb₀ := IsSurreal.isSurreal_option ctx.sb hb₀
  have sc₀ := IsSurreal.isSurreal_option ctx.sc hc₀
  exact mulOpt4_assoc_rewrite
    (h₁ := ctx.ih ⟨a₀, b, c⟩ (Game.T_left ha₀') sa₀ ctx.sb ctx.sc)
    (h₂ := ctx.ih ⟨a, b₀, c⟩ (Game.T_mid hb₀') ctx.sa sb₀ ctx.sc)
    (h₃ := ctx.ih ⟨a₀, b₀, c⟩ (Game.T_left_mid ha₀' hb₀') sa₀ sb₀ ctx.sc)
    (h₄ := ctx.ih ⟨a, b, c₀⟩ (Game.T_right hc₀') ctx.sa ctx.sb sc₀)
    (h₅ := ctx.ih ⟨a₀, b, c₀⟩ (Game.T_left_right ha₀' hc₀') sa₀ ctx.sb sc₀)
    (h₆ := ctx.ih ⟨a, b₀, c₀⟩ (Game.T_mid_right hb₀' hc₀') ctx.sa sb₀ sc₀)
    (h₇ := ctx.ih ⟨a₀, b₀, c₀⟩ (Game.T_left_mid_right ha₀' hb₀' hc₀') sa₀ sb₀ sc₀)

/-! ### Option-matching lemmas -/

private lemma left_option_mul_assoc
    {a b c : Game}
    (ctx : AssocContext a b c)
    {L : Game} (hL : L ∈ ((a ⊗ b) ⊗ c).left) :
    ∃ L' ∈ (a ⊗ (b ⊗ c)).left, L ∼ L' := by
  rw [mem_mul_left] at hL
  rcases hL with
    ⟨abL, habL, cL, hcL, rfl⟩ | ⟨abR, habR, cR, hcR, rfl⟩
  · rw [mem_mul_left] at habL
    rcases habL with
      ⟨aL, haL, bL, hbL, rfl⟩ | ⟨aR, haR, bR, hbR, rfl⟩
    · -- branch (aL, bL, cL)
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a (Game.mulOpt4 bL c b cL),
        mem_mul_left_ll haL (mem_mul_left_ll hbL hcL), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inl haL) (Or.inl hbL) (Or.inl hcL)
    · -- branch (aR, bR, cL)
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a (Game.mulOpt4 bR c b cL),
        mem_mul_left_rr haR (mem_mul_right_rl hbR hcL), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inr haR) (Or.inr hbR) (Or.inl hcL)
  · rw [mem_mul_right] at habR
    rcases habR with
      ⟨aL, haL, bR, hbR, rfl⟩ | ⟨aR, haR, bL, hbL, rfl⟩
    · -- branch (aL, bR, cR)
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a (Game.mulOpt4 bR c b cR),
        mem_mul_left_ll haL (mem_mul_left_rr hbR hcR), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inl haL) (Or.inr hbR) (Or.inr hcR)
    · -- branch (aR, bL, cR)
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a (Game.mulOpt4 bL c b cR),
        mem_mul_left_rr haR (mem_mul_right_lr hbL hcR), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inr haR) (Or.inl hbL) (Or.inr hcR)

private lemma left_option_mul_assoc_symm
    {a b c : Game}
    (ctx : AssocContext a b c)
    {L : Game} (hL : L ∈ (a ⊗ (b ⊗ c)).left) :
    ∃ L' ∈ ((a ⊗ b) ⊗ c).left, L ∼ L' := by
  rw [mem_mul_left] at hL
  rcases hL with
    ⟨aL, haL, bcL, hbcL, rfl⟩ | ⟨aR, haR, bcR, hbcR, rfl⟩
  · rw [mem_mul_left] at hbcL
    rcases hbcL with
      ⟨bL, hbL, cL, hcL, rfl⟩ | ⟨bR, hbR, cR, hcR, rfl⟩
    · -- branch (aL, bL, cL)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aL b a bL) c (a ⊗ b) cL,
        mem_mul_left_ll (mem_mul_left_ll haL hbL) hcL, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inl haL) (Or.inl hbL) (Or.inl hcL)
    · -- branch (aL, bR, cR)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aL b a bR) c (a ⊗ b) cR,
        mem_mul_left_rr (mem_mul_right_lr haL hbR) hcR, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inl haL) (Or.inr hbR) (Or.inr hcR)
  · rw [mem_mul_right] at hbcR
    rcases hbcR with
      ⟨bL, hbL, cR, hcR, rfl⟩ | ⟨bR, hbR, cL, hcL, rfl⟩
    · -- branch (aR, bL, cR)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aR b a bL) c (a ⊗ b) cR,
        mem_mul_left_rr (mem_mul_right_rl haR hbL) hcR, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inr haR) (Or.inl hbL) (Or.inr hcR)
    · -- branch (aR, bR, cL)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aR b a bR) c (a ⊗ b) cL,
        mem_mul_left_ll (mem_mul_left_rr haR hbR) hcL, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inr haR) (Or.inr hbR) (Or.inl hcL)

private lemma right_option_mul_assoc
    {a b c : Game}
    (ctx : AssocContext a b c)
    {R : Game} (hR : R ∈ ((a ⊗ b) ⊗ c).right) :
    ∃ R' ∈ (a ⊗ (b ⊗ c)).right, R ∼ R' := by
  rw [mem_mul_right] at hR
  rcases hR with
    ⟨abL, habL, cR, hcR, rfl⟩ | ⟨abR, habR, cL, hcL, rfl⟩
  · rw [mem_mul_left] at habL
    rcases habL with
      ⟨aL, haL, bL, hbL, rfl⟩ | ⟨aR, haR, bR, hbR, rfl⟩
    · -- branch (aL, bL, cR)
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a (Game.mulOpt4 bL c b cR),
        mem_mul_right_lr haL (mem_mul_right_lr hbL hcR), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inl haL) (Or.inl hbL) (Or.inr hcR)
    · -- branch (aR, bR, cR)
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a (Game.mulOpt4 bR c b cR),
        mem_mul_right_rl haR (mem_mul_left_rr hbR hcR), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inr haR) (Or.inr hbR) (Or.inr hcR)
  · rw [mem_mul_right] at habR
    rcases habR with
      ⟨aL, haL, bR, hbR, rfl⟩ | ⟨aR, haR, bL, hbL, rfl⟩
    · -- branch (aL, bR, cL)
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a (Game.mulOpt4 bR c b cL),
        mem_mul_right_lr haL (mem_mul_right_rl hbR hcL), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inl haL) (Or.inr hbR) (Or.inl hcL)
    · -- branch (aR, bL, cL)
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a (Game.mulOpt4 bL c b cL),
        mem_mul_right_rl haR (mem_mul_left_ll hbL hcL), ?_⟩
      exact ctx.mulOpt4_assoc (Or.inr haR) (Or.inl hbL) (Or.inl hcL)

private lemma right_option_mul_assoc_symm
    {a b c : Game}
    (ctx : AssocContext a b c)
    {R : Game} (hR : R ∈ (a ⊗ (b ⊗ c)).right) :
    ∃ R' ∈ ((a ⊗ b) ⊗ c).right, R ∼ R' := by
  rw [mem_mul_right] at hR
  rcases hR with
    ⟨aL, haL, bcR, hbcR, rfl⟩ | ⟨aR, haR, bcL, hbcL, rfl⟩
  · rw [mem_mul_right] at hbcR
    rcases hbcR with
      ⟨bL, hbL, cR, hcR, rfl⟩ | ⟨bR, hbR, cL, hcL, rfl⟩
    · -- branch (aL, bL, cR)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aL b a bL) c (a ⊗ b) cR,
        mem_mul_right_lr (mem_mul_left_ll haL hbL) hcR, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inl haL) (Or.inl hbL) (Or.inr hcR)
    · -- branch (aL, bR, cL)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aL b a bR) c (a ⊗ b) cL,
        mem_mul_right_rl (mem_mul_right_lr haL hbR) hcL, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inl haL) (Or.inr hbR) (Or.inl hcL)
  · rw [mem_mul_left] at hbcL
    rcases hbcL with
      ⟨bL, hbL, cL, hcL, rfl⟩ | ⟨bR, hbR, cR, hcR, rfl⟩
    · -- branch (aR, bL, cL)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aR b a bL) c (a ⊗ b) cL,
        mem_mul_right_rl (mem_mul_right_rl haR hbL) hcL, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inr haR) (Or.inl hbL) (Or.inl hcL)
    · -- branch (aR, bR, cR)
      refine ⟨Game.mulOpt4 (Game.mulOpt4 aR b a bR) c (a ⊗ b) cR,
        mem_mul_right_lr (mem_mul_left_rr haR hbR) hcR, ?_⟩
      exact Game.eq_symm <| ctx.mulOpt4_assoc (Or.inr haR) (Or.inr hbR) (Or.inr hcR)

/-! ### Main theorem -/

theorem mul_assoc_of_isSurreal
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c) :
    ((a ⊗ b) ⊗ c) ∼ (a ⊗ (b ⊗ c)) := by
  let t : TriGame := ⟨a, b, c⟩
  change AssocPred t.a t.b t.c
  refine wf_T.induction
    (C := fun t =>
      IsSurreal t.a → IsSurreal t.b → IsSurreal t.c → AssocPred t.a t.b t.c) t ?_ sa sb sc
  intro t IH sa sb sc
  rcases t with ⟨a, b, c⟩
  let ctx : AssocContext a b c := ⟨sa, sb, sc, IH⟩
  exact Game.eq_of_equiv_options
    (fun _ h => left_option_mul_assoc ctx h)
    (fun _ h => left_option_mul_assoc_symm ctx h)
    (fun _ h => right_option_mul_assoc ctx h)
    (fun _ h => right_option_mul_assoc_symm ctx h)

end Game
