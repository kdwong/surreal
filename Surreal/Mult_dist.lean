import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm
import Surreal.CommGroup

namespace Game

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y


/-! ### Quotient-algebra rewrites -/

private lemma mulOpt4_congr {xOpt Y X yOpt A B C : Game}
    (h₁ : (xOpt ⊗ Y) ∼ A) (h₂ : (X ⊗ yOpt) ∼ B) (h₃ : (xOpt ⊗ yOpt) ∼ C) :
    Game.mulOpt4 xOpt Y X yOpt ∼ ((A ⊕ B) ⊕ C.neg) := by
  dsimp [Game.mulOpt4]
  have h₁₂ : ((xOpt ⊗ Y) ⊕ (X ⊗ yOpt)) ∼ (A ⊕ B) := Game.add_equal ⟨h₁, h₂⟩
  have h₃' : (xOpt ⊗ yOpt).neg ∼ C.neg := (Game.neg_congr).mp (Game.eq_symm h₃)
  exact Game.add_equal ⟨h₁₂, h₃'⟩

private lemma distrib_q_b (p q r s t : Game) :
  ((((p ⊕ q) ⊕ (r ⊕ s)) ⊕ (t ⊕ q).neg) : Game) ∼ (((p ⊕ r) ⊕ t.neg) ⊕ s) := by
  refine Game.eq_of_q_eq ?_
  simp
  abel

private lemma distrib_q_c (p q r s t : Game) :
    ((((p ⊕ q) ⊕ (r ⊕ s)) ⊕ (p ⊕ t).neg) : Game) ∼
      (r ⊕ ((q ⊕ s) ⊕ t.neg)) := by
  refine Game.eq_of_q_eq ?_
  simp
  abel

private lemma mulOpt4_distrib_b {a b c a₀ b₀ : Game}
    (h₁ : (a₀ ⊗ (b ⊕ c)) ∼ (a₀ ⊗ b) ⊕ (a₀ ⊗ c))
    (h₂ : (a ⊗ (b₀ ⊕ c)) ∼ (a ⊗ b₀) ⊕ (a ⊗ c))
    (h₃ : (a₀ ⊗ (b₀ ⊕ c)) ∼ (a₀ ⊗ b₀) ⊕ (a₀ ⊗ c)) :
    Game.mulOpt4 a₀ (b ⊕ c) a (b₀ ⊕ c) ∼ (Game.mulOpt4 a₀ b a b₀ ⊕ (a ⊗ c)) := by
  have hrewrite :
      Game.mulOpt4 a₀ (b ⊕ c) a (b₀ ⊕ c) ∼
        ((((a₀ ⊗ b) ⊕ (a₀ ⊗ c)) ⊕ ((a ⊗ b₀) ⊕ (a ⊗ c))) ⊕
          (((a₀ ⊗ b₀) ⊕ (a₀ ⊗ c)).neg)) := by
    simpa [Game.mulOpt4] using mulOpt4_congr h₁ h₂ h₃
  refine Game.eq_trans ⟨hrewrite, ?_⟩
  simpa [Game.mulOpt4] using
    distrib_q_b (p := a₀ ⊗ b) (q := a₀ ⊗ c) (r := a ⊗ b₀)
      (s := a ⊗ c) (t := a₀ ⊗ b₀)

private lemma mulOpt4_distrib_c {a b c a₀ c₀ : Game}
    (h₁ : (a₀ ⊗ (b ⊕ c)) ∼ (a₀ ⊗ b) ⊕ (a₀ ⊗ c))
    (h₂ : (a ⊗ (b ⊕ c₀)) ∼ (a ⊗ b) ⊕ (a ⊗ c₀))
    (h₃ : (a₀ ⊗ (b ⊕ c₀)) ∼ (a₀ ⊗ b) ⊕ (a₀ ⊗ c₀)) :
    Game.mulOpt4 a₀ (b ⊕ c) a (b ⊕ c₀) ∼ ((a ⊗ b) ⊕ Game.mulOpt4 a₀ c a c₀) := by
  have hrewrite :
      Game.mulOpt4 a₀ (b ⊕ c) a (b ⊕ c₀) ∼
        ((((a₀ ⊗ b) ⊕ (a₀ ⊗ c)) ⊕ ((a ⊗ b) ⊕ (a ⊗ c₀))) ⊕
          (((a₀ ⊗ b) ⊕ (a₀ ⊗ c₀)).neg)) := by
    simpa [Game.mulOpt4] using mulOpt4_congr h₁ h₂ h₃
  refine Game.eq_trans ⟨hrewrite, ?_⟩
  simpa [Game.mulOpt4] using
    distrib_q_c (p := a₀ ⊗ b) (q := a₀ ⊗ c) (r := a ⊗ b)
      (s := a ⊗ c₀) (t := a₀ ⊗ c₀)

/-! ### Matching left and right options -/

private lemma left_option_mul_distrib {a b c L : Game}
    (IHa : ∀ a', birthday a' < birthday a → (a' ⊗ (b ⊕ c)) ∼ (a' ⊗ b) ⊕ (a' ⊗ c))
    (IHb : ∀ b', birthday b' < birthday b → (a ⊗ (b' ⊕ c)) ∼ (a ⊗ b') ⊕ (a ⊗ c))
    (IHc : ∀ c', birthday c' < birthday c → (a ⊗ (b ⊕ c')) ∼ (a ⊗ b) ⊕ (a ⊗ c'))
    (IHab : ∀ a' b', birthday a' < birthday a → birthday b' < birthday b →
      (a' ⊗ (b' ⊕ c)) ∼ (a' ⊗ b') ⊕ (a' ⊗ c))
    (IHac : ∀ a' c', birthday a' < birthday a → birthday c' < birthday c →
      (a' ⊗ (b ⊕ c')) ∼ (a' ⊗ b) ⊕ (a' ⊗ c'))
    (hL : L ∈ (a ⊗ (b ⊕ c)).left) : ∃ L' ∈ ((a ⊗ b) ⊕ (a ⊗ c)).left, L ∼ L' := by
  rw [mem_mul_left] at hL
  rcases hL with ⟨aL, haL, yL, hyL, rfl⟩ | ⟨aR, haR, yR, hyR, rfl⟩
  · rw [mem_add_left_iff] at hyL
    rcases hyL with ⟨bL, hbL, rfl⟩ | ⟨cL, hcL, rfl⟩
    · refine ⟨Game.mulOpt4 aL b a bL ⊕ (a ⊗ c), mem_add_left₁ (mem_mul_left_ll haL hbL), ?_⟩
      exact mulOpt4_distrib_b
        (IHa _ (birthday_lt_left haL))
        (IHb _ (birthday_lt_left hbL))
        (IHab _ _ (birthday_lt_left haL) (birthday_lt_left hbL))
    · refine ⟨(a ⊗ b) ⊕ Game.mulOpt4 aL c a cL, mem_add_left₂ (mem_mul_left_ll haL hcL), ?_⟩
      exact mulOpt4_distrib_c
        (IHa _ (birthday_lt_left haL))
        (IHc _ (birthday_lt_left hcL))
        (IHac _ _ (birthday_lt_left haL) (birthday_lt_left hcL))
  · rw [mem_add_right_iff] at hyR
    rcases hyR with ⟨bR, hbR, rfl⟩ | ⟨cR, hcR, rfl⟩
    · refine ⟨Game.mulOpt4 aR b a bR ⊕ (a ⊗ c), mem_add_left₁ (mem_mul_left_rr haR hbR), ?_⟩
      exact mulOpt4_distrib_b
        (IHa _ (birthday_lt_right haR))
        (IHb _ (birthday_lt_right hbR))
        (IHab _ _ (birthday_lt_right haR) (birthday_lt_right hbR))
    · refine ⟨(a ⊗ b) ⊕ Game.mulOpt4 aR c a cR, mem_add_left₂ (mem_mul_left_rr haR hcR), ?_⟩
      exact mulOpt4_distrib_c
        (IHa _ (birthday_lt_right haR))
        (IHc _ (birthday_lt_right hcR))
        (IHac _ _ (birthday_lt_right haR) (birthday_lt_right hcR))

private lemma left_option_mul_distrib_symm {a b c L : Game}
    (IHa : ∀ a', birthday a' < birthday a → (a' ⊗ (b ⊕ c)) ∼ (a' ⊗ b) ⊕ (a' ⊗ c))
    (IHb : ∀ b', birthday b' < birthday b → (a ⊗ (b' ⊕ c)) ∼ (a ⊗ b') ⊕ (a ⊗ c))
    (IHc : ∀ c', birthday c' < birthday c → (a ⊗ (b ⊕ c')) ∼ (a ⊗ b) ⊕ (a ⊗ c'))
    (IHab : ∀ a' b', birthday a' < birthday a → birthday b' < birthday b →
      (a' ⊗ (b' ⊕ c)) ∼ (a' ⊗ b') ⊕ (a' ⊗ c))
    (IHac : ∀ a' c', birthday a' < birthday a → birthday c' < birthday c →
      (a' ⊗ (b ⊕ c')) ∼ (a' ⊗ b) ⊕ (a' ⊗ c'))
    (hL : L ∈ ((a ⊗ b) ⊕ (a ⊗ c)).left) : ∃ L' ∈ (a ⊗ (b ⊕ c)).left, L ∼ L' := by
  rw [mem_add_left_iff] at hL
  rcases hL with ⟨abL, habL, rfl⟩ | ⟨acL, hacL, rfl⟩
  · rw [mem_mul_left] at habL
    rcases habL with ⟨aL, haL, bL, hbL, rfl⟩ | ⟨aR, haR, bR, hbR, rfl⟩
    · refine ⟨Game.mulOpt4 aL (b ⊕ c) a (bL ⊕ c), mem_mul_left_ll haL (mem_add_left₁ hbL), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_b
        (IHa _ (birthday_lt_left haL))
        (IHb _ (birthday_lt_left hbL))
        (IHab _ _ (birthday_lt_left haL) (birthday_lt_left hbL))
    · refine ⟨Game.mulOpt4 aR (b ⊕ c) a (bR ⊕ c), mem_mul_left_rr haR (mem_add_right₁ hbR), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_b
        (IHa _ (birthday_lt_right haR))
        (IHb _ (birthday_lt_right hbR))
        (IHab _ _ (birthday_lt_right haR) (birthday_lt_right hbR))
  · rw [mem_mul_left] at hacL
    rcases hacL with ⟨aL, haL, cL, hcL, rfl⟩ | ⟨aR, haR, cR, hcR, rfl⟩
    · refine ⟨Game.mulOpt4 aL (b ⊕ c) a (b ⊕ cL), mem_mul_left_ll haL (mem_add_left₂ hcL), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_c
        (IHa _ (birthday_lt_left haL))
        (IHc _ (birthday_lt_left hcL))
        (IHac _ _ (birthday_lt_left haL) (birthday_lt_left hcL))
    · refine ⟨Game.mulOpt4 aR (b ⊕ c) a (b ⊕ cR), mem_mul_left_rr haR (mem_add_right₂ hcR), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_c
        (IHa _ (birthday_lt_right haR))
        (IHc _ (birthday_lt_right hcR))
        (IHac _ _ (birthday_lt_right haR) (birthday_lt_right hcR))

private lemma right_option_mul_distrib {a b c R : Game}
    (IHa : ∀ a', birthday a' < birthday a → (a' ⊗ (b ⊕ c)) ∼ (a' ⊗ b) ⊕ (a' ⊗ c))
    (IHb : ∀ b', birthday b' < birthday b → (a ⊗ (b' ⊕ c)) ∼ (a ⊗ b') ⊕ (a ⊗ c))
    (IHc : ∀ c', birthday c' < birthday c → (a ⊗ (b ⊕ c')) ∼ (a ⊗ b) ⊕ (a ⊗ c'))
    (IHab : ∀ a' b', birthday a' < birthday a → birthday b' < birthday b →
      (a' ⊗ (b' ⊕ c)) ∼ (a' ⊗ b') ⊕ (a' ⊗ c))
    (IHac : ∀ a' c', birthday a' < birthday a → birthday c' < birthday c →
      (a' ⊗ (b ⊕ c')) ∼ (a' ⊗ b) ⊕ (a' ⊗ c'))
    (hR : R ∈ (a ⊗ (b ⊕ c)).right) : ∃ R' ∈ ((a ⊗ b) ⊕ (a ⊗ c)).right, R ∼ R' := by
  rw [mem_mul_right] at hR
  rcases hR with ⟨aL, haL, yR, hyR, rfl⟩ | ⟨aR, haR, yL, hyL, rfl⟩
  · rw [mem_add_right_iff] at hyR
    rcases hyR with ⟨bR, hbR, rfl⟩ | ⟨cR, hcR, rfl⟩
    · refine ⟨Game.mulOpt4 aL b a bR ⊕ (a ⊗ c), mem_add_right₁ (mem_mul_right_lr haL hbR), ?_⟩
      exact mulOpt4_distrib_b
        (IHa _ (birthday_lt_left haL))
        (IHb _ (birthday_lt_right hbR))
        (IHab _ _ (birthday_lt_left haL) (birthday_lt_right hbR))
    · refine ⟨(a ⊗ b) ⊕ Game.mulOpt4 aL c a cR, mem_add_right₂ (mem_mul_right_lr haL hcR), ?_⟩
      exact mulOpt4_distrib_c
        (IHa _ (birthday_lt_left haL))
        (IHc _ (birthday_lt_right hcR))
        (IHac _ _ (birthday_lt_left haL) (birthday_lt_right hcR))
  · rw [mem_add_left_iff] at hyL
    rcases hyL with ⟨bL, hbL, rfl⟩ | ⟨cL, hcL, rfl⟩
    · refine ⟨Game.mulOpt4 aR b a bL ⊕ (a ⊗ c), mem_add_right₁ (mem_mul_right_rl haR hbL), ?_⟩
      exact mulOpt4_distrib_b
        (IHa _ (birthday_lt_right haR))
        (IHb _ (birthday_lt_left hbL))
        (IHab _ _ (birthday_lt_right haR) (birthday_lt_left hbL))
    · refine ⟨(a ⊗ b) ⊕ Game.mulOpt4 aR c a cL, mem_add_right₂ (mem_mul_right_rl haR hcL), ?_⟩
      exact mulOpt4_distrib_c
        (IHa _ (birthday_lt_right haR))
        (IHc _ (birthday_lt_left hcL))
        (IHac _ _ (birthday_lt_right haR) (birthday_lt_left hcL))

private lemma right_option_mul_distrib_symm {a b c R : Game}
    (IHa : ∀ a', birthday a' < birthday a → (a' ⊗ (b ⊕ c)) ∼ (a' ⊗ b) ⊕ (a' ⊗ c))
    (IHb : ∀ b', birthday b' < birthday b → (a ⊗ (b' ⊕ c)) ∼ (a ⊗ b') ⊕ (a ⊗ c))
    (IHc : ∀ c', birthday c' < birthday c → (a ⊗ (b ⊕ c')) ∼ (a ⊗ b) ⊕ (a ⊗ c'))
    (IHab : ∀ a' b', birthday a' < birthday a → birthday b' < birthday b →
      (a' ⊗ (b' ⊕ c)) ∼ (a' ⊗ b') ⊕ (a' ⊗ c))
    (IHac : ∀ a' c', birthday a' < birthday a → birthday c' < birthday c →
      (a' ⊗ (b ⊕ c')) ∼ (a' ⊗ b) ⊕ (a' ⊗ c'))
    (hR : R ∈ ((a ⊗ b) ⊕ (a ⊗ c)).right) : ∃ R' ∈ (a ⊗ (b ⊕ c)).right, R ∼ R' := by
  rw [mem_add_right_iff] at hR
  rcases hR with ⟨abR, habR, rfl⟩ | ⟨acR, hacR, rfl⟩
  · rw [mem_mul_right] at habR
    rcases habR with ⟨aL, haL, bR, hbR, rfl⟩ | ⟨aR, haR, bL, hbL, rfl⟩
    · refine ⟨Game.mulOpt4 aL (b ⊕ c) a (bR ⊕ c), mem_mul_right_lr haL (mem_add_right₁ hbR), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_b
        (IHa _ (birthday_lt_left haL))
        (IHb _ (birthday_lt_right hbR))
        (IHab _ _ (birthday_lt_left haL) (birthday_lt_right hbR))
    · refine ⟨Game.mulOpt4 aR (b ⊕ c) a (bL ⊕ c), mem_mul_right_rl haR (mem_add_left₁ hbL), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_b
        (IHa _ (birthday_lt_right haR))
        (IHb _ (birthday_lt_left hbL))
        (IHab _ _ (birthday_lt_right haR) (birthday_lt_left hbL))
  · rw [mem_mul_right] at hacR
    rcases hacR with ⟨aL, haL, cR, hcR, rfl⟩ | ⟨aR, haR, cL, hcL, rfl⟩
    · refine ⟨Game.mulOpt4 aL (b ⊕ c) a (b ⊕ cR), mem_mul_right_lr haL (mem_add_right₂ hcR), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_c
        (IHa _ (birthday_lt_left haL))
        (IHc _ (birthday_lt_right hcR))
        (IHac _ _ (birthday_lt_left haL) (birthday_lt_right hcR))
    · refine ⟨Game.mulOpt4 aR (b ⊕ c) a (b ⊕ cL), mem_mul_right_rl haR (mem_add_left₂ hcL), ?_⟩
      exact Game.eq_symm <| mulOpt4_distrib_c
        (IHa _ (birthday_lt_right haR))
        (IHc _ (birthday_lt_left hcL))
        (IHac _ _ (birthday_lt_right haR) (birthday_lt_left hcL))

/-! ### Main distributivity proofs -/

theorem mul_distrib_tri (x : TriGame) :
    (x.a ⊗ (x.b ⊕ x.c)) ∼ ((x.a ⊗ x.b) ⊕ (x.a ⊗ x.c)) := by
  refine wf_T.induction
    (C := fun t : TriGame => (t.a ⊗ (t.b ⊕ t.c)) ∼ ((t.a ⊗ t.b) ⊕ (t.a ⊗ t.c))) x ?_
  rintro ⟨a, b, c⟩ IH
  have IH₃ {a' b' c' : Game} (hT : T ⟨a', b', c'⟩ ⟨a, b, c⟩) :
      (a' ⊗ (b' ⊕ c')) ∼ ((a' ⊗ b') ⊕ (a' ⊗ c')) := by
    simpa using IH ⟨a', b', c'⟩ hT
  have IHa : ∀ a', birthday a' < birthday a →
      (a' ⊗ (b ⊕ c)) ∼ ((a' ⊗ b) ⊕ (a' ⊗ c)) := by
    intro a' ha
    exact IH₃ (T_left ha)
  have IHb : ∀ b', birthday b' < birthday b →
      (a ⊗ (b' ⊕ c)) ∼ ((a ⊗ b') ⊕ (a ⊗ c)) := by
    intro b' hb
    exact IH₃ (T_mid hb)
  have IHc : ∀ c', birthday c' < birthday c →
      (a ⊗ (b ⊕ c')) ∼ ((a ⊗ b) ⊕ (a ⊗ c')) := by
    intro c' hc
    exact IH₃ (T_right hc)
  have IHab : ∀ a' b', birthday a' < birthday a → birthday b' < birthday b →
      (a' ⊗ (b' ⊕ c)) ∼ ((a' ⊗ b') ⊕ (a' ⊗ c)) := by
    intro a' b' ha hb
    exact IH₃ (T_left_mid ha hb)
  have IHac : ∀ a' c', birthday a' < birthday a → birthday c' < birthday c →
      (a' ⊗ (b ⊕ c')) ∼ ((a' ⊗ b) ⊕ (a' ⊗ c')) := by
    intro a' c' ha hc
    exact IH₃ (T_left_right ha hc)
  refine Game.eq_of_equiv_options
    (fun L hL => left_option_mul_distrib (a := a) (b := b) (c := c)
      IHa IHb IHc IHab IHac hL)
    (fun L hL => left_option_mul_distrib_symm (a := a) (b := b) (c := c)
      IHa IHb IHc IHab IHac hL)
    (fun R hR => right_option_mul_distrib (a := a) (b := b) (c := c)
      IHa IHb IHc IHab IHac hR)
    (fun R hR => right_option_mul_distrib_symm (a := a) (b := b) (c := c)
      IHa IHb IHc IHab IHac hR)

theorem mul_distrib {a b c : Game} :
    (a ⊗ (b ⊕ c)) ∼ ((a ⊗ b) ⊕ (a ⊗ c)) := by
  exact mul_distrib_tri ⟨a, b, c⟩

theorem mul_distrib_right {a b c : Game} :
    ((a ⊕ b) ⊗ c) ∼ ((a ⊗ c) ⊕ (b ⊗ c)) := by
  have h₁ : ((a ⊕ b) ⊗ c) ∼ (c ⊗ (a ⊕ b)) := by
    simpa using (Game.mul_comm (a := a ⊕ b) (b := c))
  have h₂ : (c ⊗ (a ⊕ b)) ∼ ((c ⊗ a) ⊕ (c ⊗ b)) := by
    simpa using (Game.mul_distrib (a := c) (b := a) (c := b))
  have h₃ : ((c ⊗ a) ⊕ (c ⊗ b)) ∼ ((a ⊗ c) ⊕ (b ⊗ c)) := by
    exact Game.add_equal
      ⟨Game.mul_comm (a := c) (b := a), Game.mul_comm (a := c) (b := b)⟩
  exact Game.eq_trans ⟨Game.eq_trans ⟨h₁, h₂⟩, h₃⟩

end Game
