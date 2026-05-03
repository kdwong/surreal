import Mathlib.Tactic.Linarith
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
  This file is a blueprint for associativity of Conway multiplication on surreal games.

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
  refine Game.eq_trans (y := y₁ ⊗ x) ?_
  constructor
  · exact Game.mul_comm (a := x) (b := y₁)
  · refine Game.eq_trans (y := y₂ ⊗ x) ?_
    constructor
    · exact Conway.conway_B sy₁ sy₂ sx h
    · exact Game.mul_comm (a := y₂) (b := x)

private lemma mul_congr
    {x₁ x₂ y₁ y₂ : Game}
    (sx₁ : IsSurreal x₁) (sx₂ : IsSurreal x₂)
    (sy₁ : IsSurreal y₁) (sy₂ : IsSurreal y₂)
    (hx : x₁ ∼ x₂) (hy : y₁ ∼ y₂) :
    (x₁ ⊗ y₁) ∼ (x₂ ⊗ y₂) := by
  refine Game.eq_trans (y := x₂ ⊗ y₁) ?_
  constructor
  · exact mul_congr_right sx₁ sx₂ sy₁ hx
  · exact mul_congr_left sx₂ sy₁ sy₂ hy

private lemma mulOpt4_congr {xOpt Y X yOpt A B C : Game}
    (h₁ : (xOpt ⊗ Y) ∼ A)
    (h₂ : (X ⊗ yOpt) ∼ B)
    (h₃ : (xOpt ⊗ yOpt) ∼ C) :
    Game.mulOpt4 xOpt Y X yOpt ∼ ((A ⊕ B) ⊕ C.neg) := by
  dsimp [Game.mulOpt4]
  have h₁₂ : ((xOpt ⊗ Y) ⊕ (X ⊗ yOpt)) ∼ (A ⊕ B) :=
    Game.add_equal ⟨h₁, h₂⟩
  have h₃' : (xOpt ⊗ yOpt).neg ∼ C.neg :=
    (Game.neg_congr).mp (Game.eq_symm h₃)
  exact Game.add_equal ⟨h₁₂, h₃'⟩

/-
  This is the key algebraic rewrite.

  In each branch of the option comparison, you instantiate:
    a₀ = one option of a
    b₀ = one option of b
    c₀ = one option of c

  and then use the seven recursive associativity hypotheses below.

  Proof sketch:
    * rewrite the outer `mulOpt4` with `mulOpt4_congr`,
    * rewrite the inner products using h₁,...,h₇,
    * use `mul_distrib` / `mul_distrib_right` to expand the RHS-shape,
    * finish with `Game.eq_of_q_eq`; after `simp`, use `abel`.
-/
private lemma mulOpt4_assoc_rewrite
    {a b c a₀ b₀ c₀ : Game}
    (h₁ : ((a₀ ⊗ b) ⊗ c) ∼ (a₀ ⊗ (b ⊗ c)))
    (h₂ : ((a ⊗ b₀) ⊗ c) ∼ (a ⊗ (b₀ ⊗ c)))
    (h₃ : ((a₀ ⊗ b₀) ⊗ c) ∼ (a₀ ⊗ (b₀ ⊗ c)))
    (h₄ : ((a ⊗ b) ⊗ c₀) ∼ (a ⊗ (b ⊗ c₀)))
    (h₅ : ((a₀ ⊗ b) ⊗ c₀) ∼ (a₀ ⊗ (b ⊗ c₀)))
    (h₆ : ((a ⊗ b₀) ⊗ c₀) ∼ (a ⊗ (b₀ ⊗ c₀)))
    (h₇ : ((a₀ ⊗ b₀) ⊗ c₀) ∼ (a₀ ⊗ (b₀ ⊗ c₀))) :
    Game.mulOpt4 (Game.mulOpt4 a₀ b a b₀) c (a ⊗ b) c₀
      ∼
    Game.mulOpt4 a₀ (b ⊗ c) a (Game.mulOpt4 b₀ c b c₀) := by
  /-
    Suggested implementation:
      1. Rewrite LHS first component:
           ((mulOpt4 a₀ b a b₀) ⊗ c)
         by applying `mulOpt4_congr` to h₁ h₂ h₃.
      2. Rewrite second component:
           ((a ⊗ b) ⊗ c₀)
         by h₄.
      3. Rewrite third component:
           ((mulOpt4 a₀ b a b₀) ⊗ c₀)
         by another `mulOpt4_congr` using h₅ h₆ h₇.
      4. Expand RHS `mulOpt4 a₀ (b ⊗ c) a (mulOpt4 b₀ c b c₀)`.
      5. Convert both sides to the additive quotient `GameQ`.
      6. `simp [Game.mulOpt4, Game.add_assoc]` and then `abel`.
  -/
  sorry

/-!
  A single packaged recursive hypothesis:
  to prove associativity for a smaller triple `(a', b', c')`,
  it is enough that each birthday is bounded by the ambient one,
  and at least one coordinate is strictly smaller.
-/
private def AssocIH (a b c : Game) : Prop :=
  ∀ a' b' c',
    Game.birthday a' ≤ Game.birthday a →
    Game.birthday b' ≤ Game.birthday b →
    Game.birthday c' ≤ Game.birthday c →
    (Game.birthday a' < Game.birthday a ∨
      Game.birthday b' < Game.birthday b ∨
      Game.birthday c' < Game.birthday c) →
    IsSurreal a' → IsSurreal b' → IsSurreal c' →
    AssocPred a' b' c'

/-! ### Option-matching lemmas

These are the four structural lemmas used by `Game.eq_of_equiv_options`.

They are intentionally written against the packaged hypothesis `AssocIH`,
so the main theorem only needs to build one local helper `IHsmall`.
-/

private lemma left_option_mul_assoc
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {L : Game} (hL : L ∈ ((a ⊗ b) ⊗ c).left) :
    ∃ L' ∈ (a ⊗ (b ⊗ c)).left, L ∼ L' := by
  rw [mem_mul_left] at hL
  rcases hL with
    ⟨abL, habL, cL, hcL, rfl⟩
  | ⟨abR, habR, cR, hcR, rfl⟩

  · rw [mem_mul_left] at habL
    rcases habL with
      ⟨aL, haL, bL, hbL, rfl⟩
    | ⟨aR, haR, bR, hbR, rfl⟩

    · -- branch (aL, bL, cL)
      let bcL : Game := Game.mulOpt4 bL c b cL
      have hbcL : bcL ∈ (b ⊗ c).left := by
        dsimp [bcL]
        exact mem_mul_left_ll hbL hcL
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a bcL, mem_mul_left_ll haL hbcL, ?_⟩
      dsimp [bcL]
      exact mulOpt4_assoc_rewrite
        (h₁ := IH aL b c
          (le_of_lt (Game.birthday_lt_left haL)) le_rfl le_rfl
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL) sb sc)
        (h₂ := IH a bL c
          le_rfl (le_of_lt (Game.birthday_lt_left hbL)) le_rfl
          (Or.inr (Or.inl (Game.birthday_lt_left hbL)))
          sa (IsSurreal.isSurreal_left sb hbL) sc)
        (h₃ := IH aL bL c
          (le_of_lt (Game.birthday_lt_left haL))
          (le_of_lt (Game.birthday_lt_left hbL)) le_rfl
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL)
          (IsSurreal.isSurreal_left sb hbL) sc)
        (h₄ := IH a b cL
          le_rfl le_rfl (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inr (Or.inr (Game.birthday_lt_left hcL)))
          sa sb (IsSurreal.isSurreal_left sc hcL))
        (h₅ := IH aL b cL
          (le_of_lt (Game.birthday_lt_left haL)) le_rfl
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL) sb
          (IsSurreal.isSurreal_left sc hcL))
        (h₆ := IH a bL cL
          le_rfl (le_of_lt (Game.birthday_lt_left hbL))
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inr (Or.inl (Game.birthday_lt_left hbL)))
          sa (IsSurreal.isSurreal_left sb hbL)
          (IsSurreal.isSurreal_left sc hcL))
        (h₇ := IH aL bL cL
          (le_of_lt (Game.birthday_lt_left haL))
          (le_of_lt (Game.birthday_lt_left hbL))
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL)
          (IsSurreal.isSurreal_left sb hbL)
          (IsSurreal.isSurreal_left sc hcL))
    · -- branch (aR, bR, cL)
      let bcR : Game := Game.mulOpt4 bR c b cL
      have hbcR : bcR ∈ (b ⊗ c).right := by
        dsimp [bcR]
        exact mem_mul_right_rl hbR hcL
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a bcR, mem_mul_left_rr haR hbcR, ?_⟩
      dsimp [bcR]
      exact mulOpt4_assoc_rewrite
        (h₁ := IH aR b c
          (le_of_lt (Game.birthday_lt_right haR)) le_rfl le_rfl
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR) sb sc)
        (h₂ := IH a bR c
          le_rfl (le_of_lt (Game.birthday_lt_right hbR)) le_rfl
          (Or.inr (Or.inl (Game.birthday_lt_right hbR)))
          sa (IsSurreal.isSurreal_right sb hbR) sc)
        (h₃ := IH aR bR c
          (le_of_lt (Game.birthday_lt_right haR))
          (le_of_lt (Game.birthday_lt_right hbR)) le_rfl
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR)
          (IsSurreal.isSurreal_right sb hbR) sc)
        (h₄ := IH a b cL
          le_rfl le_rfl (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inr (Or.inr (Game.birthday_lt_left hcL)))
          sa sb (IsSurreal.isSurreal_left sc hcL))
        (h₅ := IH aR b cL
          (le_of_lt (Game.birthday_lt_right haR)) le_rfl
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR) sb
          (IsSurreal.isSurreal_left sc hcL))
        (h₆ := IH a bR cL
          le_rfl (le_of_lt (Game.birthday_lt_right hbR))
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inr (Or.inl (Game.birthday_lt_right hbR)))
          sa (IsSurreal.isSurreal_right sb hbR)
          (IsSurreal.isSurreal_left sc hcL))
        (h₇ := IH aR bR cL
          (le_of_lt (Game.birthday_lt_right haR))
          (le_of_lt (Game.birthday_lt_right hbR))
          (le_of_lt (Game.birthday_lt_left hcL))
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR)
          (IsSurreal.isSurreal_right sb hbR)
          (IsSurreal.isSurreal_left sc hcL))
  · rw [mem_mul_right] at habR
    rcases habR with
      ⟨aL, haL, bR, hbR, rfl⟩
    | ⟨aR, haR, bL, hbL, rfl⟩

    · -- branch (aL, bR, cR)
      let bcL : Game := Game.mulOpt4 bR c b cR
      have hbcL : bcL ∈ (b ⊗ c).left := by
        dsimp [bcL]
        exact mem_mul_left_rr hbR hcR
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a bcL, mem_mul_left_ll haL hbcL, ?_⟩
      dsimp [bcL]
      exact mulOpt4_assoc_rewrite
        (h₁ := IH aL b c
          (le_of_lt (Game.birthday_lt_left haL)) le_rfl le_rfl
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL) sb sc)
        (h₂ := IH a bR c
          le_rfl (le_of_lt (Game.birthday_lt_right hbR)) le_rfl
          (Or.inr (Or.inl (Game.birthday_lt_right hbR)))
          sa (IsSurreal.isSurreal_right sb hbR) sc)
        (h₃ := IH aL bR c
          (le_of_lt (Game.birthday_lt_left haL))
          (le_of_lt (Game.birthday_lt_right hbR)) le_rfl
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL)
          (IsSurreal.isSurreal_right sb hbR) sc)
        (h₄ := IH a b cR
          le_rfl le_rfl (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inr (Or.inr (Game.birthday_lt_right hcR)))
          sa sb (IsSurreal.isSurreal_right sc hcR))
        (h₅ := IH aL b cR
          (le_of_lt (Game.birthday_lt_left haL)) le_rfl
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL) sb
          (IsSurreal.isSurreal_right sc hcR))
        (h₆ := IH a bR cR
          le_rfl (le_of_lt (Game.birthday_lt_right hbR))
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inr (Or.inl (Game.birthday_lt_right hbR)))
          sa (IsSurreal.isSurreal_right sb hbR)
          (IsSurreal.isSurreal_right sc hcR))
        (h₇ := IH aL bR cR
          (le_of_lt (Game.birthday_lt_left haL))
          (le_of_lt (Game.birthday_lt_right hbR))
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inl (Game.birthday_lt_left haL))
          (IsSurreal.isSurreal_left sa haL)
          (IsSurreal.isSurreal_right sb hbR)
          (IsSurreal.isSurreal_right sc hcR))

    · -- branch (aR, bL, cR)
      let bcR : Game := Game.mulOpt4 bL c b cR
      have hbcR : bcR ∈ (b ⊗ c).right := by
        dsimp [bcR]
        exact mem_mul_right_lr hbL hcR
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a bcR, mem_mul_left_rr haR hbcR, ?_⟩
      dsimp [bcR]
      exact mulOpt4_assoc_rewrite
        (h₁ := IH aR b c
          (le_of_lt (Game.birthday_lt_right haR)) le_rfl le_rfl
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR) sb sc)
        (h₂ := IH a bL c
          le_rfl (le_of_lt (Game.birthday_lt_left hbL)) le_rfl
          (Or.inr (Or.inl (Game.birthday_lt_left hbL)))
          sa (IsSurreal.isSurreal_left sb hbL) sc)
        (h₃ := IH aR bL c
          (le_of_lt (Game.birthday_lt_right haR))
          (le_of_lt (Game.birthday_lt_left hbL)) le_rfl
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR)
          (IsSurreal.isSurreal_left sb hbL) sc)
        (h₄ := IH a b cR
          le_rfl le_rfl (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inr (Or.inr (Game.birthday_lt_right hcR)))
          sa sb (IsSurreal.isSurreal_right sc hcR))
        (h₅ := IH aR b cR
          (le_of_lt (Game.birthday_lt_right haR)) le_rfl
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR) sb
          (IsSurreal.isSurreal_right sc hcR))
        (h₆ := IH a bL cR
          le_rfl (le_of_lt (Game.birthday_lt_left hbL))
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inr (Or.inl (Game.birthday_lt_left hbL)))
          sa (IsSurreal.isSurreal_left sb hbL)
          (IsSurreal.isSurreal_right sc hcR))
        (h₇ := IH aR bL cR
          (le_of_lt (Game.birthday_lt_right haR))
          (le_of_lt (Game.birthday_lt_left hbL))
          (le_of_lt (Game.birthday_lt_right hcR))
          (Or.inl (Game.birthday_lt_right haR))
          (IsSurreal.isSurreal_right sa haR)
          (IsSurreal.isSurreal_left sb hbL)
          (IsSurreal.isSurreal_right sc hcR))

private lemma left_option_mul_assoc_symm
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {L : Game} (hL : L ∈ (a ⊗ (b ⊗ c)).left) :
    ∃ L' ∈ ((a ⊗ b) ⊗ c).left, L ∼ L' := by
  /-
    Mirror of `left_option_mul_assoc`.

    Decompose `hL` using `mem_mul_left`.
    Then decompose membership in `(b ⊗ c).left` or `.right`.
    The 4 branches are:
      (aL, bL, cL), (aL, bR, cR), (aR, bL, cR), (aR, bR, cL).
    For each branch, choose the corresponding option on `((a ⊗ b) ⊗ c).left`
    and finish with `Game.eq_symm <| mulOpt4_assoc_rewrite ...`.
  -/
  sorry

private lemma right_option_mul_assoc
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {R : Game} (hR : R ∈ ((a ⊗ b) ⊗ c).right) :
    ∃ R' ∈ (a ⊗ (b ⊗ c)).right, R ∼ R' := by
  /-
    Outer right branches are:
      (abL, cR) or (abR, cL).

    After decomposing `abL` / `abR`, the 4 concrete branches are:
      (aL, bL, cR), (aR, bR, cR), (aL, bR, cL), (aR, bL, cL).

    Corresponding target memberships in `a ⊗ (b ⊗ c)` are:
      right_lr, right_rl, right_lr, right_rl.
  -/
  sorry

private lemma right_option_mul_assoc_symm
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {R : Game} (hR : R ∈ (a ⊗ (b ⊗ c)).right) :
    ∃ R' ∈ ((a ⊗ b) ⊗ c).right, R ∼ R' := by
  /-
    Mirror of `right_option_mul_assoc`.
  -/
  sorry

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

  have IHsmall : AssocIH a b c := by
    intro a' b' c' ha' hb' hc' hstrict sa' sb' sc'
    exact IH ⟨a', b', c'⟩ (by
      /-
        Fill this by converting the birthday bounds + one strict inequality
        into your relation `T ⟨a', b', c'⟩ ⟨a, b, c⟩`.

        If you already have constructors/lemmas such as:
          T_left, T_mid, T_right, T_left_mid, T_left_right, T_mid_right, ...
        then use them here.
      -/
      sorry) sa' sb' sc'

  refine Game.eq_of_equiv_options
    (fun L hL => left_option_mul_assoc sa sb sc IHsmall hL)
    (fun L hL => left_option_mul_assoc_symm sa sb sc IHsmall hL)
    (fun R hR => right_option_mul_assoc sa sb sc IHsmall hR)
    (fun R hR => right_option_mul_assoc_symm sa sb sc IHsmall hR)

end Game
