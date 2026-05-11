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

lemma mul_congr
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
  have h₁₂ : ((xOpt ⊗ Y) ⊕ (X ⊗ yOpt)) ∼ (A ⊕ B) := Game.add_equal ⟨h₁, h₂⟩
  have h₃' : (xOpt ⊗ yOpt).neg ∼ C.neg := (Game.neg_congr).mp (Game.eq_symm h₃)
  exact Game.add_equal ⟨h₁₂, h₃'⟩


private lemma mul_neg_mem_neg_left_iff {x l : Game} :
    l ∈ (Game.neg x).left ↔ ∃ r ∈ x.right, l = Game.neg r := by
  rw [neg_left_def, List.mem_map]
  constructor
  · rintro ⟨⟨r, hr⟩, -, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, by simp, rfl⟩

private lemma mul_neg_mem_neg_right_iff {x r : Game} :
    r ∈ (Game.neg x).right ↔ ∃ l ∈ x.left, r = Game.neg l := by
  rw [neg_right_def, List.mem_map]
  constructor
  · rintro ⟨⟨l, hl⟩, -, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, by simp, rfl⟩

private lemma mul_neg_mem_neg_left_of_right {x r : Game}
    (hr : r ∈ x.right) :
    Game.neg r ∈ (Game.neg x).left := by
  rw [mul_neg_mem_neg_left_iff]
  exact ⟨r, hr, rfl⟩

private lemma mul_neg_mem_neg_right_of_left {x l : Game}
    (hl : l ∈ x.left) :
    Game.neg l ∈ (Game.neg x).right := by
  rw [mul_neg_mem_neg_right_iff]
  exact ⟨l, hl, rfl⟩

private lemma mulOpt4_neg_right_aux
    {xOpt Y X yOpt : Game}
    (h₁ : (xOpt ⊗ Y.neg) ∼ (xOpt ⊗ Y).neg)
    (h₂ : (X ⊗ yOpt.neg) ∼ (X ⊗ yOpt).neg)
    (h₃ : (xOpt ⊗ yOpt.neg) ∼ (xOpt ⊗ yOpt).neg) :
    Game.mulOpt4 xOpt Y.neg X yOpt.neg ∼
      (Game.mulOpt4 xOpt Y X yOpt).neg := by
  refine Game.eq_of_q_eq ?_
  simp [Game.mulOpt4, Game.q_sound h₁, Game.q_sound h₂, Game.q_sound h₃]
  abel

private lemma Game.mul_neg {x y : Game} :
    (x ⊗ y.neg) ∼ (x ⊗ y).neg := by
  let P : Game.BiGame → Prop :=
    fun z => (z.a ⊗ z.b.neg) ∼ (z.a ⊗ z.b).neg

  have hP : ∀ z : Game.BiGame, P z := by
    intro z
    refine Game.wf_B.induction (C := P) z ?_
    rintro ⟨x, y⟩ IH
    dsimp [P]

    refine Game.eq_of_equiv_options ?_ ?_ ?_ ?_

    · -- left options of `x ⊗ y.neg`
      intro L hL
      rw [mem_mul_left] at hL
      rcases hL with
        ⟨xL, hxL, ynL, hynL, rfl⟩
      | ⟨xR, hxR, ynR, hynR, rfl⟩

      · rcases (mul_neg_mem_neg_left_iff.mp hynL) with ⟨yR, hyR, rfl⟩
        refine
          ⟨(Game.mulOpt4 xL y x yR).neg,
            mul_neg_mem_neg_left_of_right (mem_mul_right_lr hxL hyR),
            ?_⟩
        exact mulOpt4_neg_right_aux
          (IH ⟨xL, y⟩ (Game.B_of_left_mem_fst hxL))
          (IH ⟨x, yR⟩ (Game.B_of_right_mem_snd hyR))
          (IH ⟨xL, yR⟩ (Game.B_of_left_right hxL hyR))

      · rcases (mul_neg_mem_neg_right_iff.mp hynR) with ⟨yL, hyL, rfl⟩
        refine
          ⟨(Game.mulOpt4 xR y x yL).neg,
            mul_neg_mem_neg_left_of_right (mem_mul_right_rl hxR hyL),
            ?_⟩
        exact mulOpt4_neg_right_aux
          (IH ⟨xR, y⟩ (Game.B_of_right_mem_fst hxR))
          (IH ⟨x, yL⟩ (Game.B_of_left_mem_snd hyL))
          (IH ⟨xR, yL⟩ (Game.B_of_right_left hxR hyL))

    · -- left options of `(x ⊗ y).neg`
      intro L hL
      rw [mul_neg_mem_neg_left_iff] at hL
      rcases hL with ⟨R, hR, rfl⟩
      rw [mem_mul_right] at hR
      rcases hR with
        ⟨xL, hxL, yR, hyR, rfl⟩
      | ⟨xR, hxR, yL, hyL, rfl⟩

      · refine
          ⟨Game.mulOpt4 xL y.neg x yR.neg,
            mem_mul_left_ll hxL (mul_neg_mem_neg_left_of_right hyR),
            ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_aux
          (IH ⟨xL, y⟩ (Game.B_of_left_mem_fst hxL))
          (IH ⟨x, yR⟩ (Game.B_of_right_mem_snd hyR))
          (IH ⟨xL, yR⟩ (Game.B_of_left_right hxL hyR))

      · refine
          ⟨Game.mulOpt4 xR y.neg x yL.neg,
            mem_mul_left_rr hxR (mul_neg_mem_neg_right_of_left hyL),
            ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_aux
          (IH ⟨xR, y⟩ (Game.B_of_right_mem_fst hxR))
          (IH ⟨x, yL⟩ (Game.B_of_left_mem_snd hyL))
          (IH ⟨xR, yL⟩ (Game.B_of_right_left hxR hyL))

    · -- right options of `x ⊗ y.neg`
      intro R hR
      rw [mem_mul_right] at hR
      rcases hR with
        ⟨xL, hxL, ynR, hynR, rfl⟩
      | ⟨xR, hxR, ynL, hynL, rfl⟩

      · rcases (mul_neg_mem_neg_right_iff.mp hynR) with ⟨yL, hyL, rfl⟩
        refine
          ⟨(Game.mulOpt4 xL y x yL).neg,
            mul_neg_mem_neg_right_of_left (mem_mul_left_ll hxL hyL),
            ?_⟩
        exact mulOpt4_neg_right_aux
          (IH ⟨xL, y⟩ (Game.B_of_left_mem_fst hxL))
          (IH ⟨x, yL⟩ (Game.B_of_left_mem_snd hyL))
          (IH ⟨xL, yL⟩ (Game.B_of_left_left hxL hyL))

      · rcases (mul_neg_mem_neg_left_iff.mp hynL) with ⟨yR, hyR, rfl⟩
        refine
          ⟨(Game.mulOpt4 xR y x yR).neg,
            mul_neg_mem_neg_right_of_left (mem_mul_left_rr hxR hyR),
            ?_⟩
        exact mulOpt4_neg_right_aux
          (IH ⟨xR, y⟩ (Game.B_of_right_mem_fst hxR))
          (IH ⟨x, yR⟩ (Game.B_of_right_mem_snd hyR))
          (IH ⟨xR, yR⟩ (Game.B_of_right_right hxR hyR))

    · -- right options of `(x ⊗ y).neg`
      intro R hR
      rw [mul_neg_mem_neg_right_iff] at hR
      rcases hR with ⟨L, hL, rfl⟩
      rw [mem_mul_left] at hL
      rcases hL with
        ⟨xL, hxL, yL, hyL, rfl⟩
      | ⟨xR, hxR, yR, hyR, rfl⟩

      · refine
          ⟨Game.mulOpt4 xL y.neg x yL.neg,
            mem_mul_right_lr hxL (mul_neg_mem_neg_right_of_left hyL),
            ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_aux
          (IH ⟨xL, y⟩ (Game.B_of_left_mem_fst hxL))
          (IH ⟨x, yL⟩ (Game.B_of_left_mem_snd hyL))
          (IH ⟨xL, yL⟩ (Game.B_of_left_left hxL hyL))

      · refine
          ⟨Game.mulOpt4 xR y.neg x yR.neg,
            mem_mul_right_rl hxR (mul_neg_mem_neg_left_of_right hyR),
            ?_⟩
        exact Game.eq_symm <| mulOpt4_neg_right_aux
          (IH ⟨xR, y⟩ (Game.B_of_right_mem_fst hxR))
          (IH ⟨x, yR⟩ (Game.B_of_right_mem_snd hyR))
          (IH ⟨xR, yR⟩ (Game.B_of_right_right hxR hyR))

  exact hP ⟨x, y⟩


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
private lemma neg_mul_from_mul_neg {x y : Game} :
    (x.neg ⊗ y) ∼ (x ⊗ y).neg := by
  have hcomm₁ : (x.neg ⊗ y) ∼ (y ⊗ x.neg) := by
    simpa using (Game.mul_comm (a := x.neg) (b := y))
  have hmn : (y ⊗ x.neg) ∼ (y ⊗ x).neg := by
    simpa using (@Game.mul_neg y x)
  have hcomm₂ : (y ⊗ x).neg ∼ (x ⊗ y).neg := by
    simpa using (Game.neg_congr_left (Game.mul_comm (a := y) (b := x)))
  exact Game.eq_trans ⟨hcomm₁, Game.eq_trans ⟨hmn, hcomm₂⟩⟩

private lemma q_mulOpt4_mul_right
    {xOpt Y X yOpt z A B C : Game}
    (h₁ : ((xOpt ⊗ Y) ⊗ z) ∼ A)
    (h₂ : ((X ⊗ yOpt) ⊗ z) ∼ B)
    (h₃ : ((xOpt ⊗ yOpt) ⊗ z) ∼ C) :
    (Game.q ((Game.mulOpt4 xOpt Y X yOpt) ⊗ z) : Game.GameQ) =
      Game.q A + Game.q B - Game.q C := by
  dsimp [Game.mulOpt4]

  rw [Game.q_sound (Game.mul_distrib_right
    (a := (xOpt ⊗ Y) ⊕ (X ⊗ yOpt))
    (b := (xOpt ⊗ yOpt).neg)
    (c := z))]
  simp only [Game.q_add]

  rw [Game.q_sound (Game.mul_distrib_right
    (a := xOpt ⊗ Y)
    (b := X ⊗ yOpt)
    (c := z))]
  simp only [Game.q_add]

  have hneg :
      (((xOpt ⊗ yOpt).neg) ⊗ z) ∼ (((xOpt ⊗ yOpt) ⊗ z).neg) := by
    simpa using
      (neg_mul_from_mul_neg (x := xOpt ⊗ yOpt) (y := z))
  rw [Game.q_sound hneg]
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
    (a := x)
    (b := (xOpt ⊗ Y) ⊕ (X ⊗ yOpt))
    (c := (xOpt ⊗ yOpt).neg))]
  simp only [Game.q_add]

  rw [Game.q_sound (Game.mul_distrib
    (a := x)
    (b := xOpt ⊗ Y)
    (c := X ⊗ yOpt))]
  simp only [Game.q_add]

  have hneg :
      (x ⊗ (xOpt ⊗ yOpt).neg) ∼ (x ⊗ (xOpt ⊗ yOpt)).neg := by
    simpa using (@Game.mul_neg x (xOpt ⊗ yOpt))
  rw [Game.q_sound hneg]
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

  have hABc :
      (Game.q (((Game.mulOpt4 a₀ b a b₀) ⊗ c)) : Game.GameQ) =
        Game.q (a₀ ⊗ (b ⊗ c)) +
          Game.q (a ⊗ (b₀ ⊗ c)) -
            Game.q (a₀ ⊗ (b₀ ⊗ c)) := by
    exact q_mulOpt4_mul_right
      (xOpt := a₀) (Y := b) (X := a) (yOpt := b₀) (z := c)
      h₁ h₂ h₃

  have hABc0 :
      (Game.q (((Game.mulOpt4 a₀ b a b₀) ⊗ c₀)) : Game.GameQ) =
        Game.q (a₀ ⊗ (b ⊗ c₀)) +
          Game.q (a ⊗ (b₀ ⊗ c₀)) -
            Game.q (a₀ ⊗ (b₀ ⊗ c₀)) := by
    exact q_mulOpt4_mul_right
      (xOpt := a₀) (Y := b) (X := a) (yOpt := b₀) (z := c₀)
      h₅ h₆ h₇

  have haBC :
      (Game.q (a ⊗ Game.mulOpt4 b₀ c b c₀) : Game.GameQ) =
        Game.q (a ⊗ (b₀ ⊗ c)) +
          Game.q (a ⊗ (b ⊗ c₀)) -
            Game.q (a ⊗ (b₀ ⊗ c₀)) := by
    exact q_mul_mulOpt4
      (x := a) (xOpt := b₀) (Y := c) (X := b) (yOpt := c₀)

  have ha0BC :
      (Game.q (a₀ ⊗ Game.mulOpt4 b₀ c b c₀) : Game.GameQ) =
        Game.q (a₀ ⊗ (b₀ ⊗ c)) +
          Game.q (a₀ ⊗ (b ⊗ c₀)) -
            Game.q (a₀ ⊗ (b₀ ⊗ c₀)) := by
    exact q_mul_mulOpt4
      (x := a₀) (xOpt := b₀) (Y := c) (X := b) (yOpt := c₀)

  change
    (Game.q
      (((((Game.mulOpt4 a₀ b a b₀) ⊗ c) ⊕ ((a ⊗ b) ⊗ c₀)) ⊕
        (((Game.mulOpt4 a₀ b a b₀) ⊗ c₀).neg))) : Game.GameQ)
      =
    (Game.q
      ((((a₀ ⊗ (b ⊗ c)) ⊕ (a ⊗ Game.mulOpt4 b₀ c b c₀)) ⊕
        ((a₀ ⊗ Game.mulOpt4 b₀ c b c₀).neg))) : Game.GameQ)

  simp only [Game.q_add, Game.q_neg]
  rw [hABc, Game.q_sound h₄, hABc0, haBC, ha0BC]
  abel

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
  rw [mem_mul_left] at hL
  rcases hL with
    ⟨aL, haL, bcL, hbcL, rfl⟩
  | ⟨aR, haR, bcR, hbcR, rfl⟩

  · rw [mem_mul_left] at hbcL
    rcases hbcL with
      ⟨bL, hbL, cL, hcL, rfl⟩
    | ⟨bR, hbR, cR, hcR, rfl⟩

    · -- branch (aL, bL, cL)
      let abL : Game := Game.mulOpt4 aL b a bL
      have habL : abL ∈ (a ⊗ b).left := by
        dsimp [abL]
        exact mem_mul_left_ll haL hbL
      refine ⟨Game.mulOpt4 abL c (a ⊗ b) cL, mem_mul_left_ll habL hcL, ?_⟩
      dsimp [abL]
      exact Game.eq_symm <| mulOpt4_assoc_rewrite
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

    · -- branch (aL, bR, cR)
      let abR : Game := Game.mulOpt4 aL b a bR
      have habR : abR ∈ (a ⊗ b).right := by
        dsimp [abR]
        exact mem_mul_right_lr haL hbR
      refine ⟨Game.mulOpt4 abR c (a ⊗ b) cR, mem_mul_left_rr habR hcR, ?_⟩
      dsimp [abR]
      exact Game.eq_symm <| mulOpt4_assoc_rewrite
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

  · rw [mem_mul_right] at hbcR
    rcases hbcR with
      ⟨bL, hbL, cR, hcR, rfl⟩
    | ⟨bR, hbR, cL, hcL, rfl⟩

    · -- branch (aR, bL, cR)
      let abR : Game := Game.mulOpt4 aR b a bL
      have habR : abR ∈ (a ⊗ b).right := by
        dsimp [abR]
        exact mem_mul_right_rl haR hbL
      refine ⟨Game.mulOpt4 abR c (a ⊗ b) cR, mem_mul_left_rr habR hcR, ?_⟩
      dsimp [abR]
      exact Game.eq_symm <| mulOpt4_assoc_rewrite
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

    · -- branch (aR, bR, cL)
      let abL : Game := Game.mulOpt4 aR b a bR
      have habL : abL ∈ (a ⊗ b).left := by
        dsimp [abL]
        exact mem_mul_left_rr haR hbR
      refine ⟨Game.mulOpt4 abL c (a ⊗ b) cL, mem_mul_left_ll habL hcL, ?_⟩
      dsimp [abL]
      exact Game.eq_symm <| mulOpt4_assoc_rewrite
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

private lemma right_option_mul_assoc
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {R : Game} (hR : R ∈ ((a ⊗ b) ⊗ c).right) :
    ∃ R' ∈ (a ⊗ (b ⊗ c)).right, R ∼ R' := by
  have hassoc
      {a₀ b₀ c₀ : Game}
      (ha₀ : a₀.birthday < a.birthday)
      (hb₀ : b₀.birthday < b.birthday)
      (hc₀ : c₀.birthday < c.birthday)
      (sa₀ : IsSurreal a₀) (sb₀ : IsSurreal b₀) (sc₀ : IsSurreal c₀) :
      Game.mulOpt4 (Game.mulOpt4 a₀ b a b₀) c (a ⊗ b) c₀ ∼
        Game.mulOpt4 a₀ (b ⊗ c) a (Game.mulOpt4 b₀ c b c₀) := by
    exact mulOpt4_assoc_rewrite
      (h₁ := IH a₀ b c
        (le_of_lt ha₀) le_rfl le_rfl
        (Or.inl ha₀)
        sa₀ sb sc)
      (h₂ := IH a b₀ c
        le_rfl (le_of_lt hb₀) le_rfl
        (Or.inr (Or.inl hb₀))
        sa sb₀ sc)
      (h₃ := IH a₀ b₀ c
        (le_of_lt ha₀) (le_of_lt hb₀) le_rfl
        (Or.inl ha₀)
        sa₀ sb₀ sc)
      (h₄ := IH a b c₀
        le_rfl le_rfl (le_of_lt hc₀)
        (Or.inr (Or.inr hc₀))
        sa sb sc₀)
      (h₅ := IH a₀ b c₀
        (le_of_lt ha₀) le_rfl (le_of_lt hc₀)
        (Or.inl ha₀)
        sa₀ sb sc₀)
      (h₆ := IH a b₀ c₀
        le_rfl (le_of_lt hb₀) (le_of_lt hc₀)
        (Or.inr (Or.inl hb₀))
        sa sb₀ sc₀)
      (h₇ := IH a₀ b₀ c₀
        (le_of_lt ha₀) (le_of_lt hb₀) (le_of_lt hc₀)
        (Or.inl ha₀)
        sa₀ sb₀ sc₀)

  rw [mem_mul_right] at hR
  rcases hR with
    ⟨abL, habL, cR, hcR, rfl⟩
  | ⟨abR, habR, cL, hcL, rfl⟩

  · rw [mem_mul_left] at habL
    rcases habL with
      ⟨aL, haL, bL, hbL, rfl⟩
    | ⟨aR, haR, bR, hbR, rfl⟩

    · -- branch (aL, bL, cR)
      let bcR : Game := Game.mulOpt4 bL c b cR
      have hbcR : bcR ∈ (b ⊗ c).right := by
        dsimp [bcR]
        exact mem_mul_right_lr hbL hcR
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a bcR, mem_mul_right_lr haL hbcR, ?_⟩
      dsimp [bcR]
      exact hassoc
        (a₀ := aL) (b₀ := bL) (c₀ := cR)
        (Game.birthday_lt_left haL)
        (Game.birthday_lt_left hbL)
        (Game.birthday_lt_right hcR)
        (IsSurreal.isSurreal_left sa haL)
        (IsSurreal.isSurreal_left sb hbL)
        (IsSurreal.isSurreal_right sc hcR)

    · -- branch (aR, bR, cR)
      let bcL : Game := Game.mulOpt4 bR c b cR
      have hbcL : bcL ∈ (b ⊗ c).left := by
        dsimp [bcL]
        exact mem_mul_left_rr hbR hcR
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a bcL, mem_mul_right_rl haR hbcL, ?_⟩
      dsimp [bcL]
      exact hassoc
        (a₀ := aR) (b₀ := bR) (c₀ := cR)
        (Game.birthday_lt_right haR)
        (Game.birthday_lt_right hbR)
        (Game.birthday_lt_right hcR)
        (IsSurreal.isSurreal_right sa haR)
        (IsSurreal.isSurreal_right sb hbR)
        (IsSurreal.isSurreal_right sc hcR)

  · rw [mem_mul_right] at habR
    rcases habR with
      ⟨aL, haL, bR, hbR, rfl⟩
    | ⟨aR, haR, bL, hbL, rfl⟩

    · -- branch (aL, bR, cL)
      let bcR : Game := Game.mulOpt4 bR c b cL
      have hbcR : bcR ∈ (b ⊗ c).right := by
        dsimp [bcR]
        exact mem_mul_right_rl hbR hcL
      refine ⟨Game.mulOpt4 aL (b ⊗ c) a bcR, mem_mul_right_lr haL hbcR, ?_⟩
      dsimp [bcR]
      exact hassoc
        (a₀ := aL) (b₀ := bR) (c₀ := cL)
        (Game.birthday_lt_left haL)
        (Game.birthday_lt_right hbR)
        (Game.birthday_lt_left hcL)
        (IsSurreal.isSurreal_left sa haL)
        (IsSurreal.isSurreal_right sb hbR)
        (IsSurreal.isSurreal_left sc hcL)

    · -- branch (aR, bL, cL)
      let bcL : Game := Game.mulOpt4 bL c b cL
      have hbcL : bcL ∈ (b ⊗ c).left := by
        dsimp [bcL]
        exact mem_mul_left_ll hbL hcL
      refine ⟨Game.mulOpt4 aR (b ⊗ c) a bcL, mem_mul_right_rl haR hbcL, ?_⟩
      dsimp [bcL]
      exact hassoc
        (a₀ := aR) (b₀ := bL) (c₀ := cL)
        (Game.birthday_lt_right haR)
        (Game.birthday_lt_left hbL)
        (Game.birthday_lt_left hcL)
        (IsSurreal.isSurreal_right sa haR)
        (IsSurreal.isSurreal_left sb hbL)
        (IsSurreal.isSurreal_left sc hcL)


private lemma right_option_mul_assoc_symm
    {a b c : Game}
    (sa : IsSurreal a) (sb : IsSurreal b) (sc : IsSurreal c)
    (IH : AssocIH a b c)
    {R : Game} (hR : R ∈ (a ⊗ (b ⊗ c)).right) :
    ∃ R' ∈ ((a ⊗ b) ⊗ c).right, R ∼ R' := by
  have hassoc
      {a₀ b₀ c₀ : Game}
      (ha₀ : a₀.birthday < a.birthday)
      (hb₀ : b₀.birthday < b.birthday)
      (hc₀ : c₀.birthday < c.birthday)
      (sa₀ : IsSurreal a₀) (sb₀ : IsSurreal b₀) (sc₀ : IsSurreal c₀) :
      Game.mulOpt4 (Game.mulOpt4 a₀ b a b₀) c (a ⊗ b) c₀ ∼
        Game.mulOpt4 a₀ (b ⊗ c) a (Game.mulOpt4 b₀ c b c₀) := by
    exact mulOpt4_assoc_rewrite
      (h₁ := IH a₀ b c
        (le_of_lt ha₀) le_rfl le_rfl
        (Or.inl ha₀)
        sa₀ sb sc)
      (h₂ := IH a b₀ c
        le_rfl (le_of_lt hb₀) le_rfl
        (Or.inr (Or.inl hb₀))
        sa sb₀ sc)
      (h₃ := IH a₀ b₀ c
        (le_of_lt ha₀) (le_of_lt hb₀) le_rfl
        (Or.inl ha₀)
        sa₀ sb₀ sc)
      (h₄ := IH a b c₀
        le_rfl le_rfl (le_of_lt hc₀)
        (Or.inr (Or.inr hc₀))
        sa sb sc₀)
      (h₅ := IH a₀ b c₀
        (le_of_lt ha₀) le_rfl (le_of_lt hc₀)
        (Or.inl ha₀)
        sa₀ sb sc₀)
      (h₆ := IH a b₀ c₀
        le_rfl (le_of_lt hb₀) (le_of_lt hc₀)
        (Or.inr (Or.inl hb₀))
        sa sb₀ sc₀)
      (h₇ := IH a₀ b₀ c₀
        (le_of_lt ha₀) (le_of_lt hb₀) (le_of_lt hc₀)
        (Or.inl ha₀)
        sa₀ sb₀ sc₀)

  rw [mem_mul_right] at hR
  rcases hR with
    ⟨aL, haL, bcR, hbcR, rfl⟩
  | ⟨aR, haR, bcL, hbcL, rfl⟩

  · rw [mem_mul_right] at hbcR
    rcases hbcR with
      ⟨bL, hbL, cR, hcR, rfl⟩
    | ⟨bR, hbR, cL, hcL, rfl⟩

    · -- branch (aL, bL, cR)
      let abL : Game := Game.mulOpt4 aL b a bL
      have habL : abL ∈ (a ⊗ b).left := by
        dsimp [abL]
        exact mem_mul_left_ll haL hbL
      refine ⟨Game.mulOpt4 abL c (a ⊗ b) cR, mem_mul_right_lr habL hcR, ?_⟩
      dsimp [abL]
      exact Game.eq_symm <| hassoc
        (a₀ := aL) (b₀ := bL) (c₀ := cR)
        (Game.birthday_lt_left haL)
        (Game.birthday_lt_left hbL)
        (Game.birthday_lt_right hcR)
        (IsSurreal.isSurreal_left sa haL)
        (IsSurreal.isSurreal_left sb hbL)
        (IsSurreal.isSurreal_right sc hcR)

    · -- branch (aL, bR, cL)
      let abR : Game := Game.mulOpt4 aL b a bR
      have habR : abR ∈ (a ⊗ b).right := by
        dsimp [abR]
        exact mem_mul_right_lr haL hbR
      refine ⟨Game.mulOpt4 abR c (a ⊗ b) cL, mem_mul_right_rl habR hcL, ?_⟩
      dsimp [abR]
      exact Game.eq_symm <| hassoc
        (a₀ := aL) (b₀ := bR) (c₀ := cL)
        (Game.birthday_lt_left haL)
        (Game.birthday_lt_right hbR)
        (Game.birthday_lt_left hcL)
        (IsSurreal.isSurreal_left sa haL)
        (IsSurreal.isSurreal_right sb hbR)
        (IsSurreal.isSurreal_left sc hcL)

  · rw [mem_mul_left] at hbcL
    rcases hbcL with
      ⟨bL, hbL, cL, hcL, rfl⟩
    | ⟨bR, hbR, cR, hcR, rfl⟩

    · -- branch (aR, bL, cL)
      let abR : Game := Game.mulOpt4 aR b a bL
      have habR : abR ∈ (a ⊗ b).right := by
        dsimp [abR]
        exact mem_mul_right_rl haR hbL
      refine ⟨Game.mulOpt4 abR c (a ⊗ b) cL, mem_mul_right_rl habR hcL, ?_⟩
      dsimp [abR]
      exact Game.eq_symm <| hassoc
        (a₀ := aR) (b₀ := bL) (c₀ := cL)
        (Game.birthday_lt_right haR)
        (Game.birthday_lt_left hbL)
        (Game.birthday_lt_left hcL)
        (IsSurreal.isSurreal_right sa haR)
        (IsSurreal.isSurreal_left sb hbL)
        (IsSurreal.isSurreal_left sc hcL)

    · -- branch (aR, bR, cR)
      let abL : Game := Game.mulOpt4 aR b a bR
      have habL : abL ∈ (a ⊗ b).left := by
        dsimp [abL]
        exact mem_mul_left_rr haR hbR
      refine ⟨Game.mulOpt4 abL c (a ⊗ b) cR, mem_mul_right_lr habL hcR, ?_⟩
      dsimp [abL]
      exact Game.eq_symm <| hassoc
        (a₀ := aR) (b₀ := bR) (c₀ := cR)
        (Game.birthday_lt_right haR)
        (Game.birthday_lt_right hbR)
        (Game.birthday_lt_right hcR)
        (IsSurreal.isSurreal_right sa haR)
        (IsSurreal.isSurreal_right sb hbR)
        (IsSurreal.isSurreal_right sc hcR)

/-! ### Main theorem -/

private lemma T_of_assoc_bounds
    {a b c a' b' c' : Game}
    (ha' : a'.birthday ≤ a.birthday)
    (hb' : b'.birthday ≤ b.birthday)
    (hc' : c'.birthday ≤ c.birthday)
    (hstrict :
      a'.birthday < a.birthday ∨
        b'.birthday < b.birthday ∨
          c'.birthday < c.birthday) :
    T ⟨a', b', c'⟩ ⟨a, b, c⟩ := by
  rcases hstrict with ha_strict | hb_strict | hc_strict
  · have h_ab₁ :
        a'.birthday + b'.birthday < a.birthday + b'.birthday :=
      Nat.add_lt_add_right ha_strict b'.birthday
    have h_ab₂ :
        a.birthday + b'.birthday ≤ a.birthday + b.birthday :=
      Nat.add_le_add_left hb' a.birthday
    have h_ab :
        a'.birthday + b'.birthday < a.birthday + b.birthday :=
      _root_.lt_of_lt_of_le h_ab₁ h_ab₂

    have h_sum₁ :
        (a'.birthday + b'.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c'.birthday :=
      Nat.add_lt_add_right h_ab c'.birthday
    have h_sum₂ :
        (a.birthday + b.birthday) + c'.birthday ≤
          (a.birthday + b.birthday) + c.birthday :=
      Nat.add_le_add_left hc' (a.birthday + b.birthday)
    have h_sum :
        (a'.birthday + b'.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c.birthday :=
      _root_.lt_of_lt_of_le h_sum₁ h_sum₂

    simpa [T, Nat.add_assoc] using h_sum

  · have h_ab₁ :
        a'.birthday + b'.birthday ≤ a.birthday + b'.birthday :=
      Nat.add_le_add_right ha' b'.birthday
    have h_ab₂ :
        a.birthday + b'.birthday < a.birthday + b.birthday :=
      Nat.add_lt_add_left hb_strict a.birthday
    have h_ab :
        a'.birthday + b'.birthday < a.birthday + b.birthday :=
      _root_.lt_of_le_of_lt h_ab₁ h_ab₂

    have h_sum₁ :
        (a'.birthday + b'.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c'.birthday :=
      Nat.add_lt_add_right h_ab c'.birthday
    have h_sum₂ :
        (a.birthday + b.birthday) + c'.birthday ≤
          (a.birthday + b.birthday) + c.birthday :=
      Nat.add_le_add_left hc' (a.birthday + b.birthday)
    have h_sum :
        (a'.birthday + b'.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c.birthday :=
      _root_.lt_of_lt_of_le h_sum₁ h_sum₂

    simpa [T, Nat.add_assoc] using h_sum

  · have h_ab₁ :
        a'.birthday + b'.birthday ≤ a.birthday + b'.birthday :=
      Nat.add_le_add_right ha' b'.birthday
    have h_ab₂ :
        a.birthday + b'.birthday ≤ a.birthday + b.birthday :=
      Nat.add_le_add_left hb' a.birthday
    have h_ab :
        a'.birthday + b'.birthday ≤ a.birthday + b.birthday :=
      _root_.le_trans h_ab₁ h_ab₂

    have h_sum₁ :
        (a'.birthday + b'.birthday) + c'.birthday ≤
          (a.birthday + b.birthday) + c'.birthday :=
      Nat.add_le_add_right h_ab c'.birthday
    have h_sum₂ :
        (a.birthday + b.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c.birthday :=
      Nat.add_lt_add_left hc_strict (a.birthday + b.birthday)
    have h_sum :
        (a'.birthday + b'.birthday) + c'.birthday <
          (a.birthday + b.birthday) + c.birthday :=
      _root_.lt_of_le_of_lt h_sum₁ h_sum₂

    simpa [T, Nat.add_assoc] using h_sum


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
    exact IH ⟨a', b', c'⟩
      (T_of_assoc_bounds
        (a := a) (b := b) (c := c)
        (a' := a') (b' := b') (c' := c')
        ha' hb' hc' hstrict)
      sa' sb' sc'

  refine Game.eq_of_equiv_options
    (fun L hL => left_option_mul_assoc sa sb sc IHsmall hL)
    (fun L hL => left_option_mul_assoc_symm sa sb sc IHsmall hL)
    (fun R hR => right_option_mul_assoc sa sb sc IHsmall hR)
    (fun R hR => right_option_mul_assoc_symm sa sb sc IHsmall hR)

end Game
