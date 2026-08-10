import Mathlib.Tactic.Linarith
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm
import Surreal.Mult_dist
import Surreal.CommGroup
import Surreal.Order
import Surreal.MulOpt

open Multiset
open Game

namespace Conway

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y


/-
  Conway A/B/C, but with the corrected 3-variable C:

    A(x,y) : x*y is surreal.
    B(x1,x2,y) : x1 ∼ x2 -> x1*y ∼ x2*y.
    C(x1,x2,y) : x1 ≺ x2 ->
      (forall yL ∈ y.left,  x1*y + x2*yL < x1*yL + x2*y)  and
      (forall yR ∈ y.right, x1*yR + x2*y < x1*y + x2*yR).
  which is the CLeft and CRight conditions on the `mulOpt` file.
  The whole file is arranged as one simultaneous well-founded induction on the
  Dershowitz–Manna order of multisets of birthdays.
-/

/-! ### DM measure on birthdays

The shared `Goal`, `μGoal`, `GoalLT`, and `wfGoal` declarations from
`Surreal.Order` drive the simultaneous induction below.
-/

abbrev CConditions (x1 x2 y : Game) : Prop :=
  (∀ yL ∈ y.left, CLeft x1 x2 y yL) ∧
  (∀ yR ∈ y.right, CRight x1 x2 y yR)

def Holds : Goal → Prop
  | .A x y =>
      IsSurreal x → IsSurreal y → IsSurreal (x ⊗ y)
  | .B x1 x2 y =>
      IsSurreal x1 → IsSurreal x2 → IsSurreal y →
      x1 ∼ x2 → (x1 ⊗ y) ∼ (x2 ⊗ y)
  | .C x1 x2 y =>
      IsSurreal x1 → IsSurreal x2 → IsSurreal y →
      x1 ≺ x2 → CConditions x1 x2 y

/-! ### Small wrappers around existing APIs -/

def asSurreal (x : Game) (hx : IsSurreal x) : Surreal := ⟨x, hx⟩

lemma trichotomy_game {x y : Game} (sx : IsSurreal x) (sy : IsSurreal y) :
    x ≺ y ∨ x ∼ y ∨ y ≺ x := by
  simpa using (Surreal.trichotomy (x := asSurreal x sx) (y := asSurreal y sy))

lemma add_isSurreal_game {a b : Game} (ha : IsSurreal a) (hb : IsSurreal b) :
    IsSurreal (a ⊕ b) := by
  simpa using (Surreal.add_isSurreal (a := asSurreal a ha) (b := asSurreal b hb))

lemma neg_isSurreal_game {a : Game} (ha : IsSurreal a) :
    IsSurreal a.neg := by
  simpa using (Surreal.neg_isSurreal (a := asSurreal a ha))

lemma left_lt_game {x xL : Game} (sx : IsSurreal x) (hxL : xL ∈ x.left) :
    xL ≺ x := by
  exact IsSurreal.left_lt sx hxL

lemma lt_right_game {x xR : Game} (sx : IsSurreal x) (hxR : xR ∈ x.right) :
    x ≺ xR := by
  exact IsSurreal.lt_right sx hxR

lemma left_lt_right_game {x xL xR : Game}
    (sx : IsSurreal x) (hxL : xL ∈ x.left) (hxR : xR ∈ x.right) :
    xL ≺ xR := by
  exact Game.lt_trans ⟨left_lt_game sx hxL, lt_right_game sx hxR⟩

lemma mul_eq_mul_left_of_mul_eq_mul_right {x y1 y2 : Game}
    (h : (y1 ⊗ x) ∼ (y2 ⊗ x)) :
    (x ⊗ y1) ∼ (x ⊗ y2) := by
  exact Game.eq_trans ⟨
    Game.mul_comm,
    Game.eq_trans ⟨h, Game.eq_symm Game.mul_comm⟩⟩

/-
  Strict version of the rearrangement lemma
    (((a ⊕ b) ⊕ c.neg) ≺ d) ↔ (a ⊕ b) ≺ (d ⊕ c).

  If you keep your earlier `P_ineq_rearrange` / `sub_le_iff` lemma, prove this once
  and use it everywhere in the branch algebra.
-/
private lemma add_neg_add_cancel (x c : Game) : ((x ⊕ c.neg) ⊕ c).eq x := by
  apply Game.eq_of_q_eq
  change (⟦((x ⊕ c.neg) ⊕ c)⟧ : Game.GameQ) = ⟦x⟧
  simp

private lemma add_add_neg_cancel (x c : Game) : ((x ⊕ c) ⊕ c.neg).eq x := by
  apply Game.eq_of_q_eq
  change (⟦((x ⊕ c) ⊕ c.neg)⟧ : Game.GameQ) = ⟦x⟧
  simp

lemma lt_rearrange_neg {a b c d : Game} :
    (((a ⊕ b) ⊕ c.neg) ≺ d) ↔ (a ⊕ b) ≺ (d ⊕ c) := by
  rw [Game.lt, Game.lt]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · exact Game.le_trans ⟨(add_neg_add_cancel (a ⊕ b) c).2, Game.add_le_add_right h₁⟩
    · intro hcontra
      exact h₂ (Game.le_trans ⟨(add_add_neg_cancel d c).2, Game.add_le_add_right hcontra⟩)
  · rintro ⟨h₁, h₂⟩
    constructor
    · exact Game.le_trans ⟨Game.add_le_add_right h₁, (add_add_neg_cancel d c).1⟩
    · intro hcontra
      exact h₂ (Game.le_trans ⟨Game.add_le_add_right hcontra, (add_neg_add_cancel (a ⊕ b) c).1⟩)



/-
  Bridge extraction from `x1 ≺ x2`:

  either there is a right option `x1R` with `x1R ≼ x2`,
  or there is a left option `x2L` with `x1 ≼ x2L`.
-/
lemma bridge_exists_of_lt {x1 x2 : Game} (h : x1 ≺ x2) :
    (∃ x1R ∈ x1.right, x1R ≼ x2) ∨
    (∃ x2L ∈ x2.left, x1 ≼ x2L) := by
  classical
  by_contra hBridge
  apply h.2
  unfold Game.le
  constructor
  · intro x2L hx2L hxle
    exact hBridge (Or.inr ⟨x2L, hx2L, hxle⟩)
  · intro x1R hx1R hxle
    exact hBridge (Or.inl ⟨x1R, hx1R, hxle⟩)

/-
  These are the two bridge lemmas used in the strict-bridge cases of C:
  compose C(x1,xm,y) and C(xm,x2,y) into C(x1,x2,y).
-/


/-! ### A-case helpers -/

private structure AContext (x y : Game) : Prop where
  ih : ∀ g', GoalLT g' (.A x y) → Holds g'
  sx : IsSurreal x
  sy : IsSurreal y

private lemma goal_lt_A_both
    {x x' y y' : Game}
    (hx' : Game.birthday x' < Game.birthday x)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.A x' y') (.A x y) := by
  exact IsDershowitzMannaLT.trans
    (goal_lt_A₁ (x := x) (x' := x') (y := y') hx')
    (goal_lt_A₂ (x := x) (y := y) (y' := y') hy')

private lemma A_mulOpt_isSurreal
    {x y : Game} (ctx : AContext x y) (x' y' : Game)
    (sx' : IsSurreal x') (sy' : IsSurreal y')
    (hx' : Game.birthday x' < Game.birthday x)
    (hy' : Game.birthday y' < Game.birthday y) :
    IsSurreal (M x' y x y') := by
  simpa [M, Game.mulOpt4] using
    add_isSurreal_game
      (add_isSurreal_game
        ((ctx.ih (.A x' y) (goal_lt_A₁ hx')) sx' ctx.sy)
        ((ctx.ih (.A x y') (goal_lt_A₂ hy')) ctx.sx sy'))
      (neg_isSurreal_game ((ctx.ih (.A x' y') (goal_lt_A_both hx' hy')) sx' sy'))

private lemma A_option_isSurreal_left
    {x y : Game} (ctx : AContext x y)
    {L : Game} (hL : L ∈ (x ⊗ y).left) :
    IsSurreal L := by
  rw [mem_mul_left] at hL
  rcases hL with ⟨xl, hxl, yl, hyl, rfl⟩ | ⟨xr, hxr, yr, hyr, rfl⟩
  · exact A_mulOpt_isSurreal ctx xl yl
      (IsSurreal.isSurreal_left ctx.sx hxl) (IsSurreal.isSurreal_left ctx.sy hyl)
      (Game.birthday_lt_left hxl) (Game.birthday_lt_left hyl)
  · exact A_mulOpt_isSurreal ctx xr yr
      (IsSurreal.isSurreal_right ctx.sx hxr) (IsSurreal.isSurreal_right ctx.sy hyr)
      (Game.birthday_lt_right hxr) (Game.birthday_lt_right hyr)

private lemma A_option_isSurreal_right
    {x y : Game} (ctx : AContext x y)
    {R : Game} (hR : R ∈ (x ⊗ y).right) :
    IsSurreal R := by
  rw [mem_mul_right] at hR
  rcases hR with ⟨xl, hxl, yr, hyr, rfl⟩ | ⟨xr, hxr, yl, hyl, rfl⟩
  · exact A_mulOpt_isSurreal ctx xl yr
      (IsSurreal.isSurreal_left ctx.sx hxl) (IsSurreal.isSurreal_right ctx.sy hyr)
      (Game.birthday_lt_left hxl) (Game.birthday_lt_right hyr)
  · exact A_mulOpt_isSurreal ctx xr yl
      (IsSurreal.isSurreal_right ctx.sx hxr) (IsSurreal.isSurreal_left ctx.sy hyl)
      (Game.birthday_lt_right hxr) (Game.birthday_lt_left hyl)


/-! ### Four branch-family lemmas -/

private lemma AContext.c_x
    {x y x₁ x₂ : Game} (ctx : AContext x y)
    (hx₁ : x₁ ∈ x.left ∨ x₁ ∈ x.right)
    (hx₂ : x₂ ∈ x.left ∨ x₂ ∈ x.right)
    (h : x₁ ≺ x₂) :
    CConditions x₁ x₂ y := by
  exact (ctx.ih (.C x₁ x₂ y)
    (goal_lt_C_from_A (Game.birthday_lt_of_isOption hx₁) (Game.birthday_lt_of_isOption hx₂)))
    (IsSurreal.isSurreal_option ctx.sx hx₁) (IsSurreal.isSurreal_option ctx.sx hx₂) ctx.sy h

private lemma AContext.c_y
    {x y y₁ y₂ : Game} (ctx : AContext x y)
    (hy₁ : y₁ ∈ y.left ∨ y₁ ∈ y.right)
    (hy₂ : y₂ ∈ y.left ∨ y₂ ∈ y.right)
    (h : y₁ ≺ y₂) :
    CConditions y₁ y₂ x := by
  exact (ctx.ih (.C y₁ y₂ x)
    (goal_lt_C_from_A' (Game.birthday_lt_of_isOption hy₁) (Game.birthday_lt_of_isOption hy₂)))
    (IsSurreal.isSurreal_option ctx.sy hy₁) (IsSurreal.isSurreal_option ctx.sy hy₂) ctx.sx h

private lemma AContext.b_x
    {x y x₁ x₂ : Game} (ctx : AContext x y)
    (hx₁ : x₁ ∈ x.left ∨ x₁ ∈ x.right)
    (hx₂ : x₂ ∈ x.left ∨ x₂ ∈ x.right)
    (h : x₁ ∼ x₂) :
    (x₁ ⊗ y) ∼ (x₂ ⊗ y) := by
  exact (ctx.ih (.B x₁ x₂ y)
    (goal_lt_B_from_A (Game.birthday_lt_of_isOption hx₁) (Game.birthday_lt_of_isOption hx₂)))
    (IsSurreal.isSurreal_option ctx.sx hx₁) (IsSurreal.isSurreal_option ctx.sx hx₂) ctx.sy h

private lemma AContext.b_x_option
    {x y x₁ x₂ y' : Game} (ctx : AContext x y)
    (hx₁ : x₁ ∈ x.left ∨ x₁ ∈ x.right)
    (hx₂ : x₂ ∈ x.left ∨ x₂ ∈ x.right)
    (hy' : y' ∈ y.left ∨ y' ∈ y.right)
    (h : x₁ ∼ x₂) :
    (x₁ ⊗ y') ∼ (x₂ ⊗ y') := by
  exact (ctx.ih (.B x₁ x₂ y')
    (goal_lt_B_from_A_mixed
      (Game.birthday_lt_of_isOption hx₁)
      (Game.birthday_lt_of_isOption hx₂)
      (Game.birthday_lt_of_isOption hy')))
    (IsSurreal.isSurreal_option ctx.sx hx₁)
    (IsSurreal.isSurreal_option ctx.sx hx₂)
    (IsSurreal.isSurreal_option ctx.sy hy') h

private lemma AContext.b_y
    {x y y₁ y₂ : Game} (ctx : AContext x y)
    (hy₁ : y₁ ∈ y.left ∨ y₁ ∈ y.right)
    (hy₂ : y₂ ∈ y.left ∨ y₂ ∈ y.right)
    (h : y₁ ∼ y₂) :
    (y₁ ⊗ x) ∼ (y₂ ⊗ x) := by
  exact (ctx.ih (.B y₁ y₂ x)
    (goal_lt_B_from_A' (Game.birthday_lt_of_isOption hy₁) (Game.birthday_lt_of_isOption hy₂)))
    (IsSurreal.isSurreal_option ctx.sy hy₁) (IsSurreal.isSurreal_option ctx.sy hy₂) ctx.sx h

private lemma AContext.b_y_option
    {x y y₁ y₂ x' : Game} (ctx : AContext x y)
    (hy₁ : y₁ ∈ y.left ∨ y₁ ∈ y.right)
    (hy₂ : y₂ ∈ y.left ∨ y₂ ∈ y.right)
    (hx' : x' ∈ x.left ∨ x' ∈ x.right)
    (h : y₁ ∼ y₂) :
    (y₁ ⊗ x') ∼ (y₂ ⊗ x') := by
  exact (ctx.ih (.B y₁ y₂ x')
    (goal_lt_B_from_A_mixed'
      (Game.birthday_lt_of_isOption hy₁)
      (Game.birthday_lt_of_isOption hy₂)
      (Game.birthday_lt_of_isOption hx')))
    (IsSurreal.isSurreal_option ctx.sy hy₁)
    (IsSurreal.isSurreal_option ctx.sy hy₂)
    (IsSurreal.isSurreal_option ctx.sx hx') h

/-- Family `LL` versus `LR`: `(xL₁,yL)` versus `(xL₂,yR)`. -/
private lemma A_left_lt_right_LL
    {x y : Game} (ctx : AContext x y)
    {xL₁ xL₂ yL yR : Game}
    (hxL₁ : xL₁ ∈ x.left) (hxL₂ : xL₂ ∈ x.left)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right) :
    M xL₁ y x yL ≺ M xL₂ y x yR := by
  rcases trichotomy_game
      (IsSurreal.isSurreal_option ctx.sx (Or.inl hxL₁))
      (IsSurreal.isSurreal_option ctx.sx (Or.inl hxL₂)) with hlt | heq | hgt
  · exact Game.lt_trans ⟨
      mulOpt4_move_x_left_to_right ((ctx.c_x (Or.inl hxL₁) (Or.inl hxL₂) hlt).1 yL hyL),
      mulOpt4_move_y_left_to_right
        ((ctx.c_y (Or.inl hyL) (Or.inr hyR) (left_lt_right_game ctx.sy hyL hyR)).1 xL₂ hxL₂)⟩
  · exact Game.lt_of_lt_of_le
      (mulOpt4_move_y_left_to_right
        ((ctx.c_y (Or.inl hyL) (Or.inr hyR) (left_lt_right_game ctx.sy hyL hyR)).1 xL₁ hxL₁))
      (mulOpt4_congr_xslot
        (ctx.b_x (Or.inl hxL₁) (Or.inl hxL₂) heq)
        (ctx.b_x_option (Or.inl hxL₁) (Or.inl hxL₂) (Or.inr hyR) heq)).1
  · exact Game.lt_trans ⟨
      mulOpt4_move_y_left_to_right
        ((ctx.c_y (Or.inl hyL) (Or.inr hyR) (left_lt_right_game ctx.sy hyL hyR)).1 xL₁ hxL₁),
      mulOpt4_move_x_right_to_left ((ctx.c_x (Or.inl hxL₂) (Or.inl hxL₁) hgt).2 yR hyR)⟩

/-- Family `LL` versus `RL`: `(xL,yL₁)` versus `(xR,yL₂)`. -/
private lemma A_left_lt_right_LR
    {x y : Game} (ctx : AContext x y)
    {xL xR yL₁ yL₂ : Game}
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL₁ : yL₁ ∈ y.left) (hyL₂ : yL₂ ∈ y.left) :
    M xL y x yL₁ ≺ M xR y x yL₂ := by
  rcases trichotomy_game
      (IsSurreal.isSurreal_option ctx.sy (Or.inl hyL₁))
      (IsSurreal.isSurreal_option ctx.sy (Or.inl hyL₂)) with hlt | heq | hgt
  · exact Game.lt_trans ⟨
      mulOpt4_move_y_left_to_right ((ctx.c_y (Or.inl hyL₁) (Or.inl hyL₂) hlt).1 xL hxL),
      mulOpt4_move_x_left_to_right
        ((ctx.c_x (Or.inl hxL) (Or.inr hxR) (left_lt_right_game ctx.sx hxL hxR)).1 yL₂ hyL₂)⟩
  · exact Game.lt_of_lt_of_le
      (mulOpt4_move_x_left_to_right
        ((ctx.c_x (Or.inl hxL) (Or.inr hxR) (left_lt_right_game ctx.sx hxL hxR)).1 yL₁ hyL₁))
      (mulOpt4_congr_yslot
        (mul_eq_mul_left_of_mul_eq_mul_right
          (ctx.b_y_option (Or.inl hyL₁) (Or.inl hyL₂) (Or.inr hxR) heq))
        (mul_eq_mul_left_of_mul_eq_mul_right
          (ctx.b_y (Or.inl hyL₁) (Or.inl hyL₂) heq))).1
  · exact Game.lt_trans ⟨
      mulOpt4_move_x_left_to_right
        ((ctx.c_x (Or.inl hxL) (Or.inr hxR) (left_lt_right_game ctx.sx hxL hxR)).1 yL₁ hyL₁),
      mulOpt4_move_y_right_to_left ((ctx.c_y (Or.inl hyL₂) (Or.inl hyL₁) hgt).2 xR hxR)⟩



/-- Family `RR` versus `LR`: `(xR₁,yR₁)` versus `(xL₂,yR₂)`. -/
private lemma A_left_lt_right_RL
    {x y : Game} (ctx : AContext x y)
    {xR₁ xL₂ yR₁ yR₂ : Game}
    (hxR₁ : xR₁ ∈ x.right) (hxL₂ : xL₂ ∈ x.left)
    (hyR₁ : yR₁ ∈ y.right) (hyR₂ : yR₂ ∈ y.right) :
    M xR₁ y x yR₁ ≺ M xL₂ y x yR₂ := by
  rcases trichotomy_game
      (IsSurreal.isSurreal_option ctx.sy (Or.inr hyR₁))
      (IsSurreal.isSurreal_option ctx.sy (Or.inr hyR₂)) with hlt | heq | hgt
  · exact Game.lt_trans ⟨
      mulOpt4_move_x_right_to_left
        ((ctx.c_x (Or.inl hxL₂) (Or.inr hxR₁) (left_lt_right_game ctx.sx hxL₂ hxR₁)).2 yR₁ hyR₁),
      mulOpt4_move_y_left_to_right ((ctx.c_y (Or.inr hyR₁) (Or.inr hyR₂) hlt).1 xL₂ hxL₂)⟩
  · exact Game.lt_of_lt_of_le
      (mulOpt4_move_x_right_to_left
        ((ctx.c_x (Or.inl hxL₂) (Or.inr hxR₁) (left_lt_right_game ctx.sx hxL₂ hxR₁)).2 yR₁ hyR₁))
      (mulOpt4_congr_yslot
        (mul_eq_mul_left_of_mul_eq_mul_right
          (ctx.b_y_option (Or.inr hyR₁) (Or.inr hyR₂) (Or.inl hxL₂) heq))
        (mul_eq_mul_left_of_mul_eq_mul_right
          (ctx.b_y (Or.inr hyR₁) (Or.inr hyR₂) heq))).1
  · exact Game.lt_trans ⟨
      mulOpt4_move_y_right_to_left ((ctx.c_y (Or.inr hyR₂) (Or.inr hyR₁) hgt).2 xR₁ hxR₁),
      mulOpt4_move_x_right_to_left
        ((ctx.c_x (Or.inl hxL₂) (Or.inr hxR₁) (left_lt_right_game ctx.sx hxL₂ hxR₁)).2 yR₂ hyR₂)⟩

/-- Family `RR` versus `RL`: `(xR₁,yR₁)` versus `(xR₂,yL₂)`. -/
private lemma A_left_lt_right_RR
    {x y : Game} (ctx : AContext x y)
    {xR₁ xR₂ yR₁ yL₂ : Game}
    (hxR₁ : xR₁ ∈ x.right) (hxR₂ : xR₂ ∈ x.right)
    (hyR₁ : yR₁ ∈ y.right) (hyL₂ : yL₂ ∈ y.left) :
    M xR₁ y x yR₁ ≺ M xR₂ y x yL₂ := by
  rcases trichotomy_game
      (IsSurreal.isSurreal_option ctx.sx (Or.inr hxR₁))
      (IsSurreal.isSurreal_option ctx.sx (Or.inr hxR₂)) with hlt | heq | hgt
  · exact Game.lt_trans ⟨
      mulOpt4_move_y_right_to_left
        ((ctx.c_y (Or.inl hyL₂) (Or.inr hyR₁) (left_lt_right_game ctx.sy hyL₂ hyR₁)).2 xR₁ hxR₁),
      mulOpt4_move_x_left_to_right ((ctx.c_x (Or.inr hxR₁) (Or.inr hxR₂) hlt).1 yL₂ hyL₂)⟩
  · exact Game.lt_of_lt_of_le
      (mulOpt4_move_y_right_to_left
        ((ctx.c_y (Or.inl hyL₂) (Or.inr hyR₁) (left_lt_right_game ctx.sy hyL₂ hyR₁)).2 xR₁ hxR₁))
      (mulOpt4_congr_xslot
        (ctx.b_x (Or.inr hxR₁) (Or.inr hxR₂) heq)
        (ctx.b_x_option (Or.inr hxR₁) (Or.inr hxR₂) (Or.inl hyL₂) heq)).1
  · exact Game.lt_trans ⟨
      mulOpt4_move_x_right_to_left ((ctx.c_x (Or.inr hxR₂) (Or.inr hxR₁) hgt).2 yR₁ hyR₁),
      mulOpt4_move_y_right_to_left
        ((ctx.c_y (Or.inl hyL₂) (Or.inr hyR₁) (left_lt_right_game ctx.sy hyL₂ hyR₁)).2 xR₂ hxR₂)⟩

private lemma A_left_lt_right
    {x y : Game} (ctx : AContext x y)
    {L R : Game}
    (hL : L ∈ (x ⊗ y).left)
    (hR : R ∈ (x ⊗ y).right) :
    L ≺ R := by
  rw [mem_mul_left] at hL
  rw [mem_mul_right] at hR
  rcases hL with
    ⟨xL₁, hxL₁, yL₁, hyL₁, rfl⟩ | ⟨xR₁, hxR₁, yR₁, hyR₁, rfl⟩
  · rcases hR with
      ⟨xL₂, hxL₂, yR₂, hyR₂, rfl⟩ | ⟨xR₂, hxR₂, yL₂, hyL₂, rfl⟩
    · simpa [M] using A_left_lt_right_LL ctx hxL₁ hxL₂ hyL₁ hyR₂
    · simpa [M] using A_left_lt_right_LR ctx hxL₁ hxR₂ hyL₁ hyL₂
  · rcases hR with
      ⟨xL₂, hxL₂, yR₂, hyR₂, rfl⟩ | ⟨xR₂, hxR₂, yL₂, hyL₂, rfl⟩
    · simpa [M] using A_left_lt_right_RL ctx hxR₁ hxL₂ hyR₁ hyR₂
    · simpa [M] using A_left_lt_right_RR ctx hxR₁ hxR₂ hyR₁ hyL₂

private lemma A_product_isSurreal
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y) :
    IsSurreal (x ⊗ y) := by
  let ctx : AContext x y := ⟨IH, sx, sy⟩
  unfold IsSurreal
  refine ⟨?_, ?_⟩
  · intro L hL R hR
    exact (A_left_lt_right ctx hL hR).2
  · constructor
    · intro L hL
      exact A_option_isSurreal_left ctx hL
    · intro R hR
      exact A_option_isSurreal_right ctx hR



/-! ### B-case helper -/

private lemma μGoal_B_swap (x1 x2 y : Game) :
    μGoal (.B x1 x2 y) = μGoal (.B x2 x1 y) := by
  simp [μGoal, μB, Multiset.insert_eq_cons, Multiset.cons_swap]

private lemma goal_lt_transport_right
    {gTop₁ gTop₂ g' : Goal}
    (hμ : μGoal gTop₁ = μGoal gTop₂) :
    GoalLT g' gTop₁ → GoalLT g' gTop₂ := by
  intro hg
  simpa [GoalLT, InvImage, hμ] using hg

private lemma IHswap_of_IH
    {x1 x2 y : Game}
    (IH : ∀ g', GoalLT g' (.B x1 x2 y) → Holds g') :
    ∀ g', GoalLT g' (.B x2 x1 y) → Holds g' := by
  intro g' hg'
  exact IH g' (goal_lt_transport_right (μGoal_B_swap x2 x1 y) hg')

private structure BContext (a b y : Game) : Prop where
  ih : ∀ g', GoalLT g' (.B a b y) → Holds g'
  sa : IsSurreal a
  sb : IsSurreal b
  sy : IsSurreal y
  hEq : a ∼ b

private def BContext.swap {a b y : Game} (ctx : BContext a b y) :
    BContext b a y :=
  ⟨IHswap_of_IH ctx.ih, ctx.sb, ctx.sa, ctx.sy, Game.eq_symm ctx.hEq⟩

private lemma BContext.b_option
    {a b y y' : Game} (ctx : BContext a b y)
    (hy' : y' ∈ y.left ∨ y' ∈ y.right) :
    (a ⊗ y') ∼ (b ⊗ y') := by
  exact (ctx.ih (.B a b y') (goal_lt_B₃ (Game.birthday_lt_of_isOption hy')))
    ctx.sa ctx.sb (IsSurreal.isSurreal_option ctx.sy hy') ctx.hEq

private lemma BContext.b_option_swap
    {a b y y' : Game} (ctx : BContext a b y)
    (hy' : y' ∈ y.left ∨ y' ∈ y.right) :
    (b ⊗ y') ∼ (a ⊗ y') := by
  exact Game.eq_symm (ctx.b_option hy')

private lemma BContext.c_left_left
    {a b y aL : Game} (ctx : BContext a b y) (haL : aL ∈ a.left) :
    CConditions aL b y := by
  exact (ctx.ih (.C aL b y) (goal_lt_C_from_B_left_left (Game.birthday_lt_left haL)))
    (IsSurreal.isSurreal_left ctx.sa haL) ctx.sb ctx.sy
    (Game.lt_of_lt_of_le (left_lt_game ctx.sa haL) ctx.hEq.1)

private lemma BContext.c_left_right
    {a b y aR : Game} (ctx : BContext a b y) (haR : aR ∈ a.right) :
    CConditions b aR y := by
  exact (ctx.ih (.C b aR y) (goal_lt_C_from_B_left_right (Game.birthday_lt_right haR)))
    ctx.sb (IsSurreal.isSurreal_right ctx.sa haR) ctx.sy
    (Game.lt_of_le_of_lt ctx.hEq.2 (lt_right_game ctx.sa haR))

private lemma BContext.c_right_left
    {a b y bL : Game} (ctx : BContext a b y) (hbL : bL ∈ b.left) :
    CConditions bL a y := by
  exact (ctx.ih (.C bL a y) (goal_lt_C_from_B_right_left (Game.birthday_lt_left hbL)))
    (IsSurreal.isSurreal_left ctx.sb hbL) ctx.sa ctx.sy
    (Game.lt_of_lt_of_le (left_lt_game ctx.sb hbL) ctx.hEq.2)

private lemma BContext.c_right_right
    {a b y bR : Game} (ctx : BContext a b y) (hbR : bR ∈ b.right) :
    CConditions a bR y := by
  exact (ctx.ih (.C a bR y) (goal_lt_C_from_B_right_right (Game.birthday_lt_right hbR)))
    ctx.sa (IsSurreal.isSurreal_right ctx.sb hbR) ctx.sy
    (Game.lt_of_le_of_lt ctx.hEq.1 (lt_right_game ctx.sb hbR))

private lemma B_product_le
    {a b y : Game} (ctx : BContext a b y) :
    (a ⊗ y) ≼ (b ⊗ y) := by
  unfold Game.le
  constructor
  · intro L hL
    rw [mem_mul_left] at hL
    rcases hL with
      ⟨aL, haL, yL, hyL, rfl⟩ | ⟨aR, haR, yR, hyR, rfl⟩
    · exact
        (mulOpt4_LL_lt_product (ctx.b_option (Or.inl hyL)) ((ctx.c_left_left haL).1 yL hyL)).2
    · exact
        (mulOpt4_RR_lt_product (ctx.b_option (Or.inr hyR)) ((ctx.c_left_right haR).2 yR hyR)).2
  · intro R hR
    rw [mem_mul_right] at hR
    rcases hR with
      ⟨bL, hbL, yR, hyR, rfl⟩ | ⟨bR, hbR, yL, hyL, rfl⟩
    · exact
        (product_lt_mulOpt4_LR (ctx.b_option_swap (Or.inr hyR)) ((ctx.c_right_left hbL).2 yR hyR)).2
    · exact
        (product_lt_mulOpt4_RL
          (ctx.b_option_swap (Or.inl hyL)) ((ctx.c_right_right hbR).1 yL hyL)).2

/-! #### Final B theorem -/

private lemma B_product_eq
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.B x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hEq : x1 ∼ x2) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  let ctx : BContext x1 x2 y := ⟨IH, sx1, sx2, sy, hEq⟩
  exact ⟨B_product_le ctx, B_product_le ctx.swap⟩




/-! ### C-case helper -/


private lemma C_compose
    {x1 xm x2 y : Game}
    (h1 : CConditions x1 xm y)
    (h2 : CConditions xm x2 y) :
    CConditions x1 x2 y := by
  exact ⟨fun yL hyL => C_compose_left (h1.1 yL hyL) (h2.1 yL hyL),
    fun yR hyR => C_compose_right (h1.2 yR hyR) (h2.2 yR hyR)⟩

private lemma C_replace_right_endpoint
    (x1 xm x2 y : Game)
    (IH : ∀ g', GoalLT g' (.C x1 x2 y) → Holds g')
    (sxm : IsSurreal xm) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (bxm : Game.birthday xm < Game.birthday x1)
    (hEq : xm ∼ x2)
    (hAdj : CConditions x1 xm y) :
    CConditions x1 x2 y := by
  have hBy : (xm ⊗ y) ∼ (x2 ⊗ y) := by
    exact (IH (.B xm x2 y) (goal_lt_B_from_C_left bxm)) sxm sx2 sy hEq
  constructor
  · intro yL hyL
    exact C_replace_eq_left
      ((IH (.B xm x2 yL)
        (goal_lt_B_from_C_left_mixed bxm (Game.birthday_lt_left hyL)))
        sxm sx2 (IsSurreal.isSurreal_left sy hyL) hEq)
      hBy (hAdj.1 yL hyL)
  · intro yR hyR
    exact C_replace_eq_right
      ((IH (.B xm x2 yR)
        (goal_lt_B_from_C_left_mixed bxm (Game.birthday_lt_right hyR)))
        sxm sx2 (IsSurreal.isSurreal_right sy hyR) hEq)
      hBy (hAdj.2 yR hyR)

private lemma C_replace_left_endpoint
    (x1 xm x2 y : Game)
    (IH : ∀ g', GoalLT g' (.C x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sxm : IsSurreal xm) (sy : IsSurreal y)
    (bxm : Game.birthday xm < Game.birthday x2)
    (hEq : x1 ∼ xm)
    (hAdj : CConditions xm x2 y) :
    CConditions x1 x2 y := by
  have hBy : (x1 ⊗ y) ∼ (xm ⊗ y) := by
    exact (IH (.B x1 xm y) (goal_lt_B_from_C_right bxm)) sx1 sxm sy hEq
  constructor
  · intro yL hyL
    exact C_replace_eq_left_first
      ((IH (.B x1 xm yL)
        (goal_lt_B_from_C_right_mixed bxm (Game.birthday_lt_left hyL)))
        sx1 sxm (IsSurreal.isSurreal_left sy hyL) hEq)
      hBy (hAdj.1 yL hyL)
  · intro yR hyR
    exact C_replace_eq_right_first
      ((IH (.B x1 xm yR)
        (goal_lt_B_from_C_right_mixed bxm (Game.birthday_lt_right hyR)))
        sx1 sxm (IsSurreal.isSurreal_right sy hyR) hEq)
      hBy (hAdj.2 yR hyR)

private lemma C_core
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.C x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hLt : x1 ≺ x2) :
    CConditions x1 x2 y := by
  rcases bridge_exists_of_lt hLt with hbridge | hbridge

  · /- Case A: ∃ x1R ∈ x1.right, x1R ≼ x2 -/
    rcases hbridge with ⟨x1R, hx1R, hle⟩
    have sx1R : IsSurreal x1R := IsSurreal.isSurreal_right sx1 hx1R
    have bx1R : Game.birthday x1R < Game.birthday x1 := Game.birthday_lt_right hx1R

    have hAdj :
        CConditions x1 x1R y := by
      exact adjacentC_right_of_A ((IH (.A x1 y) goal_lt_A_from_C₁) sx1 sy) hx1R

    rcases trichotomy_game sx1R sx2 with hltR | heqR | hgtR

    · /- A2: x1R ≺ x2 -/
      exact C_compose hAdj ((IH (.C x1R x2 y) (goal_lt_C₁ bx1R)) sx1R sx2 sy hltR)

    · /- A1: x1R ∼ x2 -/
      exact C_replace_right_endpoint x1 x1R x2 y IH sx1R sx2 sy bx1R heqR hAdj

    · exfalso
      exact hgtR.2 hle

  · /- Case B: ∃ x2L ∈ x2.left, x1 ≼ x2L -/
    rcases hbridge with ⟨x2L, hx2L, hle⟩
    have sx2L : IsSurreal x2L := IsSurreal.isSurreal_left sx2 hx2L
    have bx2L : Game.birthday x2L < Game.birthday x2 := Game.birthday_lt_left hx2L

    have hAdj :
        CConditions x2L x2 y := by
      exact adjacentC_left_of_A ((IH (.A x2 y) goal_lt_A_from_C₂) sx2 sy) hx2L

    rcases trichotomy_game sx1 sx2L with hltL | heqL | hgtL

    · /- B2: x1 ≺ x2L -/
      exact C_compose ((IH (.C x1 x2L y) (goal_lt_C₂ bx2L)) sx1 sx2L sy hltL) hAdj

    · /- B1: x1 ∼ x2L -/
      exact C_replace_left_endpoint x1 x2L x2 y IH sx1 sx2L sy bx2L heqL hAdj

    · exfalso
      exact hgtL.2 hle

/-! ### The three main cases of the simultaneous induction -/

private theorem proveA
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g') :
    Holds (.A x y) := by
  intro sx sy
  exact A_product_isSurreal x y IH sx sy

private theorem proveB
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.B x1 x2 y) → Holds g') :
    Holds (.B x1 x2 y) := by
  intro sx1 sx2 sy hEq
  exact B_product_eq x1 x2 y IH sx1 sx2 sy hEq

private theorem proveC
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.C x1 x2 y) → Holds g') :
    Holds (.C x1 x2 y) := by
  intro sx1 sx2 sy hLt
  exact C_core x1 x2 y IH sx1 sx2 sy hLt

/-! ### One simultaneous DM induction proving all three statements -/

theorem ABC_main : ∀ g : Goal, Holds g := by
  intro g
  refine wfGoal.induction g ?_
  intro g IH
  cases g with
  | A x y =>
      exact proveA x y IH
  | B x1 x2 y =>
      exact proveB x1 x2 y IH
  | C x1 x2 y =>
      exact proveC x1 x2 y IH

/-! ### Exported Conway statements A, B, C -/

theorem conway_A {x y : Game}
    (sx : IsSurreal x) (sy : IsSurreal y) :
    IsSurreal (x ⊗ y) := by
  exact (ABC_main (.A x y)) sx sy

/-- Conway B: multiplication respects surreal equivalence in either factor. -/
theorem conway_B {x1 x2 y : Game}
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hEq : x1 ∼ x2) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  exact (ABC_main (.B x1 x2 y)) sx1 sx2 sy hEq

theorem conway_C {x1 x2 y : Game}
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hLt : x1 ≺ x2) :
    (∀ yL ∈ y.left, CLeft x1 x2 y yL) ∧
    (∀ yR ∈ y.right, CRight x1 x2 y yR) := by
  exact (ABC_main (.C x1 x2 y)) sx1 sx2 sy hLt

end Conway
