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

/-
  Strict version of the rearrangement lemma
    (((a ⊕ b) ⊕ c.neg) ≺ d) ↔ (a ⊕ b) ≺ (d ⊕ c).

  If you keep your earlier `P_ineq_rearrange` / `sub_le_iff` lemma, prove this once
  and use it everywhere in the branch algebra.
-/
lemma lt_rearrange_neg {a b c d : Game} :
    (((a ⊕ b) ⊕ c.neg) ≺ d) ↔ (a ⊕ b) ≺ (d ⊕ c) := by
  have cancel_neg_add (x : Game) : ((x ⊕ c.neg) ⊕ c).eq x := by
    apply Game.eq_of_q_eq
    change (Game.q (((x ⊕ c.neg) ⊕ c)) : Game.GameQ) = Game.q x
    simp
  have cancel_add_neg (x : Game) : ((x ⊕ c) ⊕ c.neg).eq x := by
    apply Game.eq_of_q_eq
    change (Game.q (((x ⊕ c) ⊕ c.neg)) : Game.GameQ) = Game.q x
    simp
  rw [Game.lt, Game.lt]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h' : (((a ⊕ b) ⊕ c.neg) ⊕ c).le (d ⊕ c) :=
        Game.add_le_add_right h₁
      exact Game.le_trans ⟨(cancel_neg_add (a ⊕ b)).2, h'⟩
    · intro hcontra
      have h' : ((d ⊕ c) ⊕ c.neg).le ((a ⊕ b) ⊕ c.neg) :=
        Game.add_le_add_right hcontra
      exact h₂ (Game.le_trans ⟨(cancel_add_neg d).2, h'⟩)
  · rintro ⟨h₁, h₂⟩
    constructor
    · have h' : ((a ⊕ b) ⊕ c.neg).le ((d ⊕ c) ⊕ c.neg) :=
        Game.add_le_add_right h₁
      exact Game.le_trans ⟨h', (cancel_add_neg d).1⟩
    · intro hcontra
      have h' : (d ⊕ c).le (((a ⊕ b) ⊕ c.neg) ⊕ c) :=
        Game.add_le_add_right hcontra
      exact h₂ (Game.le_trans ⟨h', (cancel_neg_add (a ⊕ b)).1⟩)



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
  have hNoR : ∀ x1R, x1R ∈ x1.right → ¬ x1R ≼ x2 := by
    intro x1R hx1R hxle
    exact hBridge (Or.inl ⟨x1R, hx1R, hxle⟩)
  have hNoL : ∀ x2L, x2L ∈ x2.left → ¬ x1 ≼ x2L := by
    intro x2L hx2L hxle
    exact hBridge (Or.inr ⟨x2L, hx2L, hxle⟩)
  apply h.2
  unfold Game.le
  constructor
  · intro x2L hx2L
    exact hNoL x2L hx2L
  · intro x1R hx1R
    exact hNoR x1R hx1R

/-
  These are the two bridge lemmas used in the strict-bridge cases of C:
  compose C(x1,xm,y) and C(xm,x2,y) into C(x1,x2,y).
-/


/-! ### A-case helpers -/

private lemma A_mulOpt_isSurreal
    (x y x' y' : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    (sx' : IsSurreal x') (sy' : IsSurreal y')
    (hx' : Game.birthday x' < Game.birthday x)
    (hy' : Game.birthday y' < Game.birthday y) :
    IsSurreal (M x' y x y') := by
  have h1 : IsSurreal (x' ⊗ y) := (IH (.A x' y) (goal_lt_A₁ hx')) sx' sy
  have h2 : IsSurreal (x ⊗ y') := (IH (.A x y') (goal_lt_A₂ hy')) sx sy'
  have h3 : IsSurreal (x' ⊗ y') := by
    apply (IH (.A x' y') ?_) sx' sy'
    exact IsDershowitzMannaLT.trans
      (goal_lt_A₁ (x := x) (x' := x') (y := y') hx')
      (goal_lt_A₂ (x := x) (y := y) (y' := y') hy')
  have h12 : IsSurreal ((x' ⊗ y) ⊕ (x ⊗ y')) := add_isSurreal_game h1 h2
  have h3n : IsSurreal (x' ⊗ y').neg := neg_isSurreal_game h3
  simpa [M, Game.mulOpt4] using add_isSurreal_game h12 h3n

private lemma A_option_isSurreal_left
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {L : Game} (hL : L ∈ (x ⊗ y).left) :
    IsSurreal L := by
  rw [mem_mul_left] at hL
  rcases hL with ⟨xl, hxl, yl, hyl, rfl⟩ | ⟨xr, hxr, yr, hyr, rfl⟩
  · exact A_mulOpt_isSurreal x y xl yl IH sx sy
      (IsSurreal.isSurreal_left sx hxl) (IsSurreal.isSurreal_left sy hyl)
      (Game.birthday_lt_left hxl) (Game.birthday_lt_left hyl)
  · exact A_mulOpt_isSurreal x y xr yr IH sx sy
      (IsSurreal.isSurreal_right sx hxr) (IsSurreal.isSurreal_right sy hyr)
      (Game.birthday_lt_right hxr) (Game.birthday_lt_right hyr)

private lemma A_option_isSurreal_right
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {R : Game} (hR : R ∈ (x ⊗ y).right) :
    IsSurreal R := by
  rw [mem_mul_right] at hR
  rcases hR with ⟨xl, hxl, yr, hyr, rfl⟩ | ⟨xr, hxr, yl, hyl, rfl⟩
  · exact A_mulOpt_isSurreal x y xl yr IH sx sy
      (IsSurreal.isSurreal_left sx hxl) (IsSurreal.isSurreal_right sy hyr)
      (Game.birthday_lt_left hxl) (Game.birthday_lt_right hyr)
  · exact A_mulOpt_isSurreal x y xr yl IH sx sy
      (IsSurreal.isSurreal_right sx hxr) (IsSurreal.isSurreal_left sy hyl)
      (Game.birthday_lt_right hxr) (Game.birthday_lt_left hyl)


/-! ### Four branch-family lemmas -/

/-- Family LL: `(xL₁,yL)` versus `(xL₂,yR)`. -/
private lemma A_left_lt_right_LL
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {xL₁ xL₂ yL yR : Game}
    (hxL₁ : xL₁ ∈ x.left) (hxL₂ : xL₂ ∈ x.left)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right) :
    M xL₁ y x yL ≺ M xL₂ y x yR := by
  have sxL₁ : IsSurreal xL₁ := IsSurreal.isSurreal_left sx hxL₁
  have sxL₂ : IsSurreal xL₂ := IsSurreal.isSurreal_left sx hxL₂
  have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
  have syR : IsSurreal yR := IsSurreal.isSurreal_right sy hyR
  have bxL₁ : Game.birthday xL₁ < Game.birthday x := Game.birthday_lt_left hxL₁
  have bxL₂ : Game.birthday xL₂ < Game.birthday x := Game.birthday_lt_left hxL₂
  have byL : Game.birthday yL < Game.birthday y := Game.birthday_lt_left hyL
  have byR : Game.birthday yR < Game.birthday y := Game.birthday_lt_right hyR
  have hyLyR : yL ≺ yR := by
    exact Game.lt_trans ⟨left_lt_game sy hyL, lt_right_game sy hyR⟩
  rcases trichotomy_game sxL₁ sxL₂ with hlt | heq | hgt
  · have hCx :=
      (IH (.C xL₁ xL₂ y) (goal_lt_C_from_A bxL₁ bxL₂)) sxL₁ sxL₂ sy hlt
    have hCy :=
      (IH (.C yL yR x) (goal_lt_C_from_A' byL byR)) syL syR sx hyLyR
    have h1 : M xL₁ y x yL ≺ M xL₂ y x yL := by
      exact mulOpt4_move_x_left_to_right (hCx.1 yL hyL)
    have h2 : M xL₂ y x yL ≺ M xL₂ y x yR := by
      exact mulOpt4_move_y_left_to_right (hCy.1 xL₂ hxL₂)
    exact Game.lt_trans ⟨h1, h2⟩
  · have hCy :=
      (IH (.C yL yR x) (goal_lt_C_from_A' byL byR)) syL syR sx hyLyR
    have hxy : (xL₁ ⊗ y) ∼ (xL₂ ⊗ y) := by
      exact (IH (.B xL₁ xL₂ y) (goal_lt_B_from_A bxL₁ bxL₂)) sxL₁ sxL₂ sy heq
    have hxyR : (xL₁ ⊗ yR) ∼ (xL₂ ⊗ yR) := by
      exact (IH (.B xL₁ xL₂ yR) (goal_lt_B_from_A_mixed bxL₁ bxL₂ byR))
        sxL₁ sxL₂ syR heq
    have h1 : M xL₁ y x yL ≺ M xL₁ y x yR := by
      exact mulOpt4_move_y_left_to_right (hCy.1 xL₁ hxL₁)
    have hEq : M xL₁ y x yR ∼ M xL₂ y x yR := by
      exact mulOpt4_congr_xslot hxy hxyR
    exact Game.lt_of_lt_of_le h1 hEq.1
  · have hCy :=
      (IH (.C yL yR x) (goal_lt_C_from_A' byL byR)) syL syR sx hyLyR
    have hCx :=
      (IH (.C xL₂ xL₁ y) (goal_lt_C_from_A bxL₂ bxL₁)) sxL₂ sxL₁ sy hgt
    have h1 : M xL₁ y x yL ≺ M xL₁ y x yR := by
      exact mulOpt4_move_y_left_to_right (hCy.1 xL₁ hxL₁)
    have h2 : M xL₁ y x yR ≺ M xL₂ y x yR := by
      exact mulOpt4_move_x_right_to_left (hCx.2 yR hyR)
    exact Game.lt_trans ⟨h1, h2⟩

/-- Family LR: `(xL,yL₁)` versus `(xR,yL₂)`. -/
private lemma A_left_lt_right_LR
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {xL xR yL₁ yL₂ : Game}
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL₁ : yL₁ ∈ y.left) (hyL₂ : yL₂ ∈ y.left) :
    M xL y x yL₁ ≺ M xR y x yL₂ := by
  have sxL : IsSurreal xL := IsSurreal.isSurreal_left sx hxL
  have sxR : IsSurreal xR := IsSurreal.isSurreal_right sx hxR
  have syL₁ : IsSurreal yL₁ := IsSurreal.isSurreal_left sy hyL₁
  have syL₂ : IsSurreal yL₂ := IsSurreal.isSurreal_left sy hyL₂
  have bxL : Game.birthday xL < Game.birthday x := Game.birthday_lt_left hxL
  have bxR : Game.birthday xR < Game.birthday x := Game.birthday_lt_right hxR
  have byL₁ : Game.birthday yL₁ < Game.birthday y := Game.birthday_lt_left hyL₁
  have byL₂ : Game.birthday yL₂ < Game.birthday y := Game.birthday_lt_left hyL₂
  have hxLxR : xL ≺ xR := by
    exact Game.lt_trans ⟨left_lt_game sx hxL, lt_right_game sx hxR⟩
  rcases trichotomy_game syL₁ syL₂ with hlt | heq | hgt
  · have hCy :=
      (IH (.C yL₁ yL₂ x) (goal_lt_C_from_A' byL₁ byL₂)) syL₁ syL₂ sx hlt
    have hCx :=
      (IH (.C xL xR y) (goal_lt_C_from_A bxL bxR)) sxL sxR sy hxLxR
    have h1 : M xL y x yL₁ ≺ M xL y x yL₂ := by
      exact mulOpt4_move_y_left_to_right (hCy.1 xL hxL)
    have h2 : M xL y x yL₂ ≺ M xR y x yL₂ := by
      exact mulOpt4_move_x_left_to_right (hCx.1 yL₂ hyL₂)
    exact Game.lt_trans ⟨h1, h2⟩
  · have hCx :=
      (IH (.C xL xR y) (goal_lt_C_from_A bxL bxR)) sxL sxR sy hxLxR
    have hxy₁ : (x ⊗ yL₁) ∼ (x ⊗ yL₂) := by
      have htmp : (yL₁ ⊗ x) ∼ (yL₂ ⊗ x) := by exact
      (IH (.B yL₁ yL₂ x) (goal_lt_B_from_A' byL₁ byL₂)) syL₁ syL₂ sx heq
      have hcomm1 : (x ⊗ yL₁) ∼ (yL₁ ⊗ x) := by
        simpa using (Game.mul_comm : (x ⊗ yL₁) ∼ (yL₁ ⊗ x))
      have hcomm2 : (x ⊗ yL₂) ∼ (yL₂ ⊗ x) := by
        simpa using (Game.mul_comm : (x ⊗ yL₂) ∼ (yL₂ ⊗ x))
      exact ⟨Game.le_trans' hcomm1.1 (Game.le_trans' htmp.1 hcomm2.2),
         Game.le_trans' hcomm2.1 (Game.le_trans' htmp.2 hcomm1.2)⟩
    have hxy₂ : (xR ⊗ yL₁) ∼ (xR ⊗ yL₂) := by
      have htmp : (yL₁ ⊗ xR) ∼ (yL₂ ⊗ xR) := by exact
      (IH (.B yL₁ yL₂ xR) (goal_lt_B_from_A_mixed' byL₁ byL₂ bxR)) syL₁ syL₂ sxR heq
      have hcomm1 : (xR ⊗ yL₁) ∼ (yL₁ ⊗ xR) := by
        simpa using (Game.mul_comm : (xR ⊗ yL₁) ∼ (yL₁ ⊗ xR))
      have hcomm2 : (xR ⊗ yL₂) ∼ (yL₂ ⊗ xR) := by
        simpa using (Game.mul_comm : (xR ⊗ yL₂) ∼ (yL₂ ⊗ xR))
      exact ⟨Game.le_trans' hcomm1.1 (Game.le_trans' htmp.1 hcomm2.2),
         Game.le_trans' hcomm2.1 (Game.le_trans' htmp.2 hcomm1.2)⟩
    have h1 : M xL y x yL₁ ≺ M xR y x yL₁ := by
      exact mulOpt4_move_x_left_to_right (hCx.1 yL₁ hyL₁)
    have hEq : M xR y x yL₁ ∼ M xR y x yL₂ := by
      exact mulOpt4_congr_yslot hxy₂ hxy₁
    exact Game.lt_of_lt_of_le h1 hEq.1
  · have hCx :=
      (IH (.C xL xR y) (goal_lt_C_from_A bxL bxR)) sxL sxR sy hxLxR
    have hCy :=
      (IH (.C yL₂ yL₁ x) (goal_lt_C_from_A' byL₂ byL₁)) syL₂ syL₁ sx hgt
    have h1 : M xL y x yL₁ ≺ M xR y x yL₁ := by
      exact mulOpt4_move_x_left_to_right (hCx.1 yL₁ hyL₁)
    have h2 : M xR y x yL₁ ≺ M xR y x yL₂ := by
      exact mulOpt4_move_y_right_to_left (hCy.2 xR hxR)
    exact Game.lt_trans ⟨h1, h2⟩



/-- Family RL: `(xR₁,yR₁)` versus `(xL₂,yR₂)`. -/
private lemma A_left_lt_right_RL
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {xR₁ xL₂ yR₁ yR₂ : Game}
    (hxR₁ : xR₁ ∈ x.right) (hxL₂ : xL₂ ∈ x.left)
    (hyR₁ : yR₁ ∈ y.right) (hyR₂ : yR₂ ∈ y.right) :
    M xR₁ y x yR₁ ≺ M xL₂ y x yR₂ := by
  have sxR₁ : IsSurreal xR₁ := IsSurreal.isSurreal_right sx hxR₁
  have sxL₂ : IsSurreal xL₂ := IsSurreal.isSurreal_left sx hxL₂
  have syR₁ : IsSurreal yR₁ := IsSurreal.isSurreal_right sy hyR₁
  have syR₂ : IsSurreal yR₂ := IsSurreal.isSurreal_right sy hyR₂
  have bxR₁ : Game.birthday xR₁ < Game.birthday x := Game.birthday_lt_right hxR₁
  have bxL₂ : Game.birthday xL₂ < Game.birthday x := Game.birthday_lt_left hxL₂
  have byR₁ : Game.birthday yR₁ < Game.birthday y := Game.birthday_lt_right hyR₁
  have byR₂ : Game.birthday yR₂ < Game.birthday y := Game.birthday_lt_right hyR₂
  have hxL₂xR₁ : xL₂ ≺ xR₁ := by
    exact Game.lt_trans ⟨left_lt_game sx hxL₂, lt_right_game sx hxR₁⟩
  rcases trichotomy_game syR₁ syR₂ with hlt | heq | hgt
  · have hCx :=
      (IH (.C xL₂ xR₁ y) (goal_lt_C_from_A bxL₂ bxR₁)) sxL₂ sxR₁ sy hxL₂xR₁
    have hCy :=
      (IH (.C yR₁ yR₂ x) (goal_lt_C_from_A' byR₁ byR₂)) syR₁ syR₂ sx hlt
    have h1 : M xR₁ y x yR₁ ≺ M xL₂ y x yR₁ := by
      exact mulOpt4_move_x_right_to_left (hCx.2 yR₁ hyR₁)
    have h2 : M xL₂ y x yR₁ ≺ M xL₂ y x yR₂ := by
      exact mulOpt4_move_y_left_to_right (hCy.1 xL₂ hxL₂)
    exact Game.lt_trans ⟨h1, h2⟩
  · have hCx :=
      (IH (.C xL₂ xR₁ y) (goal_lt_C_from_A bxL₂ bxR₁)) sxL₂ sxR₁ sy hxL₂xR₁
    have hxy₁ : (x ⊗ yR₁) ∼ (x ⊗ yR₂) := by
      have htmp : (yR₁ ⊗ x) ∼ (yR₂ ⊗ x) := by
        exact (IH (.B yR₁ yR₂ x) (goal_lt_B_from_A' byR₁ byR₂))
            syR₁ syR₂ sx heq
      have hcomm1 : (x ⊗ yR₁) ∼ (yR₁ ⊗ x) := by
        simpa using (Game.mul_comm : (x ⊗ yR₁) ∼ (yR₁ ⊗ x))
      have hcomm2 : (x ⊗ yR₂) ∼ (yR₂ ⊗ x) := by
        simpa using (Game.mul_comm : (x ⊗ yR₂) ∼ (yR₂ ⊗ x))
      exact ⟨Game.le_trans' hcomm1.1 (Game.le_trans' htmp.1 hcomm2.2),
       Game.le_trans' hcomm2.1 (Game.le_trans' htmp.2 hcomm1.2)⟩
    have hxy₂ : (xL₂ ⊗ yR₁) ∼ (xL₂ ⊗ yR₂) := by
      have htmp : (yR₁ ⊗ xL₂) ∼ (yR₂ ⊗ xL₂) := by
        exact (IH (.B yR₁ yR₂ xL₂) (goal_lt_B_from_A_mixed' byR₁ byR₂ bxL₂))
          syR₁ syR₂ sxL₂ heq
      have hcomm1 : (xL₂ ⊗ yR₁) ∼ (yR₁ ⊗ xL₂) := by
        simpa using (Game.mul_comm : (xL₂ ⊗ yR₁) ∼ (yR₁ ⊗ xL₂))
      have hcomm2 : (xL₂ ⊗ yR₂) ∼ (yR₂ ⊗ xL₂) := by
        simpa using (Game.mul_comm : (xL₂ ⊗ yR₂) ∼ (yR₂ ⊗ xL₂))
      exact ⟨Game.le_trans' hcomm1.1 (Game.le_trans' htmp.1 hcomm2.2),
        Game.le_trans' hcomm2.1 (Game.le_trans' htmp.2 hcomm1.2)⟩
    have h1 : M xR₁ y x yR₁ ≺ M xL₂ y x yR₁ := by
      exact mulOpt4_move_x_right_to_left (hCx.2 yR₁ hyR₁)
    have hEq : M xL₂ y x yR₁ ∼ M xL₂ y x yR₂ := by
      exact mulOpt4_congr_yslot hxy₂ hxy₁
    exact Game.lt_of_lt_of_le h1 hEq.1
  · have hCy :=
      (IH (.C yR₂ yR₁ x) (goal_lt_C_from_A' byR₂ byR₁)) syR₂ syR₁ sx hgt
    have hCx :=
      (IH (.C xL₂ xR₁ y) (goal_lt_C_from_A bxL₂ bxR₁)) sxL₂ sxR₁ sy hxL₂xR₁
    have h1 : M xR₁ y x yR₁ ≺ M xR₁ y x yR₂ := by
      exact mulOpt4_move_y_right_to_left (hCy.2 xR₁ hxR₁)
    have h2 : M xR₁ y x yR₂ ≺ M xL₂ y x yR₂ := by
      exact mulOpt4_move_x_right_to_left (hCx.2 yR₂ hyR₂)
    exact Game.lt_trans ⟨h1, h2⟩

private lemma A_left_lt_right_RR
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {xR₁ xR₂ yR₁ yL₂ : Game}
    (hxR₁ : xR₁ ∈ x.right) (hxR₂ : xR₂ ∈ x.right)
    (hyR₁ : yR₁ ∈ y.right) (hyL₂ : yL₂ ∈ y.left) :
    M xR₁ y x yR₁ ≺ M xR₂ y x yL₂ := by
  have sxR₁ : IsSurreal xR₁ := IsSurreal.isSurreal_right sx hxR₁
  have sxR₂ : IsSurreal xR₂ := IsSurreal.isSurreal_right sx hxR₂
  have syR₁ : IsSurreal yR₁ := IsSurreal.isSurreal_right sy hyR₁
  have syL₂ : IsSurreal yL₂ := IsSurreal.isSurreal_left sy hyL₂
  have bxR₁ : Game.birthday xR₁ < Game.birthday x := Game.birthday_lt_right hxR₁
  have bxR₂ : Game.birthday xR₂ < Game.birthday x := Game.birthday_lt_right hxR₂
  have byR₁ : Game.birthday yR₁ < Game.birthday y := Game.birthday_lt_right hyR₁
  have byL₂ : Game.birthday yL₂ < Game.birthday y := Game.birthday_lt_left hyL₂
  have hyL₂yR₁ : yL₂ ≺ yR₁ := by
    exact Game.lt_trans ⟨left_lt_game sy hyL₂, lt_right_game sy hyR₁⟩
  rcases trichotomy_game sxR₁ sxR₂ with hlt | heq | hgt
  · have hCy :=
      (IH (.C yL₂ yR₁ x) (goal_lt_C_from_A' byL₂ byR₁)) syL₂ syR₁ sx hyL₂yR₁
    have hCx :=
      (IH (.C xR₁ xR₂ y) (goal_lt_C_from_A bxR₁ bxR₂)) sxR₁ sxR₂ sy hlt
    have h1 : M xR₁ y x yR₁ ≺ M xR₁ y x yL₂ := by
      exact mulOpt4_move_y_right_to_left (hCy.2 xR₁ hxR₁)
    have h2 : M xR₁ y x yL₂ ≺ M xR₂ y x yL₂ := by
      exact mulOpt4_move_x_left_to_right (hCx.1 yL₂ hyL₂)
    exact Game.lt_trans ⟨h1, h2⟩
  · have hCy :=
      (IH (.C yL₂ yR₁ x) (goal_lt_C_from_A' byL₂ byR₁)) syL₂ syR₁ sx hyL₂yR₁
    have hxy : (xR₁ ⊗ y) ∼ (xR₂ ⊗ y) := by
      exact (IH (.B xR₁ xR₂ y) (goal_lt_B_from_A bxR₁ bxR₂)) sxR₁ sxR₂ sy heq
    have hxyL : (xR₁ ⊗ yL₂) ∼ (xR₂ ⊗ yL₂) := by
      exact (IH (.B xR₁ xR₂ yL₂) (goal_lt_B_from_A_mixed bxR₁ bxR₂ byL₂))
        sxR₁ sxR₂ syL₂ heq
    have h1 : M xR₁ y x yR₁ ≺ M xR₁ y x yL₂ := by
      exact mulOpt4_move_y_right_to_left (hCy.2 xR₁ hxR₁)
    have hEq : M xR₁ y x yL₂ ∼ M xR₂ y x yL₂ := by
      exact mulOpt4_congr_xslot hxy hxyL
    exact Game.lt_of_lt_of_le h1 hEq.1
  · have hCx :=
      (IH (.C xR₂ xR₁ y) (goal_lt_C_from_A bxR₂ bxR₁)) sxR₂ sxR₁ sy hgt
    have hCy :=
      (IH (.C yL₂ yR₁ x) (goal_lt_C_from_A' byL₂ byR₁)) syL₂ syR₁ sx hyL₂yR₁
    have h1 : M xR₁ y x yR₁ ≺ M xR₂ y x yR₁ := by
      exact mulOpt4_move_x_right_to_left (hCx.2 yR₁ hyR₁)
    have h2 : M xR₂ y x yR₁ ≺ M xR₂ y x yL₂ := by
      exact mulOpt4_move_y_right_to_left (hCy.2 xR₂ hxR₂)
    exact Game.lt_trans ⟨h1, h2⟩

private lemma A_left_lt_right
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
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
    · simpa [M] using A_left_lt_right_LL x y IH sx sy hxL₁ hxL₂ hyL₁ hyR₂
    · simpa [M] using A_left_lt_right_LR x y IH sx sy hxL₁ hxR₂ hyL₁ hyL₂
  · rcases hR with
      ⟨xL₂, hxL₂, yR₂, hyR₂, rfl⟩ | ⟨xR₂, hxR₂, yL₂, hyL₂, rfl⟩
    · simpa [M] using A_left_lt_right_RL x y IH sx sy hxR₁ hxL₂ hyR₁ hyR₂
    · simpa [M] using A_left_lt_right_RR x y IH sx sy hxR₁ hxR₂ hyR₁ hyL₂

private lemma A_product_isSurreal
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y) :
    IsSurreal (x ⊗ y) := by
  unfold IsSurreal
  refine ⟨?_, ?_⟩
  · intro L hL R hR
    exact (A_left_lt_right x y IH sx sy hL hR).2
  · constructor
    · intro L hL
      exact A_option_isSurreal_left x y IH sx sy hL
    · intro R hR
      exact A_option_isSurreal_right x y IH sx sy hR



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

private lemma B_product_le
    (a b y : Game)
    (IH : ∀ g', GoalLT g' (.B a b y) → Holds g')
    (sa : IsSurreal a) (sb : IsSurreal b) (sy : IsSurreal y)
    (hEq : a ∼ b) :
    (a ⊗ y) ≼ (b ⊗ y) := by
  have hAa : IsSurreal (a ⊗ y) := by
    exact (IH (.A a y) goal_lt_A_from_B₁) sa sy
  have hAb : IsSurreal (b ⊗ y) := by
    exact (IH (.A b y) goal_lt_A_from_B₂) sb sy
  have IHswap := IHswap_of_IH IH
  have hEq' : b ∼ a := ⟨hEq.2, hEq.1⟩
  unfold Game.le
  constructor
  · intro L hL
    rw [mem_mul_left] at hL
    rcases hL with
      ⟨aL, haL, yL, hyL, rfl⟩ | ⟨aR, haR, yR, hyR, rfl⟩
    · have saL : IsSurreal aL := IsSurreal.isSurreal_left sa haL
      have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
      have hB : (a ⊗ yL) ∼ (b ⊗ yL) := by
        exact
          (IH (.B a b yL) (goal_lt_B₃ (Game.birthday_lt_left hyL)))
            sa sb syL hEq
      have hlt : aL ≺ b := by
        exact Game.lt_of_lt_of_le (left_lt_game sa haL) hEq.1
      have hC :
          CConditions aL b y := by
        exact
          (IH (.C aL b y)
            (goal_lt_C_from_B_left_left (Game.birthday_lt_left haL)))
            saL sb sy hlt
      exact (mulOpt4_LL_lt_product hB (hC.1 yL hyL)).2
    · have saR : IsSurreal aR := IsSurreal.isSurreal_right sa haR
      have syR : IsSurreal yR := IsSurreal.isSurreal_right sy hyR
      have hB : (a ⊗ yR) ∼ (b ⊗ yR) := by
        exact
          (IH (.B a b yR) (goal_lt_B₃ (Game.birthday_lt_right hyR)))
            sa sb syR hEq
      have hlt : b ≺ aR := by
        exact Game.lt_of_le_of_lt hEq.2 (lt_right_game sa haR)
      have hC :
          CConditions b aR y := by
        exact
          (IH (.C b aR y)
            (goal_lt_C_from_B_left_right (Game.birthday_lt_right haR)))
            sb saR sy hlt
      exact (mulOpt4_RR_lt_product hB (hC.2 yR hyR)).2
  · intro R hR
    rw [mem_mul_right] at hR
    rcases hR with
      ⟨bL, hbL, yR, hyR, rfl⟩ | ⟨bR, hbR, yL, hyL, rfl⟩
    · have sbL : IsSurreal bL := IsSurreal.isSurreal_left sb hbL
      have syR : IsSurreal yR := IsSurreal.isSurreal_right sy hyR
      have hB : (b ⊗ yR) ∼ (a ⊗ yR) := by
        exact
          (IHswap (.B b a yR) (goal_lt_B₃ (Game.birthday_lt_right hyR)))
            sb sa syR hEq'
      have hlt : bL ≺ a := by
        exact Game.lt_of_lt_of_le (left_lt_game sb hbL) hEq.2
      have hC :
          CConditions bL a y := by
        exact
          (IH (.C bL a y)
            (goal_lt_C_from_B_right_left (Game.birthday_lt_left hbL)))
            sbL sa sy hlt
      exact (product_lt_mulOpt4_LR hB (hC.2 yR hyR)).2
    · have sbR : IsSurreal bR := IsSurreal.isSurreal_right sb hbR
      have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
      have hB : (b ⊗ yL) ∼ (a ⊗ yL) := by
        exact
          (IHswap (.B b a yL) (goal_lt_B₃ (Game.birthday_lt_left hyL)))
            sb sa syL hEq'
      have hlt : a ≺ bR := by
        exact Game.lt_of_le_of_lt hEq.1 (lt_right_game sb hbR)
      have hC :
          CConditions a bR y := by
        exact
          (IH (.C a bR y)
            (goal_lt_C_from_B_right_right (Game.birthday_lt_right hbR)))
            sa sbR sy hlt
      exact (product_lt_mulOpt4_RL hB (hC.1 yL hyL)).2

/-! #### Final B theorem -/

private lemma B_product_eq
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.B x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hEq : x1 ∼ x2) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  have h₁ : (x1 ⊗ y) ≼ (x2 ⊗ y) := by
    exact B_product_le x1 x2 y IH sx1 sx2 sy hEq
  have IHswap : ∀ g', GoalLT g' (.B x2 x1 y) → Holds g' := by
    exact IHswap_of_IH IH
  have hEq' : x2 ∼ x1 := ⟨hEq.2, hEq.1⟩
  have h₂ : (x2 ⊗ y) ≼ (x1 ⊗ y) := by
    exact B_product_le x2 x1 y IHswap sx2 sx1 sy hEq'
  exact ⟨h₁, h₂⟩




/-! ### C-case helper -/


private lemma C_compose
    {x1 xm x2 y : Game}
    (h1 : CConditions x1 xm y)
    (h2 : CConditions xm x2 y) :
    CConditions x1 x2 y := by
  exact ⟨fun yL hyL => C_compose_left (h1.1 yL hyL) (h2.1 yL hyL),
    fun yR hyR => C_compose_right (h1.2 yR hyR) (h2.2 yR hyR)⟩

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

    have hAxy : IsSurreal (x1 ⊗ y) := by
      exact (IH (.A x1 y) goal_lt_A_from_C₁) sx1 sy

    have hAdj :
        CConditions x1 x1R y := by
      exact adjacentC_right_of_A hAxy hx1R

    rcases trichotomy_game sx1R sx2 with hltR | heqR | hgtR

    · /- A2: x1R ≺ x2 -/
      have hRec :
          CConditions x1R x2 y := by
        exact (IH (.C x1R x2 y) (goal_lt_C₁ bx1R)) sx1R sx2 sy hltR

      exact C_compose hAdj hRec

    · /- A1: x1R ∼ x2 -/
      have hBy : (x1R ⊗ y) ∼ (x2 ⊗ y) := by
        exact (IH (.B x1R x2 y) (goal_lt_B_from_C_left bx1R)) sx1R sx2 sy heqR

      refine ⟨?_, ?_⟩
      · intro yL hyL
        have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
        have byL : Game.birthday yL < Game.birthday y := Game.birthday_lt_left hyL
        have hByL : (x1R ⊗ yL) ∼ (x2 ⊗ yL) := by
          exact
            (IH (.B x1R x2 yL) (goal_lt_B_from_C_left_mixed bx1R byL))
              sx1R sx2 syL heqR
        exact C_replace_eq_left hByL hBy (hAdj.1 yL hyL)

      · intro yR hyR
        have syR : IsSurreal yR := IsSurreal.isSurreal_right sy hyR
        have byR : Game.birthday yR < Game.birthday y := Game.birthday_lt_right hyR
        have hByR : (x1R ⊗ yR) ∼ (x2 ⊗ yR) := by
          exact
            (IH (.B x1R x2 yR) (goal_lt_B_from_C_left_mixed bx1R byR))
              sx1R sx2 syR heqR
        exact C_replace_eq_right hByR hBy (hAdj.2 yR hyR)

    · exfalso
      exact hgtR.2 hle

  · /- Case B: ∃ x2L ∈ x2.left, x1 ≼ x2L -/
    rcases hbridge with ⟨x2L, hx2L, hle⟩
    have sx2L : IsSurreal x2L := IsSurreal.isSurreal_left sx2 hx2L
    have bx2L : Game.birthday x2L < Game.birthday x2 := Game.birthday_lt_left hx2L

    have hAxy : IsSurreal (x2 ⊗ y) := by
      exact (IH (.A x2 y) goal_lt_A_from_C₂) sx2 sy

    have hAdj :
        CConditions x2L x2 y := by
      exact adjacentC_left_of_A hAxy hx2L

    rcases trichotomy_game sx1 sx2L with hltL | heqL | hgtL

    · /- B2: x1 ≺ x2L -/
      have hRec :
          CConditions x1 x2L y := by
        exact (IH (.C x1 x2L y) (goal_lt_C₂ bx2L)) sx1 sx2L sy hltL

      exact C_compose hRec hAdj

    · /- B1: x1 ∼ x2L -/
      have hBy : (x1 ⊗ y) ∼ (x2L ⊗ y) := by
        exact (IH (.B x1 x2L y) (goal_lt_B_from_C_right bx2L)) sx1 sx2L sy heqL

      refine ⟨?_, ?_⟩
      · intro yL hyL
        have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
        have byL : Game.birthday yL < Game.birthday y := Game.birthday_lt_left hyL
        have hByL : (x1 ⊗ yL) ∼ (x2L ⊗ yL) := by
          exact
            (IH (.B x1 x2L yL) (goal_lt_B_from_C_right_mixed bx2L byL))
              sx1 sx2L syL heqL
        exact C_replace_eq_left_first hByL hBy (hAdj.1 yL hyL)

      · intro yR hyR
        have syR : IsSurreal yR := IsSurreal.isSurreal_right sy hyR
        have byR : Game.birthday yR < Game.birthday y := Game.birthday_lt_right hyR
        have hByR : (x1 ⊗ yR) ∼ (x2L ⊗ yR) := by
          exact
            (IH (.B x1 x2L yR) (goal_lt_B_from_C_right_mixed bx2L byR))
              sx1 sx2L syR heqL
        exact C_replace_eq_right_first hByR hBy (hAdj.2 yR hyR)

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

/-
  This is Conway's B in the `Game.eq` / surreal-equivalence sense.
  If you really want a literal `=` version as well, it is a trivial corollary.
-/
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
