import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm
import Surreal.CommGroup

open Multiset
open Game

namespace ConwayDMBlueprint

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y


/-
  Conway A/B/C, but with the corrected 3-variable C:

    A(x,y) : x*y is surreal.
    B(x1,x2,y) : x1 ∼ x2 -> x1*y ∼ x2*y.
    C(x1,x2,y) : x1 ≺ x2 ->
      (forall yL ∈ y.left,  x1*y + x2*yL < x1*yL + x2*y)  and
      (forall yR ∈ y.right, x1*yR + x2*y < x1*y + x2*yR).

  The whole file is arranged as one simultaneous well-founded induction on the
  Dershowitz–Manna order of multisets of birthdays.
-/

/-! ### DM measure on birthdays -/

theorem dm_wf :
    WellFounded (IsDershowitzMannaLT : Multiset ℕ → Multiset ℕ → Prop) := by
  exact wellFounded_isDershowitzMannaLT

def μA (x y : Game) : Multiset ℕ :=
  {Game.birthday x, Game.birthday y}

def μB (x1 x2 y : Game) : Multiset ℕ :=
  {Game.birthday x1, Game.birthday x2, Game.birthday y}

/-!
  A goal is either an A-goal, a B-goal, or a C-goal.
  B and C share the same 3-variable measure.
-/
inductive Goal where
  | A : Game → Game → Goal
  | B : Game → Game → Game → Goal
  | C : Game → Game → Game → Goal
deriving Repr

def μGoal : Goal → Multiset ℕ
  | .A x y      => μA x y
  | .B x1 x2 y  => μB x1 x2 y
  | .C x1 x2 y  => μB x1 x2 y

abbrev GoalLT : Goal → Goal → Prop :=
  InvImage IsDershowitzMannaLT μGoal

theorem wfGoal : WellFounded GoalLT := by
  exact InvImage.wf μGoal dm_wf

/-!
  Basic DM wrappers.

  You already have most of these in your birthday-DM file; I am restating them
  here as the interface the proof below wants to use.
-/

lemma goal_lt_A₁ {x x' y : Game} (h : Game.birthday x' < Game.birthday x) :
    GoalLT (.A x' y) (.A x y) := by
  sorry

lemma goal_lt_A₂ {x y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.A x y') (.A x y) := by
  sorry

lemma goal_lt_B₁ {x1 x1' x2 y : Game} (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.B x1' x2 y) (.B x1 x2 y) := by
  sorry

lemma goal_lt_B₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.B x1 x2' y) (.B x1 x2 y) := by
  sorry

lemma goal_lt_B₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2 y') (.B x1 x2 y) := by
  sorry

lemma goal_lt_C₁ {x1 x1' x2 y : Game} (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.C x1' x2 y) (.C x1 x2 y) := by
  sorry

lemma goal_lt_C₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.C x1 x2' y) (.C x1 x2 y) := by
  sorry

lemma goal_lt_C₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.C x1 x2 y') (.C x1 x2 y) := by
  sorry

lemma goal_lt_B_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.B x1 x2 y) (.A x y) := by
  sorry

lemma goal_lt_C_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.C x1 x2 y) (.A x y) := by
  sorry

lemma goal_lt_B_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.B y1 y2 x) (.A x y) := by
  sorry

lemma goal_lt_C_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.C y1 y2 x) (.A x y) := by
  sorry

lemma goal_lt_A_from_B₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.B x1 x2 y) := by
  sorry

lemma goal_lt_A_from_B₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.B x1 x2 y) := by
  sorry

lemma goal_lt_A_from_C₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.C x1 x2 y) := by
  sorry

lemma goal_lt_A_from_C₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.C x1 x2 y) := by
  sorry

/-! ### The three statements as a dependent predicate on `Goal` -/

def CLeft (x1 x2 y yL : Game) : Prop :=
  ((x1 ⊗ y) ⊕ (x2 ⊗ yL)) ≺ ((x1 ⊗ yL) ⊕ (x2 ⊗ y))

def CRight (x1 x2 y yR : Game) : Prop :=
  ((x1 ⊗ yR) ⊕ (x2 ⊗ y)) ≺ ((x1 ⊗ y) ⊕ (x2 ⊗ yR))

def Holds : Goal → Prop
  | .A x y =>
      IsSurreal x → IsSurreal y → IsSurreal (x ⊗ y)
  | .B x1 x2 y =>
      IsSurreal x1 → IsSurreal x2 → IsSurreal y →
      x1 ∼ x2 → (x1 ⊗ y) ∼ (x2 ⊗ y)
  | .C x1 x2 y =>
      IsSurreal x1 → IsSurreal x2 → IsSurreal y →
      x1 ≺ x2 →
      (∀ yL ∈ y.left, CLeft x1 x2 y yL) ∧
      (∀ yR ∈ y.right, CRight x1 x2 y yR)

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
  sorry

/-
  “Adjacent C” comes from A: if `xL` is a left option of `x`, then the two C-inequalities
  for `(xL,x,y)` are exactly the facts that the corresponding `mulOpt4` terms are left/right
  options of `x ⊗ y`, hence sit on the correct side of `x ⊗ y`.
-/
lemma adjacentC_left_of_A
    {x xL y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxL : xL ∈ x.left) :
    (∀ yL ∈ y.left, CLeft xL x y yL) ∧
    (∀ yR ∈ y.right, CRight xL x y yR) := by
  sorry

lemma adjacentC_right_of_A
    {x xR y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxR : xR ∈ x.right) :
    (∀ yL ∈ y.left, CLeft x xR y yL) ∧
    (∀ yR ∈ y.right, CRight x xR y yR) := by
  sorry

/-
  Bridge extraction from `x1 ≺ x2`:

  either there is a right option `x1R` with `x1R ≼ x2`,
  or there is a left option `x2L` with `x1 ≼ x2L`.
-/
lemma bridge_exists_of_lt {x1 x2 : Game} (h : x1 ≺ x2) :
    (∃ x1R ∈ x1.right, x1R ≼ x2) ∨
    (∃ x2L ∈ x2.left, x1 ≼ x2L) := by
  sorry

/-
  These are the two bridge lemmas used in the strict-bridge cases of C:
  compose C(x1,xm,y) and C(xm,x2,y) into C(x1,x2,y).
-/
lemma C_compose_left
    {x1 xm x2 y yL : Game}
    (h1 : CLeft x1 xm y yL)
    (h2 : CLeft xm x2 y yL) :
    CLeft x1 x2 y yL := by
  sorry

lemma C_compose_right
    {x1 xm x2 y yR : Game}
    (h1 : CRight x1 xm y yR)
    (h2 : CRight xm x2 y yR) :
    CRight x1 x2 y yR := by
  sorry

/-
  These are the bridge lemmas used in the equality-bridge cases of C:
  replace the intermediate factor `xm * y?` by `x2 * y?` using B.
-/
lemma C_replace_eq_left
    {x1 xm x2 y yL : Game}
    (hEqL : (xm ⊗ yL) ∼ (x2 ⊗ yL))
    (hEq  : (xm ⊗ y)  ∼ (x2 ⊗ y))
    (hAdj : CLeft x1 xm y yL) :
    CLeft x1 x2 y yL := by
  sorry

lemma C_replace_eq_right
    {x1 xm x2 y yR : Game}
    (hEqR : (xm ⊗ yR) ∼ (x2 ⊗ yR))
    (hEq  : (xm ⊗ y)  ∼ (x2 ⊗ y))
    (hAdj : CRight x1 xm y yR) :
    CRight x1 x2 y yR := by
  sorry

/-! ### A-case helpers -/

private lemma A_option_isSurreal_left
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {L : Game} (hL : L ∈ (x ⊗ y).left) :
    IsSurreal L := by
  /-
    Decompose `hL` with `Game.mem_mul_left`.
    In either branch, `L` is a `Game.mulOpt4 ...`.
    Use recursive A-calls on the three smaller products:
      xOpt * y, x * yOpt, xOpt * yOpt.
    Then close under `+` and `neg`.
  -/
  sorry

private lemma A_option_isSurreal_right
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {R : Game} (hR : R ∈ (x ⊗ y).right) :
    IsSurreal R := by
  /-
    Same as the left-option helper, but using `Game.mem_mul_right`.
  -/
  sorry

private lemma A_left_lt_right
    (x y : Game)
    (IH : ∀ g', GoalLT g' (.A x y) → Holds g')
    (sx : IsSurreal x) (sy : IsSurreal y)
    {L R : Game}
    (hL : L ∈ (x ⊗ y).left)
    (hR : R ∈ (x ⊗ y).right) :
    L ≺ R := by
  /-
    This is the corrected dependency table, implemented by cases on
    `Game.mem_mul_left` and `Game.mem_mul_right`.

    Families of branches:

    F1: (xL1,yL)  vs (xL2,yR)
      xL1 ∼ xL2 : use B(xL1,xL2,y), B(xL1,xL2,yR), C(yL,yR,x)
      xL1 < xL2 : use C(xL1,xL2,y), C(yL,yR,x)
      xL2 < xL1 : use C(yL,yR,x), C(xL2,xL1,y)

    F2: (xL,yL1)  vs (xR,yL2)
      yL1 ∼ yL2 : use B(yL1,yL2,x), B(yL1,yL2,xR), C(xL,xR,y)
      yL1 < yL2 : use C(yL1,yL2,x), C(xL,xR,y)
      yL2 < yL1 : use C(xL,xR,y), C(yL2,yL1,x)

    F3: (xR,yR1)  vs (xL,yR2)
      yR1 ∼ yR2 : use B(yR1,yR2,x), B(yR1,yR2,xL), C(xL,xR,y)
      yR1 < yR2 : use C(xL,xR,y), C(yR1,yR2,x)
      yR2 < yR1 : use C(yR2,yR1,x), C(xL,xR,y)

    F4: (xR1,yR)  vs (xR2,yL)
      xR1 ∼ xR2 : use B(xR1,xR2,y), B(xR1,xR2,yL), C(yL,yR,x)
      xR1 < xR2 : use C(xR1,xR2,y), C(yL,yR,x)
      xR2 < xR1 : use C(yL,yR,x), C(xR2,xR1,y)

    In each branch:
      * get the relevant recursive A/B/C call from `IH`;
      * rewrite the `mulOpt4` terms into a common additive normal form;
      * use `lt_rearrange_neg`, `Game.add_equal`, `Game.add_lt_le`,
        `Game.add_le_lt`, `Game.add_assoc`, `Game.add_comm`,
        `Game.add_neg`, `Game.neg_add`, and, when convenient,
        quotient-level `abel` rewrites (`Game.eq_of_q_eq`).
      * F2/F3 are handled by switching to the y-side through `Game.mul_comm`.
  -/
  sorry

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

private lemma B_product_eq
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.B x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hEq : x1 ∼ x2) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  /-
    Unfold `Game.eq`; prove both `Game.le` directions.

    Ambient A-calls:
      A(x1,y), A(x2,y)

    For `(x1 ⊗ y) ≼ (x2 ⊗ y)`:
      left options of x1*y:
        x1-LL : B(x1,x2,yL) + C(x1L,x2,y)
        x1-RR : B(x1,x2,yR) + C(x2,x1R,y)
        x1-LR : B(x1,x2,yR) + C(x1L,x2,y)
        x1-RL : B(x1,x2,yL) + C(x2,x1R,y)
      right options of x2*y:
        x2-LL : B(x2,x1,yL) + C(x2L,x1,y)
        x2-RR : B(x2,x1,yR) + C(x1,x2R,y)
        x2-LR : B(x2,x1,yR) + C(x2L,x1,y)
        x2-RL : B(x2,x1,yL) + C(x1,x2R,y)

    Each branch:
      * take the recursive B-call for the y-option;
      * derive the needed `<` hypothesis for the recursive C-call from
        `IsSurreal.left_lt` / `IsSurreal.lt_right` plus `Game.lt_of_lt_of_le`
        or `Game.lt_of_le_of_lt`;
      * rearrange the resulting inequality to show the relevant option lies on the
        correct side, hence obtain the desired `¬ ... ≤ ...`.

    The reverse direction `(x2 ⊗ y) ≼ (x1 ⊗ y)` is the same with x1/x2 swapped.
  -/
  sorry

/-! ### C-case helper -/

private lemma C_core
    (x1 x2 y : Game)
    (IH : ∀ g', GoalLT g' (.C x1 x2 y) → Holds g')
    (sx1 : IsSurreal x1) (sx2 : IsSurreal x2) (sy : IsSurreal y)
    (hLt : x1 ≺ x2) :
    (∀ yL ∈ y.left, CLeft x1 x2 y yL) ∧
    (∀ yR ∈ y.right, CRight x1 x2 y yR) := by
  /-
    Step 1: extract a bridge from `x1 ≺ x2` using `bridge_exists_of_lt`.

    Case A: there exists x1R ∈ x1.right with x1R ≼ x2.
      A1. If x1R ∼ x2:
            use B(x1R,x2,yL), B(x1R,x2,y), B(x1R,x2,yR)
            together with `adjacentC_right_of_A` coming from A(x1,y).
      A2. If x1R ≺ x2:
            use recursive C(x1,x1R,y) and recursive C(x1R,x2,y),
            then compose with `C_compose_left/right`.

    Case B: there exists x2L ∈ x2.left with x1 ≼ x2L.
      B1. If x1 ∼ x2L:
            use B(x1,x2L,yL), B(x1,x2L,y), B(x1,x2L,yR)
            together with `adjacentC_left_of_A` coming from A(x2,y).
      B2. If x1 ≺ x2L:
            use recursive C(x1,x2L,y) and recursive C(x2L,x2,y),
            then compose with `C_compose_left/right`.

    Equality-bridge branches are finished with `C_replace_eq_left/right`.
  -/
  sorry

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

end ConwayDMBlueprint
