import Mathlib.Data.Multiset.DershowitzManna
import Surreal.Game

open Multiset

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

private inductive TripleGoalKind where
  | B
  | C

private def TripleGoalKind.toGoal : TripleGoalKind → Game → Game → Game → Goal
  | .B => .B
  | .C => .C

@[simp] private lemma μGoal_toGoal (k : TripleGoalKind) (x1 x2 y : Game) :
    μGoal (k.toGoal x1 x2 y) = μB x1 x2 y := by
  cases k <;> rfl

abbrev GoalLT : Goal → Goal → Prop :=
  InvImage IsDershowitzMannaLT μGoal

theorem wfGoal : WellFounded GoalLT := by
  exact InvImage.wf μGoal dm_wf


private lemma dm_of_replace
    (X Y Z : Multiset ℕ)
    (hY : Y ≠ ∅)
    (hsmall : ∀ z ∈ Z, ∃ y ∈ Y, z < y) :
    IsDershowitzMannaLT (X + Z) (X + Y) := by
  unfold IsDershowitzMannaLT
  exact ⟨X, Z, Y, hY, rfl, rfl, hsmall⟩

private lemma dm_of_replace_one
    (X Z : Multiset ℕ) {a : ℕ}
    (hsmall : ∀ z ∈ Z, z < a) :
    IsDershowitzMannaLT (X + Z) (X + {a}) := by
  apply dm_of_replace
  · simp
  · simpa using hsmall

/-!
These are the three canonical decreases used throughout the Conway induction:
replace one entry by one smaller entry, replace it by two smaller entries, or
delete it.  The remaining lemmas only put these comparisons into the coordinate
order appropriate for a particular goal.
-/

private lemma dm_replace_one
    (X : Multiset ℕ) {a b : ℕ} (h : a < b) :
    IsDershowitzMannaLT (X + {a}) (X + {b}) := by
  exact dm_of_replace_one X {a} (a := b) (by simpa using h)

private lemma dm_replace_one_by_two
    (X : Multiset ℕ) {a b c : ℕ} (hb : b < a) (hc : c < a) :
    IsDershowitzMannaLT (X + {b, c}) (X + {a}) := by
  exact dm_of_replace_one X {b, c} (a := a) (by simpa using And.intro hb hc)

private lemma dm_delete_one (X : Multiset ℕ) (a : ℕ) :
    IsDershowitzMannaLT X (X + {a}) := by
  simpa using dm_of_replace_one X ∅ (a := a) (by simp)

lemma dm_pair_one_left {a b c : ℕ} (h : a < b) :
    IsDershowitzMannaLT ({a, c} : Multiset ℕ) ({b, c} : Multiset ℕ) := by
  simpa [add_comm] using dm_replace_one {c} h

lemma dm_pair_one_right {a b c : ℕ} (h : a < b) :
    IsDershowitzMannaLT ({c, a} : Multiset ℕ) ({c, b} : Multiset ℕ) := by
  simpa using dm_replace_one {c} h

lemma dm_pair_both {a b c d : ℕ} (hab : a < b) (hcd : c < d) :
    IsDershowitzMannaLT ({a, c} : Multiset ℕ) ({b, d} : Multiset ℕ) := by
  exact IsDershowitzMannaLT.trans
    (dm_pair_one_right (a := c) (b := d) (c := a) hcd)
    (dm_pair_one_left (a := a) (b := b) (c := d) hab)

private lemma dm_triple_one₁ {a a' b c : ℕ} (h : a' < a) :
    IsDershowitzMannaLT ({a', b, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc, Multiset.cons_swap] using
    dm_replace_one {b, c} h

private lemma dm_triple_one₂ {a b b' c : ℕ} (h : b' < b) :
    IsDershowitzMannaLT ({a, b', c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_replace_one {a, c} h

private lemma dm_triple_one₃ {a b c c' : ℕ} (h : c' < c) :
    IsDershowitzMannaLT ({a, b, c'} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_replace_one {a, b} h

private lemma dm_triple_one₁_swap {a a' b c : ℕ} (h : a' < a) :
    IsDershowitzMannaLT ({b, a', c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc, Multiset.cons_swap] using
    dm_replace_one {b, c} h

private lemma dm_triple_one₂_swap {a b b' c : ℕ} (h : b' < b) :
    IsDershowitzMannaLT ({b', a, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc, Multiset.cons_swap] using
    dm_replace_one {a, c} h

private lemma dm_triple_from_pair_replace_left
    {a b c d : ℕ} (hb : b < a) (hc : c < a) :
    IsDershowitzMannaLT ({b, c, d} : Multiset ℕ) ({a, d} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_replace_one_by_two {d} hb hc

private lemma dm_triple_from_pair_replace_right
    {a b c d : ℕ} (hb : b < a) (hc : c < a) :
    IsDershowitzMannaLT ({b, c, d} : Multiset ℕ) ({d, a} : Multiset ℕ) := by
  change IsDershowitzMannaLT (b ::ₘ c ::ₘ d ::ₘ 0) (d ::ₘ a ::ₘ 0)
  rw [Multiset.cons_swap d a]
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_replace_one_by_two {d} hb hc

private lemma dm_pair_lt_triple_middle {a b c : ℕ} :
    IsDershowitzMannaLT ({a, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_delete_one {a, c} b

private lemma dm_pair_lt_triple_left {a b c : ℕ} :
    IsDershowitzMannaLT ({b, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  change IsDershowitzMannaLT (b ::ₘ c ::ₘ 0) (a ::ₘ b ::ₘ c ::ₘ 0)
  rw [Multiset.cons_swap a b]
  simpa [add_comm, add_left_comm, add_assoc] using
    dm_delete_one {b, c} a

private lemma goal_lt_triple₁ {k k' : TripleGoalKind} {x1 x1' x2 y : Game}
    (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (k.toGoal x1' x2 y) (k'.toGoal x1 x2 y) := by
  simpa [GoalLT, InvImage, μB] using
    dm_triple_one₁
      (a := Game.birthday x1)
      (a' := Game.birthday x1')
      (b := Game.birthday x2)
      (c := Game.birthday y)
      h

private lemma goal_lt_triple₂ {k k' : TripleGoalKind} {x1 x2 x2' y : Game}
    (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (k.toGoal x1 x2' y) (k'.toGoal x1 x2 y) := by
  simpa [GoalLT, InvImage, μB] using
    dm_triple_one₂
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (b' := Game.birthday x2')
      (c := Game.birthday y)
      h

private lemma goal_lt_triple₃ {k k' : TripleGoalKind} {x1 x2 y y' : Game}
    (h : Game.birthday y' < Game.birthday y) :
    GoalLT (k.toGoal x1 x2 y') (k'.toGoal x1 x2 y) := by
  simpa [GoalLT, InvImage, μB] using
    dm_triple_one₃
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)
      (c' := Game.birthday y')
      h

private lemma goal_lt_triple₁_swap {k k' : TripleGoalKind} {a a' b y : Game}
    (h : Game.birthday a' < Game.birthday a) :
    GoalLT (k.toGoal b a' y) (k'.toGoal a b y) := by
  simpa [GoalLT, InvImage, μB] using
    dm_triple_one₁_swap
      (a := Game.birthday a)
      (a' := Game.birthday a')
      (b := Game.birthday b)
      (c := Game.birthday y)
      h

private lemma goal_lt_triple₂_swap {k k' : TripleGoalKind} {a b b' y : Game}
    (h : Game.birthday b' < Game.birthday b) :
    GoalLT (k.toGoal b' a y) (k'.toGoal a b y) := by
  simpa [GoalLT, InvImage, μB] using
    dm_triple_one₂_swap
      (a := Game.birthday a)
      (b := Game.birthday b)
      (b' := Game.birthday b')
      (c := Game.birthday y)
      h

private lemma goal_lt_triple_from_A {k : TripleGoalKind} {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (k.toGoal x1 x2 y) (.A x y) := by
  simpa [GoalLT, InvImage, μA, μB] using
    dm_triple_from_pair_replace_left
      (a := Game.birthday x)
      (b := Game.birthday x1)
      (c := Game.birthday x2)
      (d := Game.birthday y)
      hx1 hx2

private lemma goal_lt_triple_from_A' {k : TripleGoalKind} {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (k.toGoal y1 y2 x) (.A x y) := by
  simpa [GoalLT, InvImage, μA, μB] using
    dm_triple_from_pair_replace_right
      (a := Game.birthday y)
      (b := Game.birthday y1)
      (c := Game.birthday y2)
      (d := Game.birthday x)
      hy1 hy2

private lemma goal_lt_A_from_triple₁ {k : TripleGoalKind} {x1 x2 y : Game} :
    GoalLT (.A x1 y) (k.toGoal x1 x2 y) := by
  simpa [GoalLT, InvImage, μA, μB] using
    dm_pair_lt_triple_middle
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

private lemma goal_lt_A_from_triple₂ {k : TripleGoalKind} {x1 x2 y : Game} :
    GoalLT (.A x2 y) (k.toGoal x1 x2 y) := by
  simpa [GoalLT, InvImage, μA, μB] using
    dm_pair_lt_triple_left
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

lemma goal_lt_A₁ {x x' y : Game} (h : Game.birthday x' < Game.birthday x) :
    GoalLT (.A x' y) (.A x y) := by
  simpa [GoalLT, μGoal, μA] using
    dm_pair_one_left
      (a := Game.birthday x')
      (b := Game.birthday x)
      (c := Game.birthday y)
      h

lemma goal_lt_A₂ {x y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.A x y') (.A x y) := by
  simpa [GoalLT, μGoal, μA] using
    dm_pair_one_right
      (a := Game.birthday y')
      (b := Game.birthday y)
      (c := Game.birthday x)
      h

lemma goal_lt_B₁ {x1 x1' x2 y : Game} (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.B x1' x2 y) (.B x1 x2 y) := by
  exact goal_lt_triple₁ (k := .B) (k' := .B) h

lemma goal_lt_B₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.B x1 x2' y) (.B x1 x2 y) := by
  exact goal_lt_triple₂ (k := .B) (k' := .B) h

lemma goal_lt_B₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2 y') (.B x1 x2 y) := by
  exact goal_lt_triple₃ (k := .B) (k' := .B) h

lemma goal_lt_C₁ {x1 x1' x2 y : Game} (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.C x1' x2 y) (.C x1 x2 y) := by
  exact goal_lt_triple₁ (k := .C) (k' := .C) h

lemma goal_lt_C₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.C x1 x2' y) (.C x1 x2 y) := by
  exact goal_lt_triple₂ (k := .C) (k' := .C) h

lemma goal_lt_C₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.C x1 x2 y') (.C x1 x2 y) := by
  exact goal_lt_triple₃ (k := .C) (k' := .C) h

lemma goal_lt_B_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.B x1 x2 y) (.A x y) := by
  exact goal_lt_triple_from_A (k := .B) hx1 hx2

lemma goal_lt_C_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.C x1 x2 y) (.A x y) := by
  exact goal_lt_triple_from_A (k := .C) hx1 hx2

lemma goal_lt_B_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.B y1 y2 x) (.A x y) := by
  exact goal_lt_triple_from_A' (k := .B) hy1 hy2


lemma goal_lt_C_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.C y1 y2 x) (.A x y) := by
  exact goal_lt_triple_from_A' (k := .C) hy1 hy2

lemma goal_lt_A_from_B₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.B x1 x2 y) := by
  exact goal_lt_A_from_triple₁ (k := .B)

lemma goal_lt_A_from_B₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.B x1 x2 y) := by
  exact goal_lt_A_from_triple₂ (k := .B)

lemma goal_lt_A_from_C₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.C x1 x2 y) := by
  exact goal_lt_A_from_triple₁ (k := .C)

lemma goal_lt_A_from_C₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.C x1 x2 y) := by
  exact goal_lt_A_from_triple₂ (k := .C)

lemma goal_lt_B_from_A_mixed
    {x y x1 x2 y' : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2 y') (.A x y) := by
  exact IsDershowitzMannaLT.trans (goal_lt_B₃ hy') (goal_lt_B_from_A hx1 hx2)

lemma goal_lt_B_from_A_mixed'
    {x y x' y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y)
    (hx' : Game.birthday x' < Game.birthday x) :
    GoalLT (.B y1 y2 x') (.A x y) := by
  exact IsDershowitzMannaLT.trans (goal_lt_B₃ hx') (goal_lt_B_from_A' hy1 hy2)

lemma goal_lt_C_from_B_left_left
    {a a' b y : Game}
    (ha' : Game.birthday a' < Game.birthday a) :
    GoalLT (.C a' b y) (.B a b y) := by
  exact goal_lt_triple₁ (k := .C) (k' := .B) ha'

lemma goal_lt_C_from_B_left_right
    {a a' b y : Game}
    (ha' : Game.birthday a' < Game.birthday a) :
    GoalLT (.C b a' y) (.B a b y) := by
  exact goal_lt_triple₁_swap (k := .C) (k' := .B) ha'

lemma goal_lt_C_from_B_right_left
    {a b b' y : Game}
    (hb' : Game.birthday b' < Game.birthday b) :
    GoalLT (.C b' a y) (.B a b y) := by
  exact goal_lt_triple₂_swap (k := .C) (k' := .B) hb'

lemma goal_lt_C_from_B_right_right
    {a b b' y : Game}
    (hb' : Game.birthday b' < Game.birthday b) :
    GoalLT (.C a b' y) (.B a b y) := by
  exact goal_lt_triple₂ (k := .C) (k' := .B) hb'

lemma goal_lt_B_from_C_left
    {x1 x1' x2 y : Game}
    (hx1' : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.B x1' x2 y) (.C x1 x2 y) := by
  exact goal_lt_triple₁ (k := .B) (k' := .C) hx1'

lemma goal_lt_B_from_C_right
    {x1 x2 x2' y : Game}
    (hx2' : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.B x1 x2' y) (.C x1 x2 y) := by
  exact goal_lt_triple₂ (k := .B) (k' := .C) hx2'

lemma goal_lt_B_from_C_left_mixed
    {x1 x1' x2 y y' : Game}
    (hx1' : Game.birthday x1' < Game.birthday x1)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1' x2 y') (.C x1 x2 y) := by
  exact IsDershowitzMannaLT.trans (goal_lt_B₃ hy') (goal_lt_B_from_C_left hx1')

lemma goal_lt_B_from_C_right_mixed
    {x1 x2 x2' y y' : Game}
    (hx2' : Game.birthday x2' < Game.birthday x2)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2' y') (.C x1 x2 y) := by
  exact IsDershowitzMannaLT.trans (goal_lt_B₃ hy') (goal_lt_B_from_C_right hx2')
