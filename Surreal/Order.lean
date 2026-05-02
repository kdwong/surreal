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

private lemma dm_pair_one_left {a b c : ℕ} (h : a < b) :
    IsDershowitzMannaLT ({a, c} : Multiset ℕ) ({b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({c} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ({b} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    subst z
    exact ⟨b, by simp, h⟩

private lemma dm_pair_one_right {a b c : ℕ} (h : a < b) :
    IsDershowitzMannaLT ({c, a} : Multiset ℕ) ({c, b} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({c} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ({b} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
  · intro z hz
    simp at hz
    subst z
    exact ⟨b, by simp, h⟩

private lemma dm_triple_one₁ {a a' b c : ℕ} (h : a' < a) :
    IsDershowitzMannaLT ({a', b, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({b, c} : Multiset ℕ),
      ({a'} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    subst z
    exact ⟨a, by simp, h⟩

private lemma dm_triple_one₂ {a b b' c : ℕ} (h : b' < b) :
    IsDershowitzMannaLT ({a, b', c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({a, c} : Multiset ℕ),
      ({b'} : Multiset ℕ),
      ({b} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    subst z
    exact ⟨b, by simp, h⟩

private lemma dm_triple_one₃ {a b c c' : ℕ} (h : c' < c) :
    IsDershowitzMannaLT ({a, b, c'} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({a, b} : Multiset ℕ),
      ({c'} : Multiset ℕ),
      ({c} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
  · intro z hz
    simp at hz
    subst z
    exact ⟨c, by simp, h⟩

private lemma dm_triple_one₁_swap {a a' b c : ℕ} (h : a' < a) :
    IsDershowitzMannaLT ({b, a', c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({b, c} : Multiset ℕ),
      ({a'} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    subst z
    exact ⟨a, by simp, h⟩

private lemma dm_triple_one₂_swap {a b b' c : ℕ} (h : b' < b) :
    IsDershowitzMannaLT ({b', a, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({a, c} : Multiset ℕ),
      ({b'} : Multiset ℕ),
      ({b} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    subst z
    exact ⟨b, by simp, h⟩

private lemma dm_triple_from_pair_replace_left
    {a b c d : ℕ} (hb : b < a) (hc : c < a) :
    IsDershowitzMannaLT ({b, c, d} : Multiset ℕ) ({a, d} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({d} : Multiset ℕ),
      ({b, c} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz
    rcases hz with rfl | rfl
    · exact ⟨a, by simp, hb⟩
    · exact ⟨a, by simp, hc⟩

private lemma dm_triple_from_pair_replace_right
    {a b c d : ℕ} (hb : b < a) (hc : c < a) :
    IsDershowitzMannaLT ({b, c, d} : Multiset ℕ) ({d, a} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({d} : Multiset ℕ),
      ({b, c} : Multiset ℕ),
      ({a} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
  · intro z hz
    simp at hz
    rcases hz with rfl | rfl
    · exact ⟨a, by simp, hb⟩
    · exact ⟨a, by simp, hc⟩

private lemma dm_pair_lt_triple_middle {a b c : ℕ} :
    IsDershowitzMannaLT ({a, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({a, c} : Multiset ℕ),
      (∅ : Multiset ℕ),
      ({b} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz

private lemma dm_pair_lt_triple_left {a b c : ℕ} :
    IsDershowitzMannaLT ({b, c} : Multiset ℕ) ({a, b, c} : Multiset ℕ) := by
  unfold IsDershowitzMannaLT
  refine
    ⟨({b, c} : Multiset ℕ),
      (∅ : Multiset ℕ),
      ({a} : Multiset ℕ),
      ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · ext z
    simp [Multiset.count_cons, Multiset.count_singleton]
    ac_rfl
  · intro z hz
    simp at hz

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
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₁
      (a := Game.birthday x1)
      (a' := Game.birthday x1')
      (b := Game.birthday x2)
      (c := Game.birthday y)
      h

lemma goal_lt_B₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.B x1 x2' y) (.B x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₂
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (b' := Game.birthday x2')
      (c := Game.birthday y)
      h

lemma goal_lt_B₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2 y') (.B x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₃
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)
      (c' := Game.birthday y')
      h

lemma goal_lt_C₁ {x1 x1' x2 y : Game} (h : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.C x1' x2 y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₁
      (a := Game.birthday x1)
      (a' := Game.birthday x1')
      (b := Game.birthday x2)
      (c := Game.birthday y)
      h

lemma goal_lt_C₂ {x1 x2 x2' y : Game} (h : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.C x1 x2' y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₂
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (b' := Game.birthday x2')
      (c := Game.birthday y)
      h

lemma goal_lt_C₃ {x1 x2 y y' : Game} (h : Game.birthday y' < Game.birthday y) :
    GoalLT (.C x1 x2 y') (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₃
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)
      (c' := Game.birthday y')
      h

lemma goal_lt_B_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.B x1 x2 y) (.A x y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_triple_from_pair_replace_left
      (a := Game.birthday x)
      (b := Game.birthday x1)
      (c := Game.birthday x2)
      (d := Game.birthday y)
      hx1 hx2

lemma goal_lt_C_from_A
    {x x1 x2 y : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x) :
    GoalLT (.C x1 x2 y) (.A x y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_triple_from_pair_replace_left
      (a := Game.birthday x)
      (b := Game.birthday x1)
      (c := Game.birthday x2)
      (d := Game.birthday y)
      hx1 hx2

lemma goal_lt_B_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.B y1 y2 x) (.A x y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_triple_from_pair_replace_right
      (a := Game.birthday y)
      (b := Game.birthday y1)
      (c := Game.birthday y2)
      (d := Game.birthday x)
      hy1 hy2


lemma goal_lt_C_from_A'
    {x y y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y) :
    GoalLT (.C y1 y2 x) (.A x y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_triple_from_pair_replace_right
      (a := Game.birthday y)
      (b := Game.birthday y1)
      (c := Game.birthday y2)
      (d := Game.birthday x)
      hy1 hy2

lemma goal_lt_A_from_B₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.B x1 x2 y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_pair_lt_triple_middle
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

lemma goal_lt_A_from_B₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.B x1 x2 y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_pair_lt_triple_left
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

lemma goal_lt_A_from_C₁ {x1 x2 y : Game} :
    GoalLT (.A x1 y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_pair_lt_triple_middle
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

lemma goal_lt_A_from_C₂ {x1 x2 y : Game} :
    GoalLT (.A x2 y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μA, μB] using
    dm_pair_lt_triple_left
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (c := Game.birthday y)

lemma goal_lt_B_from_A_mixed
    {x y x1 x2 y' : Game}
    (hx1 : Game.birthday x1 < Game.birthday x)
    (hx2 : Game.birthday x2 < Game.birthday x)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2 y') (.A x y) := by
  have h1 : GoalLT (.B x1 x2 y') (.B x1 x2 y) := by
    exact goal_lt_B₃ hy'
  have h2 : GoalLT (.B x1 x2 y) (.A x y) := by
    exact goal_lt_B_from_A hx1 hx2
  exact IsDershowitzMannaLT.trans h1 h2

lemma goal_lt_B_from_A_mixed'
    {x y x' y1 y2 : Game}
    (hy1 : Game.birthday y1 < Game.birthday y)
    (hy2 : Game.birthday y2 < Game.birthday y)
    (hx' : Game.birthday x' < Game.birthday x) :
    GoalLT (.B y1 y2 x') (.A x y) := by
  have h1 : GoalLT (.B y1 y2 x') (.B y1 y2 x) := by
    exact goal_lt_B₃ hx'
  have h2 : GoalLT (.B y1 y2 x) (.A x y) := by
    exact goal_lt_B_from_A' hy1 hy2
  exact IsDershowitzMannaLT.trans h1 h2

lemma goal_lt_C_from_B_left_left
    {a a' b y : Game}
    (ha' : Game.birthday a' < Game.birthday a) :
    GoalLT (.C a' b y) (.B a b y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₁
      (a := Game.birthday a)
      (a' := Game.birthday a')
      (b := Game.birthday b)
      (c := Game.birthday y)
      ha'

lemma goal_lt_C_from_B_left_right
    {a a' b y : Game}
    (ha' : Game.birthday a' < Game.birthday a) :
    GoalLT (.C b a' y) (.B a b y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₁_swap
      (a := Game.birthday a)
      (a' := Game.birthday a')
      (b := Game.birthday b)
      (c := Game.birthday y)
      ha'

lemma goal_lt_C_from_B_right_left
    {a b b' y : Game}
    (hb' : Game.birthday b' < Game.birthday b) :
    GoalLT (.C b' a y) (.B a b y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₂_swap
      (a := Game.birthday a)
      (b := Game.birthday b)
      (b' := Game.birthday b')
      (c := Game.birthday y)
      hb'

lemma goal_lt_C_from_B_right_right
    {a b b' y : Game}
    (hb' : Game.birthday b' < Game.birthday b) :
    GoalLT (.C a b' y) (.B a b y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₂
      (a := Game.birthday a)
      (b := Game.birthday b)
      (b' := Game.birthday b')
      (c := Game.birthday y)
      hb'

lemma goal_lt_B_from_C_left
    {x1 x1' x2 y : Game}
    (hx1' : Game.birthday x1' < Game.birthday x1) :
    GoalLT (.B x1' x2 y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₁
      (a := Game.birthday x1)
      (a' := Game.birthday x1')
      (b := Game.birthday x2)
      (c := Game.birthday y)
      hx1'

lemma goal_lt_B_from_C_right
    {x1 x2 x2' y : Game}
    (hx2' : Game.birthday x2' < Game.birthday x2) :
    GoalLT (.B x1 x2' y) (.C x1 x2 y) := by
  simpa [GoalLT, μGoal, μB] using
    dm_triple_one₂
      (a := Game.birthday x1)
      (b := Game.birthday x2)
      (b' := Game.birthday x2')
      (c := Game.birthday y)
      hx2'

lemma goal_lt_B_from_C_left_mixed
    {x1 x1' x2 y y' : Game}
    (hx1' : Game.birthday x1' < Game.birthday x1)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1' x2 y') (.C x1 x2 y) := by
  have h1 : GoalLT (.B x1' x2 y') (.B x1' x2 y) := by
    exact goal_lt_B₃ hy'
  have h2 : GoalLT (.B x1' x2 y) (.C x1 x2 y) := by
    exact goal_lt_B_from_C_left hx1'
  exact IsDershowitzMannaLT.trans h1 h2

lemma goal_lt_B_from_C_right_mixed
    {x1 x2 x2' y y' : Game}
    (hx2' : Game.birthday x2' < Game.birthday x2)
    (hy' : Game.birthday y' < Game.birthday y) :
    GoalLT (.B x1 x2' y') (.C x1 x2 y) := by
  have h1 : GoalLT (.B x1 x2' y') (.B x1 x2' y) := by
    exact goal_lt_B₃ hy'
  have h2 : GoalLT (.B x1 x2' y) (.C x1 x2 y) := by
    exact goal_lt_B_from_C_right hx2'
  exact IsDershowitzMannaLT.trans h1 h2
