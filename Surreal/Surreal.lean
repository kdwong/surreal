import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game


/-!
# IsSurreal
A combinatorial game whose all left and right options are surreal numbers,
and no left option is greater than or equal to any right option is called IsSurreal.
-/

def IsSurreal (g : Game) : Prop :=
  (∀ g_l ∈ g.left, ∀ g_r ∈ g.right, ¬(g_r.le g_l)) ∧
  (∀ g_l ∈ g.left, IsSurreal g_l) ∧ (∀ g_r ∈ g.right, IsSurreal g_r)
termination_by g.birthday
decreasing_by
  · have xl : g_l ∈ g.left := by assumption
    apply Game.birthday_lt_left xl
  · have xr : g_r ∈ g.right := by assumption
    apply Game.birthday_lt_right xr

namespace IsSurreal

lemma isSurreal_left {g : Game} (hg : IsSurreal g) {l : Game} (hl : l ∈ g.left) :
    IsSurreal l := by
  unfold IsSurreal at hg
  exact hg.2.1 l hl

lemma isSurreal_right {g : Game} (hg : IsSurreal g) {r : Game} (hr : r ∈ g.right) :
    IsSurreal r := by
  unfold IsSurreal at hg
  exact hg.2.2 r hr

lemma isSurreal_zero : IsSurreal Game.zero := by
  unfold IsSurreal
  constructor
  · simp [Game.zero, Game.left, Game.right]
  · constructor
    · simp [Game.zero, Game.left]
    · simp [Game.zero, Game.right]

lemma isSurreal_one : IsSurreal Game.one := by
  unfold IsSurreal
  constructor
  · simp [Game.one, Game.left, Game.right]
  · constructor
    · intro g hg
      simp [Game.one, Game.left] at hg
      rw [hg]
      exact isSurreal_zero
    · simp [Game.one, Game.right]

/-! ## xL < x < xR
If x = {xl ∈ XL | xr ∈ XR} is surreal, then xl < x and x < xr.
This is not true for a general combinatorial game.
-/
private lemma not_le_of_mem_left_right {g : Game} (hg : IsSurreal g)
    {l r : Game} (hl : l ∈ g.left) (hr : r ∈ g.right) : ¬ Game.le r l := by
  unfold IsSurreal at hg
  exact hg.1 l hl r hr

private lemma options_left_le {x : Game} (hx : IsSurreal x) :
    ∀ xL ∈ x.left, Game.le xL x := by
  revert hx
  apply Game.wf_R.induction x
  intro y IH hy yL hyL
  unfold Game.le
  constructor
  · intro yLL hyLL hy_le_yLL
    have hyL_sur : IsSurreal yL := isSurreal_left hy hyL
    have hrec : ∀ z ∈ yL.left, Game.le z yL :=
      IH yL (Game.birthday_lt_left hyL) hyL_sur
    exact (Game.not_ge_left_of_le hy_le_yLL hyL) (hrec yLL hyLL)
  · intro yR hyR
    exact not_le_of_mem_left_right hy hyL hyR

private lemma options_right_le {x : Game} (hx : IsSurreal x) :
    ∀ xR ∈ x.right, Game.le x xR := by
  revert hx
  apply Game.wf_R.induction x
  intro y IH hy yR hyR
  unfold Game.le
  constructor
  · intro yL hyL
    exact not_le_of_mem_left_right hy hyL hyR
  · intro yRR hyRR hyRR_le_y
    have hyR_sur : IsSurreal yR := isSurreal_right hy hyR
    have hrec : ∀ z ∈ yR.right, Game.le yR z :=
      IH yR (Game.birthday_lt_right hyR) hyR_sur
    exact (Game.not_le_right_of_le hyRR_le_y hyR) (hrec yRR hyRR)

theorem left_lt {x xL : Game} (hx : IsSurreal x) (hxL : xL ∈ x.left) :
    Game.lt xL x := by
  exact ⟨(options_left_le hx) xL hxL, Game.not_ge_left_of_le Game.le_congr hxL⟩

theorem lt_right {x xR : Game} (hx : IsSurreal x) (hxR : xR ∈ x.right) :
    Game.lt x xR := by
  exact ⟨(options_right_le hx) xR hxR, Game.not_le_right_of_le Game.le_congr hxR⟩

theorem xL_x_xR {x : Game} (hx : IsSurreal x) :
    (∀ xL ∈ x.left, Game.lt xL x) ∧ (∀ xR ∈ x.right, Game.lt x xR) := by
  exact ⟨fun xL hxL => left_lt hx hxL, fun xR hxR => lt_right hx hxR⟩

theorem le_of_not_le {x y : Game} (hx : IsSurreal x) (hy : IsSurreal y)
  (h : ¬ (Game.le x y)) : Game.le y x := by
  classical
  unfold Game.le at h
  rw [not_and_or] at h
  push_neg at h
  rcases h with h | h
  · rcases h with ⟨xL, hxL, hy_le_xL⟩
    exact Game.le_trans ⟨hy_le_xL, (IsSurreal.left_lt hx hxL).1⟩
  · rcases h with ⟨yR, hyR, hyR_le_x⟩
    exact Game.le_trans ⟨(IsSurreal.lt_right hy hyR).1, hyR_le_x⟩

theorem totality {x y : Game} (hx : IsSurreal x) (hy : IsSurreal y) :
  (Game.le x y) ∨ (Game.le y x) := by
  by_cases hxy : Game.le x y
  · exact Or.inl hxy
  · exact Or.inr (le_of_not_le hx hy hxy)

end IsSurreal

/-!
# Surreal Numbers
g is a surreal number type, but g.left and g.right are lists of games satisfying IsSurreal.
-/
def Surreal := { g : Game // IsSurreal g }

namespace Surreal

def sr_zero : Surreal := ⟨Game.zero, IsSurreal.isSurreal_zero⟩
def sr_one : Surreal := ⟨Game.one, IsSurreal.isSurreal_one⟩
def leftOption (x : Surreal) (xL : Game) (h : xL ∈ x.val.left) : Surreal :=
  ⟨xL, IsSurreal.isSurreal_left x.property h⟩
def rightOption (x : Surreal) (xR : Game) (h : xR ∈ x.val.right) : Surreal :=
  ⟨xR, IsSurreal.isSurreal_right x.property h⟩

instance : Coe Surreal Game where
  coe := Subtype.val
def left (s : Surreal) : List Game := s.val.left
def right (s : Surreal) : List Game := s.val.right
def le (s t : Surreal) : Prop := Game.le (s.val) (t.val)
def lt (s t : Surreal) : Prop := Game.lt (s.val) (t.val)
def eq (s t : Surreal) : Prop := Game.eq (s.val) (t.val)

local notation:70 x " ≼ " y => le x y
local notation:70 x " ≺ " y => lt x y
local notation:70 x " ∼ " y => eq x y


/-! ## Well-founded auxiliary relations -/

private def S : Surreal → Surreal → Prop := fun y x => Game.birthday y < Game.birthday x
private lemma wf_S : WellFounded S :=  by
  exact InvImage.wf (fun s : Surreal => Game.birthday s) wellFounded_lt

structure BiSurreal where
  a : Surreal
  b : Surreal

def U : BiSurreal → BiSurreal → Prop :=
  fun x y =>
    Game.birthday x.a.val + Game.birthday x.b.val <
      Game.birthday y.a.val + Game.birthday y.b.val

theorem wf_U : WellFounded U := by
  exact InvImage.wf
    (fun s : BiSurreal => Game.birthday s.a.val + Game.birthday s.b.val)
    wellFounded_lt

theorem U_left₁ {a b : Surreal} {al : Game} (hal : al ∈ a.val.left) :
    U ⟨leftOption a al hal, b⟩ ⟨a, b⟩ := by
  dsimp [U, leftOption]
  exact add_lt_add_right (Game.birthday_lt_left hal) _

theorem U_left₂ {a b : Surreal} {bl : Game} (hbl : bl ∈ b.val.left) :
    U ⟨a, leftOption b bl hbl⟩ ⟨a, b⟩ := by
  dsimp [U, leftOption]
  exact add_lt_add_left (Game.birthday_lt_left hbl) _

theorem U_right₁ {a b : Surreal} {ar : Game} (har : ar ∈ a.val.right) :
    U ⟨rightOption a ar har, b⟩ ⟨a, b⟩ := by
  dsimp [U, rightOption]
  exact add_lt_add_right (Game.birthday_lt_right har) _

theorem U_right₂ {a b : Surreal} {br : Game} (hbr : br ∈ b.val.right) :
    U ⟨a, rightOption b br hbr⟩ ⟨a, b⟩ := by
  dsimp [U, rightOption]
  exact add_lt_add_left (Game.birthday_lt_right hbr) _


/-! ## Basic order lemmas -/

theorem le_congr {x : Surreal} : x ≼ x := by
  unfold le
  apply Game.le_congr

theorem le_trans {x y z : Surreal} : (x ≼ y) ∧ (y ≼ z) → (x ≼ z) := by
  unfold le
  exact Game.le_trans

theorem eq_symm {x y : Surreal} : (x ∼ y) → (y ∼ x) := by
  unfold eq
  exact Game.eq_symm

theorem lt_trans {x y z : Surreal} : (x ≺ y) ∧ (y ≺ z) → (x ≺ z) := by
  intro h
  unfold lt
  constructor
  · apply le_trans
    exact ⟨h.1.1, h.2.1⟩
  · intro h_contra
    have h_z_le_y : z ≼ y := by
      apply le_trans
      exact ⟨h_contra, h.1.1⟩
    have h_z_not_le_y := h.2.2
    contradiction

/-! ## xL < x < xR
From there, we have totality and trichotomy for surreal numbers.
-/
lemma left_lt {x : Surreal} {xL : Game} (h : xL ∈ x.val.left) :
    Game.lt xL x.val := by exact IsSurreal.left_lt x.property h

lemma lt_right {x : Surreal} {xR : Game} (h : xR ∈ x.val.right) :
    Game.lt x.val xR := by
  exact IsSurreal.lt_right x.property h

lemma left_lt_right {x : Surreal} {xL xR : Game}
    (hL : xL ∈ x.val.left) (hR : xR ∈ x.val.right) :
    Game.lt xL xR := by
  exact Game.lt_trans ⟨IsSurreal.left_lt x.property hL, IsSurreal.lt_right x.property hR⟩

theorem xL_x_xR {x : Surreal} :
    (∀ xL ∈ x.left, Game.lt xL x.val) ∧ (∀ xR ∈ x.right, Game.lt x.val xR) :=
  IsSurreal.xL_x_xR x.property

theorem le_of_not_le {x y : Surreal} (h : ¬ (x ≼ y)) : y ≼ x := by
  classical
  unfold le at h
  rw [Game.le, not_and_or] at h
  push_neg at h
  rcases h with h | h
  · rcases h with ⟨xL, hxL, hy_le_xL⟩
    exact Game.le_trans ⟨hy_le_xL, (IsSurreal.left_lt x.property hxL).1⟩
  · rcases h with ⟨yR, hyR, hyR_le_x⟩
    exact Game.le_trans ⟨(IsSurreal.lt_right y.property hyR).1, hyR_le_x⟩

theorem totality {x y : Surreal} : (x ≼ y) ∨ (y ≼ x) := by
  by_cases hxy : x ≼ y
  · exact Or.inl hxy
  · exact Or.inr (le_of_not_le hxy)


theorem trichotomy {x y : Surreal} : (x ≺ y) ∨ (x ∼ y) ∨ (y ≺ x) := by
  have h_total : (x ≼ y) ∨ (y ≼ x) := totality
  rcases h_total with hxy | hyx
  · by_cases hyx : (y ≼ x)
    · exact Or.inr (Or.inl ⟨hxy, hyx⟩)
    · exact Or.inl ⟨hxy, hyx⟩
  · by_cases hxy : (x ≼ y)
    · exact Or.inr (Or.inl ⟨hxy, hyx⟩)
    · exact Or.inr (Or.inr ⟨hyx, hxy⟩)

theorem not_le_iff_lt {x y : Surreal} : (x ≺ y) ↔ ¬(y ≼ x) := by
  constructor
  · intro h_lt
    unfold lt at h_lt
    exact h_lt.2
  · intro h_not_le
    unfold lt
    constructor
    · exact (totality).resolve_left h_not_le
    · exact h_not_le

end Surreal
