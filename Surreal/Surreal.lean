import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game

open Game

-- Surreal numbers are defined as games where all left and right options are surreal numbers,
-- and no left option is greater than or equal to any right option
def IsSurreal (g : Game) : Prop :=
  (∀ g_l ∈ g.left, ∀ g_r ∈ g.right, ¬(le g_r g_l)) ∧
  (∀ g_l ∈ g.left, IsSurreal g_l) ∧ (∀ g_r ∈ g.right, IsSurreal g_r)
termination_by g.birthday
decreasing_by
  · have xl : g_l ∈ g.left := by assumption
    apply birthday_lt_left g g_l xl
  · have xr : g_r ∈ g.right := by assumption
    apply birthday_lt_right g g_r xr


def Surreal := { g : Game // IsSurreal g }

-- Caution: g is a surreal number type, but g.left and g.right are
-- just list of games satisfying IsSurreal.
instance : Coe Surreal Game where
  coe := Subtype.val
def Surreal.left (s : Surreal) : List Game := s.val.left
def Surreal.right (s : Surreal) : List Game := s.val.right
def Surreal.le (s t : Surreal) : Prop := Game.le (s.val) (t.val)
def Surreal.lt (s t : Surreal) : Prop := Game.lt (s.val) (t.val)
def Surreal.eq (s t : Surreal) : Prop := Game.eq (s.val) (t.val)

lemma isSurreal_zero : IsSurreal zero := by
  unfold IsSurreal
  constructor
  · simp [zero, Game.left, Game.right]
  · constructor
    · simp [zero, Game.left]
    · simp [zero, Game.right]
def sr_zero : Surreal := ⟨zero, isSurreal_zero⟩
#check sr_zero.val -- Game
#check sr_zero.property -- IsSurreal sr_zero

--- the well-definedness of ≤ on games implies the well-definedness of ≤ on surreal numbers

theorem Surreal.le_refl (x : Surreal) : Surreal.le x x := by
  unfold Surreal.le
  apply x_le_x x.val

theorem Surreal.le_trans : ∀ x y z : Surreal ,
  (Surreal.le x y) ∧ (Surreal.le y z) → Surreal.le x z := by
  unfold Surreal.le
  intro x y z h_le
  exact Game.le_trans x.val y.val z.val h_le

def S : Surreal → Surreal → Prop := fun y x => birthday y < birthday x
lemma wf_S : WellFounded S :=  by
  exact InvImage.wf (fun s : Surreal => birthday s) wellFounded_lt

-- Prove that for any surreal number x = {xl ∈ XL | xr ∈ XR}, xl < x and x < xr
-- The proof requires the fact that x is surreal.
theorem xL_x_xR : ∀ (x : Surreal),
  (∀ x_l ∈ x.left, lt x_l x) ∧ (∀ x_r ∈ x.right, lt x x_r) := by
  intro x
  apply wf_S.induction x
  intro y IH
  constructor
  · intro y_l h_yl
    unfold lt
    constructor
    · -- for y_l ∈ y.left, prove y_l ≤ y
      unfold le
      constructor
      · -- for y_ll ∈ y_l.left, prove ¬(y ≤ y_ll)
        intro y_ll h_yll y_contra
        have y_surreal := y.property
        unfold IsSurreal at y_surreal
        have yl_surreal := y_surreal.2.1 y_l (by simp [left]; exact h_yl)
        unfold le at y_contra
        have h_contra := y_contra.1 y_l (by simp [left]; exact h_yl)
        unfold S at IH
        have h1 := IH ⟨y_l, yl_surreal⟩ (birthday_lt_left y y_l h_yl)
        have h2 := h1.1 y_ll (by simp [Surreal.left]; exact h_yll)
        unfold lt at h2
        have h3 := h2.1
        contradiction
      · -- for y_r ∈ y.right, prove ¬(y_r ≤ y_l)
        -- this is the part where surreal property is used
        intro y_r h_yr
        have h_surreal := y.property
        unfold IsSurreal at h_surreal
        have h1 := h_surreal.1 y_l h_yl y_r h_yr
        exact h1

    · -- for y_l ∈ y.left, prove ¬(y ≤ y_l)
      intro y_le_y_l
      unfold le at y_le_y_l
      let h_contra := y_le_y_l.1 y_l (by simp [left]; exact h_yl)
      have h : le y_l y_l := by exact x_le_x y_l
      contradiction
  · intro y_r h_yr
    unfold lt
    constructor
    · -- for y_r ∈ y.right, prove y ≤ y_r
      unfold le
      constructor
      · -- for y_l ∈ y.left, prove ¬(y_r ≤ y_l)
        intro y_l h_yl
        have h_surreal := y.property
        unfold IsSurreal at h_surreal
        have h1 := h_surreal.1 y_l h_yl y_r (by simp [right]; exact h_yr)
        exact h1
      · -- for y_rr ∈ y_r.right, prove ¬(y_rr ≤ y)
        intro y_rr h_yrr y_contra
        have y_surreal := y.property
        unfold IsSurreal at y_surreal
        have yr_surreal := y_surreal.2.2 y_r (by simp [right]; exact h_yr)
        unfold le at y_contra
        have h_contra := y_contra.2 y_r (by simp [right]; exact h_yr)
        unfold S at IH
        have h1 := IH ⟨y_r, yr_surreal⟩ (birthday_lt_right y y_r h_yr)
        have h2 := h1.2 y_rr (by simp [Surreal.right]; exact h_yrr)
        unfold lt at h2
        have h3 := h2.1
        contradiction
    · -- for y_r ∈ y.right, prove ¬(y_r ≤ y)
      intro y_r_le_y
      unfold le at y_r_le_y
      let h_contra := y_r_le_y.2 y_r (by simp [right]; exact h_yr)
      have h : le y_r y_r := by exact x_le_x y_r
      contradiction

theorem totality : ∀ (x y : Surreal), Surreal.le x y ∨ Surreal.le y x := by
  intro x y
  rw [or_iff_not_imp_left]
  unfold Surreal.le
  nth_rw 1 [le]
  intro h
  rw [not_and_or] at h
  push_neg at h
  cases h with
  | inl h_left =>
    · -- case: ∃ y_r ∈ y.right, x ≤ y_r
      rcases h_left with ⟨xl, h_xl, h_le⟩
      have xl_le_x := ((xL_x_xR x).1 xl h_xl).1
      have y_le_x := le_trans y xl x ⟨h_le, xl_le_x⟩
      exact y_le_x
  | inr h_right =>
    · -- case: ∃ x_l ∈ x.left, y ≤ x_l
      rcases h_right with ⟨yr, h_yr, h_le⟩
      have y_le_yr := ((xL_x_xR y).2 yr h_yr).1
      have x_le_y := le_trans y yr x ⟨y_le_yr, h_le⟩
      exact x_le_y

theorem not_le_iff_lt (x y : Surreal) : x.lt y ↔ ¬(y.le x) := by
  constructor
  · -- Goal 1 : lt x y → ¬(le y x)
    intro h_lt
    unfold Surreal.lt at h_lt
    exact h_lt.2

  · -- Goal 2 : ¬(le y x) → lt x y
    intro h_not_le
    unfold Surreal.lt
    constructor
    · -- Goal 1 : le x y
      exact (totality y x).resolve_left h_not_le
    · -- Goal 2 : ¬(le y x)
      exact h_not_le

theorem Surreal.lt_trans (x y z : Surreal) :
  x.lt y ∧ y.lt z → x.lt z := by
  intro h
  have h_xy := h.1
  have h_yz := h.2
  unfold Surreal.lt
  constructor
  · -- Goal 1: le x z
    have h_x_le_y := h_xy.1
    have h_y_le_z := h_yz.1
    apply Surreal.le_trans x y z
    exact ⟨h_x_le_y, h_y_le_z⟩

  · -- Goal 2: ¬(le z x)
    intro h_contra --assume le z x
    have h_x_le_y := h_xy.1
    have h_z_le_y : z.le y := by
      apply Surreal.le_trans z x y
      exact ⟨h_contra, h_x_le_y⟩
    have h_z_not_le_y := h_yz.2
    contradiction



theorem left_removal_IsSurreal
    (x : Surreal) (l : Game) : IsSurreal (x.val.remove_left l) := by
    sorry

theorem right_removal_IsSurreal
    (x : Surreal) (r : Game) : IsSurreal (x.val.remove_right l) := by
    sorry


theorem like_eq : ∀ (x y : Surreal),
  (∀ xl ∈ x.left, ∃ yl ∈ y.left, eq xl yl) ∧
  (∀ yl ∈ y.left, ∃ xl ∈ x.left, eq yl xl) ∧
  (∀ xr ∈ x.right, ∃ yr ∈ y.right, eq xr yr) ∧
  (∀ yr ∈ y.right, ∃ xr ∈ x.right, eq yr xr) →
  eq x y := by
  intro x y h
  unfold eq
  constructor
  · unfold le
    constructor
    · intro xl h_xl
      by_contra h_le
      have h1 := h.1 xl h_xl
      rcases h1 with ⟨yl, h_yl, h_eq⟩
      have y_le_yl := le_trans y xl yl ⟨h_le, h_eq.1⟩
      have y_nleq_yl := ((xL_x_xR y).1 yl h_yl).2
      contradiction
    · intro yr h_yr
      by_contra h_le
      have h2 := h.2.2.2 yr h_yr
      rcases h2 with ⟨xr, h_xr, h_eq⟩
      have xr_le_x := le_trans xr yr x ⟨h_eq.2, h_le⟩
      have xr_nleq_x := ((xL_x_xR x).2 xr h_xr).2
      contradiction

  · unfold le
    constructor
    · intro yl h_yl
      by_contra h_le
      have h1 := h.2.1 yl h_yl
      rcases h1 with ⟨xl, h_xl, h_eq⟩
      have x_le_xl := le_trans x yl xl ⟨h_le, h_eq.1⟩
      have x_nleq_xl := ((xL_x_xR x).1 xl h_xl).2
      contradiction
    · intro xr h_xr
      by_contra h_le
      have h2 := h.2.2.1 xr h_xr
      rcases h2 with ⟨yr, h_yr, h_eq⟩
      have yr_le_y := le_trans yr xr y ⟨h_eq.2, h_le⟩
      have yr_nleq_y := ((xL_x_xR y).2 yr h_yr).2
      contradiction

theorem simplicity_left (x : Surreal) (l l' : Game)
  (hl : l ∈ x.left) (hl' : l' ∈ x.left) (h_dom : le l l') : (x.val.remove_left l).eq x := by
  sorry

theorem simplicity_right (x : Surreal) (r r' : Game)
  (hr : r ∈ x.right) (hr' : r' ∈ x.right) (h_dom : le r' r) : (x.val.remove_right r).eq x := by
  sorry
