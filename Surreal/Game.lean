import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

inductive Game where
  | mk : List Game → List Game → Game
deriving BEq, Repr

instance : LawfulBEq Game where
  eq_of_beq := by sorry
  rfl := by sorry

open Game

def Game.left (g : Game) : List Game :=
  match g with
  | mk left _ => left

def Game.right (g : Game) : List Game :=
  match g with
  | mk _ right => right

def zero : Game := mk [] []
def minus_one : Game := mk [] [zero]
def one : Game := mk [zero] []
def half : Game := mk [zero] [one]

def Game.birthday (g : Game) : Nat :=
  match g with
  | mk L R =>
    let bL := L.map birthday
    let bR := R.map birthday
    (bL ++ bR).maximum.getD 0 + 1

#eval birthday zero
#eval birthday half -- 3

lemma list_maximum_is_none_then_is_empty (a : List ℕ) (non : a.maximum = none) : a = [] := by
  cases a with
  | nil => rfl
  | cons hd tl =>
    have ne_none : (hd :: tl).maximum ≠ none := by
      apply List.maximum_ne_bot_of_ne_nil
      simp
    contradiction

lemma elt_leq_max (a : List ℕ) (s : ℕ) (h : s ∈ a) : s ≤ a.maximum.getD 0 := by
    match max : a.maximum with
    | none =>
      have a_empty : a = [] := by
        apply list_maximum_is_none_then_is_empty a max
      rw [a_empty] at h
      contradiction
    | some m =>
      simp [Option.getD_some]
      exact List.le_of_mem_argmax h max

lemma birthday_lt_left (g : Game) (l : Game) (h : l ∈ g.left) :
    birthday l < birthday g := by
  cases g with
  | mk L R =>
    simp [left] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday l < b.maximum.getD 0 + 1
    have h_mem_b : l.birthday ∈ b := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      use l
    have a : l.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b l.birthday h_mem_b
    linarith

lemma birthday_lt_right (g : Game) (r : Game) (h : r ∈ g.right) :
    birthday r < birthday g := by
  cases g with
  | mk L R =>
    simp [right] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday r < b.maximum.getD 0 + 1
    have h_mem_b : r.birthday ∈ b := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      use r
    have aaa : r.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b r.birthday h_mem_b
    linarith

def Game.le (g h : Game) : Prop :=
    (∀ g_l ∈ g.left, ¬(le h g_l)) ∧ (∀ h_r ∈ h.right, ¬(le h_r g))
termination_by (birthday g + birthday h)
decreasing_by
  -- Prove termination for the first recursive call: `le h g_l`
  · have xl : g_l ∈ g.left := by assumption
    rw [add_comm h.birthday g_l.birthday]
    apply add_lt_add_right
    exact birthday_lt_left g g_l xl
  -- Prove termination for the second recursive call: `le h_r g`
  · have xr : h_r ∈ h.right := by assumption
    rw [add_comm h_r.birthday g.birthday]
    apply add_lt_add_left
    exact birthday_lt_right h h_r xr

def Game.lt (g h : Game) : Prop := le g h ∧ ¬(le h g)

def Game.eq (g h : Game) : Prop :=
  le g h ∧ le h g

theorem zero_leq_zero : le zero zero := by
      unfold le
      constructor <;> (intro g h; cases h)

theorem zero_leq_one : le zero one := by
  unfold le
  constructor
  · intro z_l zero_left
    cases zero_left
  · intro o_r one_right
    cases one_right

theorem one_not_leq_zero : ¬(le one zero) := by
  intro h_le
  unfold le at h_le
  let h_not_le_zero_zero := h_le.1 zero (by simp [one, left])
  exact h_not_le_zero_zero zero_leq_zero

theorem half_leq_one : le half one := by
  unfold le
  constructor
  · intro h_l half_left
    simp only [half, left, List.mem_singleton] at half_left
    subst half_left
    exact one_not_leq_zero
  · intro o_r one_right
    cases one_right

theorem zero_lth_one : lt zero one := by
  unfold lt
  constructor
  · exact zero_leq_one
  · intro h_le
    unfold le at h_le
    let h_contra := h_le.1 zero (by simp [one, left])
    exact h_contra zero_leq_zero

def zero' : Game := mk [minus_one] [one]

theorem zero_zero'_eq : eq zero zero' := by
  unfold eq
  constructor
  · -- Prove `zero ≤ zero'`
    unfold le
    constructor
    · intro z_l zero_left
      cases zero_left
    · intro z_r zero'_right
      simp only [zero', right, List.mem_singleton] at zero'_right
      subst zero'_right
      exact one_not_leq_zero
  · -- Prove `zero' ≤ zero`
    unfold le
    constructor
    · intro z'_l zero'_left
      simp only [zero', left, List.mem_singleton] at zero'_left
      subst z'_l
      intro h_le_zero_neg_one
      unfold le at h_le_zero_neg_one
      let h_contra := h_le_zero_neg_one.2 zero (by simp [minus_one, right])
      exact h_contra zero_leq_zero
    · intro z_r zero_right
      cases zero_right

def R : Game → Game → Prop := fun y x => birthday y < birthday x
lemma wf_R : WellFounded R := InvImage.wf birthday wellFounded_lt

theorem Game.le_refl (x : Game) : le x x := by
  apply wf_R.induction x
  intro x IH
  unfold le
  unfold R at IH

  constructor
  · intro l xl h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.1 l (by simp[left]; exact xl)
    have h_le: le l l := IH l (birthday_lt_left x l xl)
    contradiction

  · intro r hr h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.2 r (by simp[right]; exact hr)
    have h_le: le r r := IH r (birthday_lt_right x r hr)
    contradiction

theorem x_eq_x : ∀ (x : Game), eq x x := by
  intro x
  unfold eq
  constructor
  · exact le_refl x
  · exact le_refl x


structure TriGame where
  a : Game  -- The first natural number, named 'a'
  b : Game  -- The second natural number, named 'b'
  c : Game  -- The third natural number, named 'c'

def T : TriGame → TriGame → Prop :=
  fun a b => birthday a.1 + birthday a.2 + birthday a.3 < birthday b.1 + birthday b.2 + birthday b.3
lemma wf_T : WellFounded T :=
  InvImage.wf (fun s : TriGame => birthday s.1 + birthday s.2 + birthday s.3) wellFounded_lt

theorem Game.le_trans1 : ∀ (x : TriGame) ,
  (le x.a x.b) ∧ (le x.b x.c) → le x.a x.c := by
  intro x
  apply wf_T.induction x
  intro x IH h_le
  have a_le_b := h_le.1
  have b_le_c := h_le.2
  unfold le
  constructor
  · -- Prove `∀ a_l ∈ a.left, ¬(c ≤ a_l)`
    intro a_l h_a_l h_contra
    -- Assume `c  ≤ a_l` for contradiction.
    have h_birthday_sum_lt : T {a := x.b, b := x.c, c := a_l} x := by
      simp [T]
      have := birthday_lt_left x.a a_l h_a_l
      linarith
    --- Use `b ≤ c` and `c  ≤ a_l` and induction to show `b ≤ a_l`
    have h_b_le_al : le x.b a_l := by
      apply IH {a := x.b, b := x.c, c := a_l} h_birthday_sum_lt
      exact ⟨b_le_c, h_contra⟩
    -- But `a ≤ b` implies `¬(b ≤ a_l)`
    unfold le at a_le_b
    have b_notle_a_l := a_le_b.1 a_l h_a_l
    contradiction
  ·-- Prove `∀ c_r ∈ c.right, ¬(c_r ≤ a)`
    intro c_r h_c_r h_contra
    -- Assume `c_r ≤ a` for contradiction.
    have h_birthday_sum_lt : T {a := c_r, b := x.a, c := x.b} x := by
      simp [T]
      have := birthday_lt_right x.c c_r h_c_r
      linarith
    --- Use `c_r ≤ a` and `a ≤ b` and induction to show `c_r ≤ b`
    have h_c_r_le_b : c_r.le x.b := by
      apply IH {a := c_r, b := x.a, c := x.b} h_birthday_sum_lt
      exact ⟨h_contra, a_le_b⟩
    unfold le at b_le_c
    -- But `b ≤ c` implies `¬(c_r ≤ b)`
    have c_r_nleq_b := b_le_c.2 c_r h_c_r
    contradiction

theorem Game.le_trans : ∀ x y z : Game , (le x y) ∧ (le y z) → le x z :=
by
  intro x y z habc
  let tri : TriGame := {a := x, b := y, c := z}
  apply le_trans1 tri habc


#eval [zero, one].erase one
#eval [zero, one].erase half


def Game.remove_left (g : Game) (l : Game) : Game :=
  mk ((g.left).erase l) g.right

def Game.remove_right (g : Game) (r : Game) : Game :=
  mk g.left (g.right.erase r)

#eval half
#eval half.remove_right one
#eval half.remove_left zero

lemma remove_left_eq_right (g : Game) (l : Game) :
  (g.remove_left l).right = g.right := by
  simp [remove_left]
  simp [right]

lemma remove_left_subset_left (g : Game) (l : Game) :
  (g.remove_left l).left ⊆ g.left := by
  simp [remove_left, left]
  apply List.erase_subset

lemma remove_left_contains_all_but (g l x : Game) (hx : x ∈ g.left) (h_neq : x ≠ l) :
  x ∈ (g.remove_left l).left := by
  change x ∈ g.left.erase l
  simp [List.mem_erase_of_ne, h_neq]
  exact hx

lemma remove_left_dom_remains (g l l' : Game) (hl' : l' ∈ g.left) (h_dom : l.lt l') :
  l' ∈ (g.remove_left l).left := by
  have h_neq : l' ≠ l := by
    by_contra h_eq
    have h : l'.le l := by rw[h_eq]; exact le_refl l
    have h_contra := h_dom.2
    contradiction
  apply remove_left_contains_all_but g l l' hl' h_neq

lemma remove_right_eq_left (g : Game) (r : Game) :
  (g.remove_right r).left = g.left := by
  simp [remove_right]
  simp [left]

lemma remove_right_subset_right (g : Game) (r : Game) :
  (g.remove_right r).right ⊆ g.right := by
  simp [right]
  apply List.erase_subset

lemma remove_right_contains_all_but (g x r : Game) (hx : x ∈ g.right) (h_neq : x ≠ r) :
  x ∈ (g.remove_right r).right := by
  change x ∈ g.right.erase r
  simp [List.mem_erase_of_ne, h_neq]
  exact hx

lemma remove_right_dom_remains (g r' r : Game) (hr' : r' ∈ g.right) (h_dom : r'.lt r) :
  r' ∈ (g.remove_right r).right := by
  have h_neq : r' ≠ r := by
    by_contra h_eq
    have h : r.le r' := by rw[h_eq]; exact le_refl r
    have h_contra := h_dom.2
    contradiction
  apply remove_right_contains_all_but g r' r hr' h_neq


