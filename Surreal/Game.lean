import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-!
# Combinatorial games

This file defines short combinatorial games, their birthdays,
and the basic recursive order/equivalence relations.
-/

inductive Game where
  | mk : List Game → List Game → Game
deriving BEq, Repr

namespace Game

def left : Game → List Game
  | mk L _ => L

def right : Game → List Game
  | mk _ R => R

theorem ext {x y : Game} (hL : x.left = y.left) (hR : x.right = y.right) :
    x = y := by
  cases x with
  | mk XL XR =>
    cases y with
    | mk YL YR =>
      simp [left, right] at hL hR
      cases hL
      cases hR
      rfl


/-! ## Basic games -/

def zero : Game := mk [] []
def one : Game := mk [zero] []

/-! ## Birthday -/

def birthday : Game → Nat
  | mk L R =>
      let bL := L.map birthday
      let bR := R.map birthday
      (bL ++ bR).maximum.getD 0 + 1

lemma maximum_eq_none_iff_eq_nil (a : List ℕ) (non : a.maximum = none) : a = [] := by
  cases a with
  | nil => rfl
  | cons hd tl =>
    have ne_none : (hd :: tl).maximum ≠ none := by
      apply List.maximum_ne_bot_of_ne_nil
      simp
    contradiction

lemma le_maximum_getD_of_mem (a : List ℕ) (s : ℕ) (h : s ∈ a) : s ≤ a.maximum.getD 0 := by
    match max : a.maximum with
    | none =>
      have a_empty : a = [] := by
        apply maximum_eq_none_iff_eq_nil a max
      rw [a_empty] at h
      contradiction
    | some m =>
      simp [Option.getD_some]
      exact List.le_of_mem_argmax h max

lemma birthday_lt_of_mem_options {L R : List Game} {x : Game}
    (h : x ∈ L ++ R) :
    birthday x < birthday (mk L R) := by
  simp [birthday]
  let b := List.map birthday L ++ List.map birthday R
  change birthday x < b.maximum.getD 0 + 1
  have h_mem_b : birthday x ∈ b := by
    dsimp [b]
    rcases List.mem_append.mp h with hL | hR
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hL, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨x, hR, rfl⟩)
  exact Nat.lt_succ_of_le (le_maximum_getD_of_mem b (birthday x) h_mem_b)

theorem birthday_lt_left {g l : Game} (h : l ∈ g.left) :
    birthday l < birthday g := by
  cases g with
  | mk L R =>
      have hL : l ∈ L := by simpa [left] using h
      exact birthday_lt_of_mem_options
        (L := L) (R := R) (List.mem_append_left _ hL)

theorem birthday_lt_right {g r : Game} (h : r ∈ g.right) :
    birthday r < birthday g := by
  cases g with
  | mk L R =>
      have hR : r ∈ R := by simpa [right] using h
      exact birthday_lt_of_mem_options
        (L := L) (R := R) (List.mem_append_right _ hR)


/-! ## Order relations -/

def le (g h : Game) : Prop :=
    (∀ g_l ∈ g.left, ¬(le h g_l)) ∧ (∀ h_r ∈ h.right, ¬(le h_r g))
termination_by g.birthday + h.birthday
decreasing_by
  · linarith [birthday_lt_left ‹_›]
  · linarith [birthday_lt_right ‹_›]

def lt (g h : Game) : Prop := le g h ∧ ¬(le h g)

def eq (g h : Game) : Prop := le g h ∧ le h g

scoped infix:50 " ≼ " => Game.le
scoped infix:50 " ≺ " => Game.lt
scoped infix:50 " ∼ " => Game.eq

/-! ## Well-founded auxiliary relations -/

def R : Game → Game → Prop := fun y x => birthday y < birthday x
lemma wf_R : WellFounded R := InvImage.wf birthday wellFounded_lt

structure BiGame where
  a : Game
  b : Game
def B : BiGame → BiGame → Prop :=
  fun a b => birthday a.1 + birthday a.2 < birthday b.1 + birthday b.2
lemma wf_B : WellFounded B :=
  InvImage.wf (fun s : BiGame => (birthday s.1) + (birthday s.2)) wellFounded_lt

lemma B_of_left_mem_fst {x y xl : Game} (hxl : xl ∈ x.left) :
    B ⟨xl, y⟩ ⟨x, y⟩ := by
  simpa [B] using add_lt_add_right (Game.birthday_lt_left hxl) y.birthday

lemma B_of_left_mem_snd {x y yl : Game} (hyl : yl ∈ y.left) :
    B ⟨x, yl⟩ ⟨x, y⟩ := by
  simpa [B] using add_lt_add_left (Game.birthday_lt_left hyl) x.birthday

lemma B_of_right_mem_fst {x y xr : Game} (hxr : xr ∈ x.right) :
    B ⟨xr, y⟩ ⟨x, y⟩ := by
  simpa [B] using add_lt_add_right (Game.birthday_lt_right hxr) y.birthday

lemma B_of_right_mem_snd {x y yr : Game} (hyr : yr ∈ y.right) :
    B ⟨x, yr⟩ ⟨x, y⟩ := by
  simpa [B] using add_lt_add_left (Game.birthday_lt_right hyr) x.birthday

lemma B_of_left_mem_swap {a b aL : Game} (haL : aL ∈ a.left) :
    B ⟨b, aL⟩ ⟨a, b⟩ := by
  simpa [B, Nat.add_comm] using
    (B_of_left_mem_snd (x := b) (y := a) haL)

lemma B_of_right_mem_swap {a b bR : Game} (hbR : bR ∈ b.right) :
    B ⟨bR, a⟩ ⟨a, b⟩ := by
  simpa [B, Nat.add_comm] using
    (B_of_right_mem_fst (x := b) (y := a) hbR)


structure TriGame where
  a : Game
  b : Game
  c : Game
def T : TriGame → TriGame → Prop :=
  fun a b => birthday a.1 + birthday a.2 + birthday a.3 < birthday b.1 + birthday b.2 + birthday b.3
lemma wf_T : WellFounded T :=
  InvImage.wf (fun s : TriGame => birthday s.1 + birthday s.2 + birthday s.3) wellFounded_lt

lemma T_of_left_mem {a b c aL : Game} (haL : aL ∈ a.left) :
    T ⟨b, c, aL⟩ ⟨a, b, c⟩ := by
  simp [T]
  linarith [birthday_lt_left haL]

lemma T_of_right_mem {a b c cR : Game} (hcR : cR ∈ c.right) :
    T ⟨cR, a, b⟩ ⟨a, b, c⟩ := by
  simp [T]
  linarith [birthday_lt_right hcR]

lemma T_of_a_left_mem {a b c al : Game} (hal : al ∈ a.left) :
    T ⟨b, al, c⟩ ⟨a, b, c⟩ := by
  have h := T_of_left_mem (a := a) (b := c) (c := b) hal
  simpa [T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma T_of_c_left_mem {a b c cl : Game} (hcl : cl ∈ c.left) :
    T ⟨a, b, cl⟩ ⟨a, b, c⟩ := by
  have h := T_of_left_mem (a := c) (b := a) (c := b) hcl
  simpa [T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma T_of_b_right_mem {a b c br : Game} (hbr : br ∈ b.right) :
    T ⟨br, a, c⟩ ⟨a, b, c⟩ := by
  have h := T_of_right_mem (a := a) (b := c) (c := b) hbr
  simpa [T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma T_of_c_right_mem {a b c cr : Game} (hcr : cr ∈ c.right) :
    T ⟨a, b, cr⟩ ⟨a, b, c⟩ := by
  have h := T_of_right_mem (a := b) (b := a) (c := c) hcr
  simpa [T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma T_of_mem_left₁ {a b c aL : Game} (haL : aL ∈ a.left) :
    T ⟨aL, b, c⟩ ⟨a, b, c⟩ := by
  simp [T]
  linarith [birthday_lt_left haL]


/-! ## Basic order inequalities -/

lemma not_ge_left_of_le {a b aL : Game} (hab : a ≼ b) (haL : aL ∈ a.left) :
    ¬ b ≼ aL := by
  have hab' := hab
  unfold le at hab'
  exact hab'.1 aL haL

lemma not_le_right_of_le {b c cR : Game} (hbc : b ≼ c) (hcR : cR ∈ c.right) :
    ¬ cR ≼ b := by
  have hbc' := hbc
  unfold le at hbc'
  exact hbc'.2 cR hcR

theorem le_congr {x : Game} : x ≼ x := by
  apply wf_R.induction x
  intro x IH
  unfold le
  unfold R at IH
  constructor
  · intro l xl h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.1 l (by simp[left]; exact xl)
    have h_le: le l l := IH l (birthday_lt_left xl)
    contradiction
  · intro r hr h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.2 r (by simp[right]; exact hr)
    have h_le: le r r := IH r (birthday_lt_right hr)
    contradiction

theorem eq_congr {x : Game} : x ∼ x := by
  unfold eq
  constructor
  · exact le_congr
  · exact le_congr

lemma eq_of_eq {u v : Game} (h : u = v) : u ∼ v := by
  subst h
  exact eq_congr

theorem le_trans' {x y z : Game} : (x ≼ y) → (y ≼ z) → (x ≼ z) := by
  intro hxy hyz
  let P : TriGame → Prop := fun t => (t.a ≼ t.b) → (t.b ≼ t.c) → (t.a ≼ t.c)
  have hP : ∀ t : TriGame, P t := by
    intro t
    refine wf_T.induction (C := P) t ?_
    rintro ⟨a, b, c⟩ IH hab hbc
    unfold le
    constructor
    · intro aL haL hcaL
      have hb_le_aL : b ≼ aL := (IH ⟨b, c, aL⟩ (T_of_left_mem haL)) hbc hcaL
      exact not_ge_left_of_le hab haL hb_le_aL
    · intro cR hcR hcR_le_a
      have hcR_le_b : cR ≼ b := (IH ⟨cR, a, b⟩ (T_of_right_mem hcR)) hcR_le_a hab
      exact not_le_right_of_le hbc hcR hcR_le_b
  exact (hP ⟨x, y, z⟩) hxy hyz

theorem le_trans {x y z : Game} : (x ≼ y) ∧ (y ≼ z) → x ≼ z := by
  intro ⟨hxy, hyz⟩
  exact le_trans' hxy hyz

theorem eq_symm {x y : Game} : (x ∼ y) → (y ∼ x):= by
  intro hxy
  exact ⟨hxy.2, hxy.1⟩

theorem eq_trans {x y z : Game} : (x ∼ y) ∧ (y ∼ z) → x ∼ z := by
  intro habc
  unfold eq
  constructor
  · exact le_trans ⟨habc.1.1,habc.2.1⟩
  · exact le_trans ⟨habc.2.2,habc.1.2⟩

theorem lt_trans {x y z : Game} : (x ≺ y) ∧ (y ≺ z) → (x ≺ z) := by
  intro ⟨h_xy, h_yz⟩
  unfold lt
  constructor
  · apply le_trans
    exact ⟨h_xy.1, h_yz.1⟩
  · intro h_contra
    have h_z_le_y : z ≼ y := by
      apply le_trans
      exact ⟨h_contra, h_xy.1⟩
    have h_z_not_le_y := h_yz.2
    contradiction

theorem lt_of_lt_of_le {x y z : Game} (hxy : x ≺ y) (hyz : y ≼ z) : x ≺ z := by
  unfold lt
  constructor
  · exact le_trans ⟨hxy.1, hyz⟩
  · intro h_contra
    have h_y_le_x : y ≼ x := by exact le_trans ⟨hyz, h_contra⟩
    exact hxy.2 h_y_le_x

theorem lt_of_le_of_lt {x y z : Game} (hxy : x ≼ y) (hyz : y ≺ z) : x ≺ z := by
  unfold lt
  constructor
  · exact le_trans ⟨hxy, hyz.1⟩
  · intro h_contra
    have h_z_le_y : z ≼ y := by exact le_trans ⟨h_contra, hxy⟩
    exact hyz.2 h_z_le_y

lemma not_le_left {x : Game} (xL : Game) (h : xL ∈ x.left) : ¬(x.le xL) := by
  intro h_le
  rw [le] at h_le
  have h_not_refl := h_le.1 xL h
  have h_refl : xL.le xL := le_congr
  contradiction

lemma not_le_right {x : Game} (xR : Game) (h : xR ∈ x.right) : ¬(xR.le x) := by
  intro h_le
  rw [le] at h_le
  have h_not_refl := h_le.2 xR h
  have h_refl : xR.le xR := le_congr
  contradiction

/-! ## Equality of games -/

private lemma le_of_equiv_options {a b : Game}
    (hL : ∀ aL ∈ a.left, ∃ bL ∈ b.left, aL ∼ bL)
    (hR : ∀ bR ∈ b.right, ∃ aR ∈ a.right, bR ∼ aR) :
    a ≼ b := by
  unfold le
  constructor
  · intro aL haL hb_le_aL
    rcases hL aL haL with ⟨bL, hbL, hEq⟩
    exact not_le_left bL hbL (le_trans ⟨hb_le_aL, hEq.1⟩)
  · intro bR hbR hbR_le_a
    rcases hR bR hbR with ⟨aR, haR, hEq⟩
    exact not_le_right aR haR (le_trans ⟨hEq.2, hbR_le_a⟩)

theorem eq_of_equiv_options {a b : Game}
    (hL_ab : ∀ aL ∈ a.left, ∃ bL ∈ b.left, aL ∼ bL)
    (hL_ba : ∀ bL ∈ b.left, ∃ aL ∈ a.left, bL ∼ aL)
    (hR_ab : ∀ aR ∈ a.right, ∃ bR ∈ b.right, aR ∼ bR)
    (hR_ba : ∀ bR ∈ b.right, ∃ aR ∈ a.right, bR ∼ aR) :
    a ∼ b := by
  unfold eq
  constructor
  · exact le_of_equiv_options hL_ab hR_ba
  · exact le_of_equiv_options hL_ba hR_ab

end Game
