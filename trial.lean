import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic

inductive Game where
  | mk : List Game → List Game → Game

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

theorem x_le_x : ∀ (x : Game), le x x := by
  intro x
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
  · exact x_le_x x
  · exact x_le_x x


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

-- Rename for clarity
def Game.Equiv (g h : Game) : Prop :=
  le g h ∧ le h g

-- You already proved this
theorem Game.equiv_refl : ∀ (x : Game), Equiv x x := x_eq_x

-- Proof of symmetry
theorem Game.equiv_symm : ∀ (x y : Game), Equiv x y → Equiv y x := by
  intro x y h
  unfold Equiv at *
  exact And.symm h

-- Proof of transitivity
theorem Game.equiv_trans : ∀ (x y z : Game), Equiv x y → Equiv y z → Equiv x z := by
  intro x y z h_xy h_yz
  unfold Equiv at *
  have x_le_y := h_xy.1
  have y_le_x := h_xy.2
  have y_le_z := h_yz.1
  have z_le_y := h_yz.2
  constructor
  · -- Prove x ≤ z
    exact le_trans x y z ⟨x_le_y, y_le_z⟩
  · -- Prove z ≤ x
    exact le_trans z y x ⟨z_le_y, y_le_x⟩

-- This bundles Game with its equivalence relation
instance Game.setoid : Setoid Game where
  r := Game.Equiv
  iseqv := {
    refl  := by
      -- Goal is: Equiv x x
      intro x;
      exact x_eq_x x;
    symm  := by
      -- Goal is: Equiv x y → Equiv y x
      intro x y h;
      unfold Game.Equiv at *;
      exact And.symm h;
    trans := by
      -- Goal is: Equiv x y → Equiv y z → Equiv x z
      intro x y z h_xy h_yz;
      unfold Game.Equiv at *;
      constructor;
      · exact le_trans x y z ⟨h_xy.1, h_yz.1⟩;
      · exact le_trans z y x ⟨h_yz.2, h_xy.2⟩;
  }

-- A proof that `le` respects the equivalence relation.
-- This is called a "congruence" proof.
-- A proof that `le` respects the equivalence relation.
-- This is called a "congruence" proof.
theorem Game.le_congr : ∀ {a b c d : Game}, a ≈ b → c ≈ d → (le a c ↔ le b d) := by
  -- `a ≈ b` is notation for `Game.Equiv a b` because of the Setoid instance.
  -- We don't need to unfold, we can just use it.
  intro a b c d h_ab h_cd
  -- `h_ab` is a proof of `Game.Equiv a b`, which is `le a b ∧ le b a`.
  -- `h_cd` is a proof of `Game.Equiv c d`, which is `le c d ∧ le d c`.
  constructor
  · -- Direction 1: `le a c → le b d`
    intro h_ac
    -- We have:
    -- h_ab.2 : le b a
    -- h_ac   : le a c
    -- h_cd.1 : le c d
    -- We need to prove `le b d`.
    -- We can chain these together: `le b a → le a c → le c d`.
    have h_ba_ac : le b c := by
      apply Game.le_trans b a c
      exact ⟨h_ab.2, h_ac⟩
    have h_bc_cd : le b d := by
      apply Game.le_trans b c d
      exact ⟨h_ba_ac, h_cd.1⟩
    exact h_bc_cd
  · -- Direction 2: `le b d → le a c`
    intro h_bd
    -- We have:
    -- h_ab.1 : le a b
    -- h_bd   : le b d
    -- h_cd.2 : le d c
    -- We need to prove `le a c`.
    have h_ab_bd : le a d := by
      apply Game.le_trans a b d
      exact ⟨h_ab.1, h_bd⟩
    have h_ad_dc : le a c := by
      apply Game.le_trans a d c
      exact ⟨h_ab_bd, h_cd.2⟩
    exact h_ad_dc

-- ... (all your previous code) ...

-- This is the congruence proof with the correct signature for `Quotient.lift₂`.
theorem Game.le_congr_propext : ∀ (a₁ a₂ b₁ b₂ : Game), a₁ ≈ b₁ → a₂ ≈ b₂ → (le a₁ a₂ = le b₁ b₂) := by
  -- We need to prove equality of propositions, so we use `propext`
  -- which says that if two propositions are equivalent (↔), they are equal (=).
  intro a₁ a₂ b₁ b₂ h_a b_h
  apply propext
  -- Now the goal is `le a₁ a₂ ↔ le b₁ b₂`, which is what your old `le_congr` proved.
  -- Let's reuse that logic.
  constructor
  · -- Direction 1: `le a₁ a₂ → le b₁ b₂`
    intro h_a1_a2
    -- We have:
    -- h_a.2 : le b₁ a₁
    -- h_a1_a2   : le a₁ a₂
    -- b_h.1 : le a₂ b₂
    have h_b1_a2 : le b₁ a₂ := by
      apply Game.le_trans b₁ a₁ a₂
      exact ⟨h_a.2, h_a1_a2⟩
    have h_b1_b2 : le b₁ b₂ := by
      apply Game.le_trans b₁ a₂ b₂
      exact ⟨h_b1_a2, b_h.1⟩
    exact h_b1_b2
  · -- Direction 2: `le b₁ b₂ → le a₁ a₂`
    intro h_b1_b2
    -- We have:
    -- h_a.1 : le a₁ b₁
    -- h_b1_b2   : le b₁ b₂
    -- b_h.2 : le b₂ a₂
    have h_a1_b2 : le a₁ b₂ := by
      apply Game.le_trans a₁ b₁ b₂
      exact ⟨h_a.1, h_b1_b2⟩
    have h_a1_a2 : le a₁ a₂ := by
      apply Game.le_trans a₁ b₂ a₂
      exact ⟨h_a1_b2, b_h.2⟩
    exact h_a1_a2

-- Now, the instance definition will work correctly.
instance : PartialOrder (Quotient Game.setoid) where
  le := Quotient.lift₂ Game.le (fun _ _ _ _ => Game.le_congr_propext _ _ _ _ )
  le_refl := by
    intro qx
    refine Quotient.inductionOn qx ?_
    intro x
    exact x_le_x x
  le_trans := by
    intro qa qb qc
    refine Quotient.inductionOn₃ qa qb qc ?_
    intro a b c h_ab h_bc
    exact Game.le_trans a b c ⟨h_ab, h_bc⟩
  le_antisymm := by
    intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b h_ab h_ba
    apply Quotient.sound
    exact ⟨h_ab, h_ba⟩
