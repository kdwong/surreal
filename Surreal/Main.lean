import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm_dist
import Surreal.mult_asso


def Surreal.Equiv (g h : Surreal) : Prop := le g h ∧ le h g

instance Surreal.setoid : Setoid Surreal where
  r := Surreal.Equiv
  iseqv := {
    refl  := by
      intro x;
      exact Game.eq_congr;
    symm  := by
      intro x y h;
      unfold Surreal.Equiv at *;
      exact And.symm h;
    trans := by
      intro x y z h_xy h_yz;
      unfold Surreal.Equiv at *;
      constructor;
      · exact le_trans ⟨h_xy.1, h_yz.1⟩;
      · exact le_trans ⟨h_yz.2, h_xy.2⟩;
  }


theorem Surreal.le_congr_propext {a₁ a₂ b₁ b₂ : Surreal} :
  (a₁ ≈ b₁) → (a₂ ≈ b₂) → (le a₁ a₂ = le b₁ b₂) := by
  intro h_a b_h
  apply propext
  constructor
  · -- Direction 1: `le a₁ a₂ → le b₁ b₂`
    intro h_a1_a2
    have h_b1_a2 : le b₁ a₂ := by
      apply Game.le_trans
      exact ⟨h_a.2, h_a1_a2⟩
    have h_b1_b2 : le b₁ b₂ := by
      apply Game.le_trans
      exact ⟨h_b1_a2, b_h.1⟩
    exact h_b1_b2
  · -- Direction 2: `le b₁ b₂ → le a₁ a₂`
    intro h_b1_b2
    have h_a1_b2 : le a₁ b₂ := by
      apply Game.le_trans
      exact ⟨h_a.1, h_b1_b2⟩
    have h_a1_a2 : le a₁ a₂ := by
      apply Game.le_trans
      exact ⟨h_a1_b2, b_h.2⟩
    exact h_a1_a2

theorem Surreal.add_congr (a₁ a₂ : Surreal) (h₁ : a₁ ≈ a₂) (b₁ b₂ : Surreal) (h₂ : b₁ ≈ b₂) :
  a₁.add b₁ ≈ a₂.add b₂ := by
  constructor
  · apply Game.add_le_add
    exact ⟨h₁.1, h₂.1⟩
  · apply Game.add_le_add
    exact ⟨h₁.2, h₂.2⟩

def SurrealNumber := Quotient Surreal.setoid

def SurrealNumber.add : SurrealNumber → SurrealNumber → SurrealNumber :=
  Quotient.map₂ Surreal.add Surreal.add_congr

instance : Add SurrealNumber where add := SurrealNumber.add

instance : Zero SurrealNumber where zero := ⟦sr_zero⟧

instance : One SurrealNumber where one := ⟦sr_one⟧

instance : Add SurrealNumber where add := SurrealNumber.add

def Surreal.neg (s : Surreal) : Surreal := ⟨Game.neg s.val, Surreal.neg_isSurreal s⟩

theorem Surreal.neg_congr (a b : Surreal) (h : a ≈ b) : Surreal.neg a ≈ Surreal.neg b := by
  constructor
  · rw [Surreal.le, Surreal.neg, Surreal.neg]
    dsimp
    rw [← Game.neg_le_neg]
    exact h.2
  · rw [Surreal.le, Surreal.neg, Surreal.neg]
    dsimp
    rw [← Game.neg_le_neg]
    exact h.1

def SurrealNumber.neg : SurrealNumber → SurrealNumber :=
  Quotient.map Surreal.neg Surreal.neg_congr

instance : Neg SurrealNumber where neg := SurrealNumber.neg

noncomputable instance : LinearOrder SurrealNumber where
  le := Quotient.lift₂ Surreal.le (fun _ _ _ _ => Surreal.le_congr_propext)
  le_refl := by
    intro qx
    refine Quotient.inductionOn qx ?_
    intro x
    exact (Game.eq_congr).1
  le_trans := by
    intro qa qb qc
    refine Quotient.inductionOn₃ qa qb qc ?_
    intro a b c h_ab h_bc
    exact Game.le_trans ⟨h_ab, h_bc⟩
  le_antisymm := by
    intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b h_ab h_ba
    apply Quotient.sound
    exact ⟨h_ab, h_ba⟩
  le_total := by
    intro qa qb
    induction qa using Quotient.inductionOn
    induction qb using Quotient.inductionOn
    exact Surreal.totality
  toDecidableLE := Classical.decRel _

noncomputable instance : AddCommGroup SurrealNumber where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := fun a b => a + (-b)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro qa qb qc
    refine Quotient.inductionOn₃ qa qb qc ?_
    intro a b c
    apply Quotient.sound
    have h_eq : Surreal.add (Surreal.add a b) c = Surreal.add a (Surreal.add b c) := by
      apply Subtype.ext
      dsimp [Surreal.add]
      rw [Game.add_assoc]
    rw [h_eq]

  add_zero := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply Quotient.sound
    change (Surreal.add a sr_zero) ≈ a
    have h_eq : Surreal.add a sr_zero = a := by
      apply Subtype.ext
      dsimp [Surreal.add]
      simp [sr_zero]
      rw [Game.add_zero]
    rw [h_eq]

  zero_add := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply Quotient.sound
    change (Surreal.add sr_zero a) ≈ a
    have h_eq : Surreal.add sr_zero a = a := by
      apply Subtype.ext
      dsimp [Surreal.add]
      simp [sr_zero]
      rw [Game.zero_add]
    rw [h_eq]

  add_comm := by
    intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b
    apply Quotient.sound
    change Game.eq (Game.add a.val b.val) (Game.add b.val a.val)
    exact Game.add_comm

  neg_add_cancel := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply Quotient.sound
    change Game.eq (Game.add (Game.neg a.val) a.val) zero
    exact Surreal.neg_add a

noncomputable instance : IsOrderedAddMonoid SurrealNumber where
    add_le_add_left := by
      intro a b h_ab c
      revert h_ab
      refine Quotient.inductionOn₃ a b c ?_
      intro a_val b_val c_val h_ab
      change Game.le (Game.add c_val.val a_val.val) (Game.add c_val.val b_val.val)
      apply Game.add_le_add
      constructor
      · exact Game.le_congr
      · exact h_ab

example {a b : SurrealNumber} : |a + b| ≤ |a| + |b| := by exact abs_add_le a b

example {a b c : SurrealNumber} (h : a ≤ b) : a - c ≤ b - c := by apply sub_le_sub_right h

-------------------------------------------
-- Define Mul
-------------------------------------------

theorem Surreal.mul_congr (a₁ a₂ : Surreal) (h₁ : a₁ ≈ a₂) (b₁ b₂ : Surreal) (h₂ : b₁ ≈ b₂) :
    Surreal.mul a₁ b₁ ≈ Surreal.mul a₂ b₂ :=
  Game.mul_equal ⟨h₁, h₂⟩

def SurrealNumber.mul : SurrealNumber → SurrealNumber → SurrealNumber :=
  Quotient.map₂ Surreal.mul Surreal.mul_congr

instance : Mul SurrealNumber where
  mul := SurrealNumber.mul

-------------------------------------------
-- Prove theorem of mul
-------------------------------------------

theorem SurrealNumber.mul_comm (a b : SurrealNumber) : a * b = b * a := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  apply Quotient.sound
  rename_i a b
  change Game.eq (a.val.mul b.val) (b.val.mul a.val)
  exact Game.mul_comm

theorem SurrealNumber.mul_assoc (a b c : SurrealNumber) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply Quotient.sound
  rename_i a b c
  change Game.eq ((a.val.mul b.val).mul c.val) (a.val.mul (b.val.mul c.val))
  exact Game.mul_assoc

theorem SurrealNumber.one_mul (a : SurrealNumber) : 1 * a = a := by
  induction a using Quotient.ind
  apply Quotient.sound
  rename_i a
  change Game.eq (one.mul a.val) a.val
  exact Game.one_mul
theorem SurrealNumber.mul_one (a : SurrealNumber) : a * 1 = a := by
  induction a using Quotient.ind
  apply Quotient.sound
  rename_i a
  change Game.eq (a.val.mul one) a.val
  exact Game.mul_one

theorem SurrealNumber.zero_mul (a : SurrealNumber) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply Quotient.sound
  rename_i a
  change Game.eq (zero.mul a.val) zero
  exact Game.zero_mul a.val


theorem SurrealNumber.mul_zero (a : SurrealNumber) : a * 0 = 0 := by
  induction a using Quotient.ind
  apply Quotient.sound
  rename_i a
  change Game.eq (a.val.mul zero) zero
  exact Game.mul_zero a.val

-------------------------------------------
-- Distribution
-------------------------------------------

theorem SurrealNumber.left_distrib (a b c : SurrealNumber) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply Quotient.sound
  rename_i a b c
  change Game.eq (a.val.mul (b.val.add c.val)) ((a.val.mul b.val).add (a.val.mul c.val))
  exact Game.mul_distrib


theorem SurrealNumber.right_distrib (a b c : SurrealNumber) : (a + b) * c = a * c + b * c := by
  calc (a + b) * c = c * (a + b) := SurrealNumber.mul_comm _ _
    _ = c * a + c * b := SurrealNumber.left_distrib _ _ _
    _ = a * c + c * b := by rw [SurrealNumber.mul_comm c a]
    _ = a * c + b * c := by rw [SurrealNumber.mul_comm c b]

-------------------------------------------
-- Put all to Comring
-------------------------------------------


noncomputable instance : CommRing SurrealNumber where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc := SurrealNumber.mul_assoc
  mul_comm := SurrealNumber.mul_comm
  one_mul := SurrealNumber.one_mul
  mul_one := SurrealNumber.mul_one
  left_distrib := SurrealNumber.left_distrib
  right_distrib := SurrealNumber.right_distrib
  zero_mul := SurrealNumber.zero_mul
  mul_zero := SurrealNumber.mul_zero

-------------------------------------------
-- Example
-------------------------------------------

example (a b c : SurrealNumber) : a * (b + c) = a * b + a * c := mul_add a b c
example (a b c : SurrealNumber) : (a + b) * c = a * c + b * c := add_mul a b c
example (a : SurrealNumber) : a * 1 = a := mul_one a
example (a b : SurrealNumber) : a * b = b * a := mul_comm a b
