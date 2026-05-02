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
import Surreal.mult_comm
import Surreal.mult_asso
import Surreal.commgroup


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
