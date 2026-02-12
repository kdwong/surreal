import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm_dist


namespace ConwayStageInduction


/-- Pretend this is your surreal type. -/

local notation:70 x " ⊗ " y => Game.mul x y

/-- Product-rank ρ(x,y) := birthday x + birthday y. -/
def rank (x y : Surreal) : Nat := Game.birthday x + Game.birthday y


def P : Surreal → Surreal → Surreal → Surreal → Prop
| x₁, x₂, y₁, y₂ =>
    ((x₁ ⊗ y₂).add (x₂ ⊗ y₁)).le ((x₁ ⊗ y₁).add (x₂ ⊗ y₂))

/-
A α: (i) and (ii) for all products with rank < α.

You can bundle (i) and (ii) however you like; here I just put the
minimal shape: closure (IsSurreal) + left congruence.
-/
def A (α : Nat) : Prop :=
  (∀ x y, rank x y < α → IsSurreal (Game.mul x y)) ∧
  (∀ x₁ x₂ y, x₁ = x₂ → rank x₁ y < α → Game.mul x₁ y = Game.mul x₂ y)

/-
B α: (iii) for all quadruples whose 4 products are all below stage α.
I.e. all of ρ(xᵢ, yⱼ) < α for i,j ∈ {1,2}.
-/
def B (α : Nat) : Prop :=
  ∀ x₁ x₂ y₁ y₂,
    rank x₁ y₁ < α →
    rank x₁ y₂ < α →
    rank x₂ y₁ < α →
    rank x₂ y₂ < α →
    P x₁ x₂ y₁ y₂

/--
Main “two-level” induction:
At each stage `α+1`, prove `A (α+1)` first (using `B α`),
then prove `B (α+1)` (using the freshly proved `A (α+1)`).
-/
theorem stage_induction : ∀ α : Nat, A α ∧ B α := by
  intro α
  induction α with
  | zero =>
      refine And.intro ?A0 ?B0
      · refine And.intro ?i0 ?ii0
        · intro x y h
          cases Nat.not_lt_zero _ h
        · intro x₁ x₂ y hx h
          cases Nat.not_lt_zero _ h
      · intro x₁ x₂ y₁ y₂ h11 h12 h21 h22
        cases Nat.not_lt_zero _ h11
  | succ α ih =>
      -- Induction hypothesis gives everything below stage α.
      have hA_prev : A α := ih.1
      have hB_prev : B α := ih.2

      /- Step 1: prove A (α+1) using A α and B α. -/
      have hA : A (Nat.succ α) := by
        refine And.intro ?i ?ii
        · -- (i) for all x y with rank < α+1
          intro x y hxy
          -- Typical structure:
          -- by cases on rank < α or rank = α, use `hA_prev` or the new boundary proof,
          -- and inside the boundary proof invoke `hB_prev` only on strictly smaller ranks.
          -- (details omitted)
          sorry
        · -- (ii) congruence for all x₁=x₂ with rank < α+1
          intro x₁ x₂ y hx12 hxy
          -- Similar: split rank, use prev stage, handle boundary case.
          sorry

      /- Step 2: prove B (α+1) using B α and the newly proved A (α+1). -/
      have hB : B (Nat.succ α) := by
        intro x₁ x₂ y₁ y₂ h11 h12 h21 h22
        -- Typical structure:
        -- 1) reduce P(x₁,x₂:y₁,y₂) to simpler ones (inner induction on “simplicity”)
        -- 2) base cases are “xy sits between its options”, which is where you use hA.
        -- (details omitted)
        sorry

      exact And.intro hA hB

/--
How you extract (i) for a particular product xy:
pick α := rank(x,y)+1, then rank(x,y) < α, so A α gives IsSurreal(x⊗y).
-/
theorem mul_IsSurreal (x y : Surreal) :
    IsSurreal (x ⊗ y) := by
  have h := stage_induction (rank x y + 1)
  have hA : A (rank x y + 1) := h.1
  exact hA.1 x y (Nat.lt_succ_self _)

end ConwayStageInduction
