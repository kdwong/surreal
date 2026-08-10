import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm


namespace Game


/-- ## Quotient on Game is a AddCommGroup -/

instance instSetoidGame : Setoid Game where
  r a b := Game.eq a b
  iseqv :=
    ⟨
      (fun _ => Game.eq_of_eq rfl),
      (fun {_ _} h => Game.eq_symm h),
      (fun {_ _ _} h₁ h₂ => Game.eq_trans ⟨h₁, h₂⟩)
    ⟩

/-- The additive quotient of games by equivalence. -/
abbrev GameQ := Quotient (instSetoidGame : Setoid Game)

/-- Compatibility alias for the quotient-class notation. -/
abbrev q (g : Game) : GameQ := ⟦g⟧

@[simp] theorem q_sound {a b : Game} (h : a ∼ b) :
    (⟦a⟧ : GameQ) = ⟦b⟧ :=
  Quotient.sound h

@[simp] theorem q_sound_eq {a b : Game} (h : a = b) :
    (⟦a⟧ : GameQ) = ⟦b⟧ :=
  Quotient.sound (Game.eq_of_eq h)

@[simp] theorem q_eq {a b : Game} :
    (⟦a⟧ : GameQ) = ⟦b⟧ ↔ a ∼ b :=
  Quotient.eq

instance : Zero GameQ := ⟨⟦Game.zero⟧⟩

instance : Add GameQ where
  add := Quotient.map₂ Game.add <| by
    intro a a' ha b b' hb
    exact Game.add_equal ⟨ha, hb⟩

instance : Neg GameQ where
  neg := Quotient.map Game.neg <| by
    intro a b hab
    exact Game.neg_congr_left hab

@[simp] theorem q_zero : (⟦Game.zero⟧ : GameQ) = 0 := rfl

@[simp] theorem q_add (a b : Game) :
    (⟦a.add b⟧ : GameQ) = ⟦a⟧ + ⟦b⟧ := rfl

@[simp] theorem q_neg (a : Game) :
    (⟦Game.neg a⟧ : GameQ) = -⟦a⟧ := rfl

instance : AddCommGroup GameQ where
  zero := (0 : GameQ)
  add := fun x y => x + y
  neg := fun x => -x

  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change (⟦(a.add b).add c⟧ : GameQ) = ⟦a.add (b.add c)⟧
    exact q_sound_eq (Game.add_assoc (a := a) (b := b) (c := c))

  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change (⟦Game.zero.add a⟧ : GameQ) = ⟦a⟧
    exact q_sound_eq (Game.zero_add' (a := a))

  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change (⟦a.add Game.zero⟧ : GameQ) = ⟦a⟧
    exact q_sound_eq (Game.add_zero' (a := a))

  nsmul := nsmulRec
  zsmul := zsmulRec

  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change (⟦(Game.neg a).add a⟧ : GameQ) = ⟦Game.zero⟧
    exact q_sound (Game.neg_add a)

  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change (⟦a.add b⟧ : GameQ) = ⟦b.add a⟧
    exact q_sound (Game.add_comm (a := a) (b := b))

@[simp] theorem q_mulOpt4 (xOpt Y X yOpt : Game) :
    (⟦Game.mulOpt4 xOpt Y X yOpt⟧ : GameQ) =
      ⟦xOpt.mul Y⟧ + ⟦X.mul yOpt⟧ - ⟦xOpt.mul yOpt⟧ := by
  simp [Game.mulOpt4, sub_eq_add_neg]

instance : LE GameQ where
  le := Quotient.lift₂ Game.le
    (by
      intro a a' b b' ha hb
      apply propext
      constructor
      · intro hab
        exact Game.le_trans ⟨ha.2, Game.le_trans ⟨hab, hb.1⟩⟩
      · intro ha'b'
        exact Game.le_trans ⟨ha.1, Game.le_trans ⟨ha'b', hb.2⟩⟩)

@[simp] theorem q_le {a b : Game} :
    ((⟦a⟧ : GameQ) ≤ ⟦b⟧) ↔ a ≼ b :=
  Iff.rfl

instance : PartialOrder GameQ where
  le := (· ≤ ·)

  le_refl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change Game.le a a
    exact Game.le_congr

  le_trans := by
    intro x y z hxy hyz
    revert hxy hyz
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c hxy hyz
    change Game.le a c
    change Game.le a b at hxy
    change Game.le b c at hyz
    exact Game.le_trans ⟨hxy, hyz⟩

  le_antisymm := by
    intro x y hxy hyx
    revert hxy hyx
    refine Quotient.inductionOn₂ x y ?_
    intro a b hxy hyx
    apply Quotient.sound
    change Game.eq a b
    constructor
    · change Game.le a b at hxy
      exact hxy
    · change Game.le b a at hyx
      exact hyx

@[simp] theorem q_lt {a b : Game} :
    ((⟦a⟧ : GameQ) < ⟦b⟧) ↔ a ≺ b :=
  Iff.rfl

noncomputable instance : IsOrderedAddMonoid GameQ where
  add_le_add_left := by
    intro a b hab c
    revert hab
    refine Quotient.inductionOn₃ a b c ?_
    intro a' b' c' hab
    change Game.le (Game.add c' a') (Game.add c' b')
    have h1 : Game.le (Game.add c' a') (Game.add a' c') :=
      (Game.add_comm (a := c') (b := a')).1
    have h2 : Game.le (Game.add a' c') (Game.add b' c') :=
      Game.add_le_add_right (a := a') (b := b') (c := c') hab
    have h3 : Game.le (Game.add b' c') (Game.add c' b') :=
      (Game.add_comm (a := b') (b := c')).1
    exact Game.le_trans ⟨h1, Game.le_trans ⟨h2, h3⟩⟩


theorem eq_of_q_eq {u v : Game} (h : (⟦u⟧ : GameQ) = ⟦v⟧) : u ∼ v :=
  q_eq.mp h

end Game


namespace Surreal

/-- ## Quotient on Game is an **ORDERED** AddCommGroup -/



def Equiv (g h : Surreal) : Prop := le g h ∧ le h g

instance setoid : Setoid Surreal where
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

theorem le_congr_propext {a₁ a₂ b₁ b₂ : Surreal} :
  (a₁ ≈ b₁) → (a₂ ≈ b₂) → (le a₁ a₂ = le b₁ b₂) := by
  intro h_a b_h
  apply propext
  constructor
  · intro h_a1_a2
    have h_b1_a2 : le b₁ a₂ := by
      apply Game.le_trans
      exact ⟨h_a.2, h_a1_a2⟩
    have h_b1_b2 : le b₁ b₂ := by
      apply Game.le_trans
      exact ⟨h_b1_a2, b_h.1⟩
    exact h_b1_b2
  · intro h_b1_b2
    have h_a1_b2 : le a₁ b₂ := by
      apply Game.le_trans
      exact ⟨h_a.1, h_b1_b2⟩
    have h_a1_a2 : le a₁ a₂ := by
      apply Game.le_trans
      exact ⟨h_a1_b2, b_h.2⟩
    exact h_a1_a2

theorem add_congr (a₁ a₂ : Surreal) (h₁ : a₁ ≈ a₂) (b₁ b₂ : Surreal) (h₂ : b₁ ≈ b₂) :
  a₁.add b₁ ≈ a₂.add b₂ := by
  constructor
  · apply Game.add_le_add
    exact ⟨h₁.1, h₂.1⟩
  · apply Game.add_le_add
    exact ⟨h₁.2, h₂.2⟩

def SurrealNumber := Quotient Surreal.setoid

/-- Equivalent underlying games determine the same surreal number. -/
theorem SurrealNumber.sound_val {a b : Surreal} (h : Game.eq a.val b.val) :
    (⟦a⟧ : SurrealNumber) = ⟦b⟧ := by
  apply Quotient.sound
  exact h

def SurrealNumber.add : SurrealNumber → SurrealNumber → SurrealNumber :=
  Quotient.map₂ Surreal.add Surreal.add_congr

instance : Add SurrealNumber where add := SurrealNumber.add
instance : Zero SurrealNumber where zero := ⟦sr_zero⟧
instance : One SurrealNumber where one := ⟦sr_one⟧

def neg (s : Surreal) : Surreal := ⟨Game.neg s.val, Surreal.neg_isSurreal s⟩

theorem neg_congr (a b : Surreal) (h : a ≈ b) : Surreal.neg a ≈ Surreal.neg b := by
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
    apply SurrealNumber.sound_val
    change Game.eq ((a.val.add b.val).add c.val) (a.val.add (b.val.add c.val))
    exact Game.eq_of_eq Game.add_assoc

  add_zero := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply SurrealNumber.sound_val
    change Game.eq (a.val.add Game.zero) a.val
    exact Game.eq_of_eq Game.add_zero'

  zero_add := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply SurrealNumber.sound_val
    change Game.eq (Game.zero.add a.val) a.val
    exact Game.eq_of_eq Game.zero_add'

  add_comm := by
    intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b
    apply SurrealNumber.sound_val
    change Game.eq (Game.add a.val b.val) (Game.add b.val a.val)
    exact Game.add_comm

  neg_add_cancel := by
    intro qa
    refine Quotient.inductionOn qa ?_
    intro a
    apply SurrealNumber.sound_val
    change Game.eq (Game.add (Game.neg a.val) a.val) Game.zero
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

end Surreal
