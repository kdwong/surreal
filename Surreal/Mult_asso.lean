import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm_dist

namespace ConwayStrategy

local notation:70 x " ⊗ " y => Game.mul x y
local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ∼ " y => Game.eq x y
local notation:70 x " ≼ " y => Game.le x y
local notation:70 x " ≺ " y => Game.lt x y




lemma game_le_trans {a b c : Game} (h1 : a ≼ b) (h2 : b ≼ c) : a ≼ c :=
  Game.le_trans ⟨h1, h2⟩


lemma game_eq_trans {a b c : Game} (h1 : a ∼ b) (h2 : b ∼ c) : a ∼ c :=
  Game.eq_trans ⟨h1, h2⟩

lemma game_lt_of_le_of_lt {a b c : Game} (h1 : a ≼ b) (h2 : b ≺ c) : a ≺ c :=
  Game.lt_of_le_of_lt h1 h2

lemma Game.add_le_add_of_le_of_eq {a b c d : Game}
    (hab : a ≼ b) (hcd : c ∼ d) : (a ⊕ c) ≼ (b ⊕ d) := by
  apply Game.add_le_add
  exact ⟨hab, hcd.1⟩

lemma game_add_le_add_right {a b c : Game} (h : a ≼ b) : (a ⊕ c) ≼ (b ⊕ c) := by
  apply Game.add_le_add_of_le_of_eq h Game.eq_congr

lemma Game.sub_le_iff {a b c : Game} :
    ((a ⊕ b.neg) ≼ c) ↔ a ≼ (c ⊕ b) := by
  constructor
  · intro h
    have h1 := Game.add_le_add_of_le_of_eq h (Game.eq_congr (x := b))
    have assoc : ((a.add b.neg).add b).eq (a.add (b.neg.add b)) :=
      Game.eq_of_eq Game.add_assoc
    have inv : (b.neg.add b).eq zero := Game.neg_add b
    have id : (a.add zero).eq a := Game.eq_of_eq Game.add_zero
    refine Game.le_trans ⟨?_, h1⟩
    refine Game.le_trans ⟨?_, assoc.2⟩
    refine Game.le_trans ⟨?_, Game.add_le_add_of_le_of_eq Game.le_congr inv.symm⟩
    exact id.2
  · intro h
    have h1 := Game.add_le_add_of_le_of_eq h (Game.eq_congr (x := b.neg))
    have assoc : ((c.add b).add b.neg).eq (c.add (b.add b.neg)) :=
      Game.eq_of_eq Game.add_assoc
    have inv : (b.add b.neg).eq zero := Game.add_neg b
    have id : (c.add zero).eq c := Game.eq_of_eq Game.add_zero
    refine Game.le_trans ⟨h1, ?_⟩
    refine Game.le_trans ⟨assoc.1, ?_⟩
    refine Game.le_trans ⟨Game.add_le_add_of_le_of_eq Game.le_congr inv, ?_⟩
    exact id.1


lemma P_ineq_rearrange {a b c d : Game} :
    (((a ⊕ b) ⊕ c.neg) ≼ d) ↔ (a ⊕ b) ≼ (d ⊕ c) := by
  constructor
  · intro h
    have h1 := Game.add_le_add_of_le_of_eq h (Game.eq_congr (x := c))
    have assoc : (((a.add b).add c.neg).add c).eq ((a.add b).add (c.neg.add c)) :=
      Game.eq_of_eq Game.add_assoc
    have inv : (c.neg.add c).eq zero := Game.neg_add c
    have id : ((a.add b).add zero).eq (a.add b) := Game.eq_of_eq Game.add_zero
    refine Game.le_trans ⟨?_, h1⟩
    refine Game.le_trans ⟨?_, assoc.2⟩
    refine Game.le_trans ⟨?_, Game.add_le_add_of_le_of_eq Game.le_congr inv.symm⟩
    exact id.2

  · intro h
    have h1 := Game.add_le_add_of_le_of_eq h (Game.eq_congr (x := c.neg))
    have assoc : ((d.add c).add c.neg).eq (d.add (c.add c.neg)) :=
      Game.eq_of_eq Game.add_assoc
    have inv : (c.add c.neg).eq zero := Game.add_neg c
    have id : (d.add zero).eq d := Game.eq_of_eq Game.add_zero
    refine Game.le_trans ⟨h1, ?_⟩
    refine Game.le_trans ⟨assoc.1, ?_⟩
    refine Game.le_trans ⟨Game.add_le_add_of_le_of_eq Game.le_congr inv, ?_⟩
    exact id.1

def prod_rank (x y : Game) : Nat := Game.birthday x + Game.birthday y

lemma rank_lt_left_left {x y xL : Game} (hxL : xL ∈ x.left) : prod_rank xL y < prod_rank x y := by
  unfold prod_rank
  have hx' := Game.birthday_lt_left hxL
  linarith

lemma rank_lt_left_right {x y xR : Game} (hxR : xR ∈ x.right) : prod_rank xR y < prod_rank x y := by
  unfold prod_rank
  have hx' := Game.birthday_lt_right hxR
  linarith

lemma rank_lt_right_left {x y yL : Game} (hyL : yL ∈ y.left) : prod_rank x yL < prod_rank x y := by
  unfold prod_rank
  have hy' := Game.birthday_lt_left hyL
  linarith

lemma rank_lt_right_right {x y yR : Game}
(hyR : yR ∈ y.right) : prod_rank x yR < prod_rank x y := by
  unfold prod_rank
  have hy' := Game.birthday_lt_right hyR
  linarith



def PropA (α : Nat) : Prop :=
  (∀ x y : Game, IsSurreal x → IsSurreal y → prod_rank x y < α → IsSurreal (x ⊗ y)) ∧
  (∀ x₁ x₂ y : Game, IsSurreal x₁ → IsSurreal x₂ → IsSurreal y → (x₁ = x₂)
   → prod_rank x₁ y < α → (x₁ ⊗ y) = (x₂ ⊗ y))

def PropB (α : Nat) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : Game,
  IsSurreal x₁ → IsSurreal x₂ → IsSurreal y₁ → IsSurreal y₂ →
  prod_rank x₁ y₁ < α → prod_rank x₁ y₂ < α →
  prod_rank x₂ y₁ < α → prod_rank x₂ y₂ < α →
  (x₁ ≺ x₂) → (y₁ ≺ y₂) →
    ((x₁ ⊗ y₂) ⊕ (x₂ ⊗ y₁)) ≺ ((x₁ ⊗ y₁) ⊕ (x₂ ⊗ y₂))


lemma prove_A_part_i (x y : Surreal) {α : Nat}
    (hrank : prod_rank x y ≤ α)
    (ih_B : PropB α) :
    ∀ L_opt ∈ (x.val ⊗ y.val).left, ∀ R_opt ∈ (x.val ⊗ y.val).right, L_opt ≺ R_opt := by
  intro L_opt hL R_opt hR
  rw [mem_mul_left] at hL
  rw [mem_mul_right] at hR

  rcases hL with ⟨xL1, hxL1, yL1, hyL1, rfl⟩ | ⟨xR1, hxR1, yR1, hyR1, rfl⟩
  <;> rcases hR with ⟨xL2, hxL2, yR2, hyR2, rfl⟩ | ⟨xR2, hxR2, yL2, hyL2, rfl⟩

  · by_cases h_lt : xL1 ≺ xL2
    · have hxL1S : IsSurreal xL1 := by
        have hxS := x.property
        unfold IsSurreal at hxS
        exact hxS.2.1 xL1 hxL1
      have hxL2S : IsSurreal xL2 := by
        have hxS := x.property
        unfold IsSurreal at hxS
        exact hxS.2.1 xL2 hxL2
      have hyL1S : IsSurreal yL1 := by
        have hyS := y.property
        unfold IsSurreal at hyS
        exact hyS.2.1 yL1 hyL1
      have hyR2S : IsSurreal yR2 := by
        have hyS := y.property
        unfold IsSurreal at hyS
        exact hyS.2.2 yR2 hyR2

      let sxL1 : Surreal := ⟨xL1, hxL1S⟩
      let sxL2 : Surreal := ⟨xL2, hxL2S⟩
      let syL1 : Surreal := ⟨yL1, hyL1S⟩
      let syR2 : Surreal := ⟨yR2, hyR2S⟩

      have hyL1_lt_y : yL1 ≺ y := by
        exact (xL_x_xR (x := y)).1 syL1 hyL1
      have hy_lt_yR2 : y ≺ yR2 := by
        exact (xL_x_xR (x := y)).2 syR2 hyR2
      have hxL2_lt_x : xL2 ≺ x := by
        exact (xL_x_xR (x := x)).1 sxL2 hxL2
      have hyL1_lt_yR2 : yL1 ≺ yR2 := by
        exact Game.lt_trans ⟨hyL1_lt_y, hy_lt_yR2⟩

      have h11 : prod_rank xL1 yL1 < α := by
        apply lt_of_lt_of_le _ hrank
        unfold prod_rank
        have hx' := Game.birthday_lt_left hxL1
        have hy' := Game.birthday_lt_left hyL1
        linarith
      have h12 : prod_rank xL1 y < α := by
        apply lt_of_lt_of_le _ hrank
        exact rank_lt_left_left hxL1
      have h21 : prod_rank xL2 yL1 < α := by
        apply lt_of_lt_of_le _ hrank
        unfold prod_rank
        have hx' := Game.birthday_lt_left hxL2
        have hy' := Game.birthday_lt_left hyL1
        linarith
      have h22 : prod_rank xL2 y < α := by
        apply lt_of_lt_of_le _ hrank
        exact rank_lt_left_left hxL2
      have h23 : prod_rank xL2 yR2 < α := by
        apply lt_of_lt_of_le _ hrank
        unfold prod_rank
        have hx' := Game.birthday_lt_left hxL2
        have hy' := Game.birthday_lt_right hyR2
        linarith
      have h31 : prod_rank x yL1 < α := by
        apply lt_of_lt_of_le _ hrank
        exact rank_lt_right_left hyL1
      have h32 : prod_rank x yR2 < α := by
        apply lt_of_lt_of_le _ hrank
        exact rank_lt_right_right hyR2

      have hP₁ :
          ((xL1 ⊗ y.val).add (xL2 ⊗ yL1)) ≺ ((xL1 ⊗ yL1).add (xL2 ⊗ y.val)) := by
        exact ih_B xL1 xL2 yL1 y.val
          hxL1S hxL2S hyL1S y.property
          h11 h12 h21 h22 h_lt hyL1_lt_y

      have hP₂ :
          ((xL2 ⊗ yR2).add (x.val ⊗ yL1)) ≺ ((xL2 ⊗ yL1).add (x.val ⊗ yR2)) := by
        exact ih_B xL2 x.val yL1 yR2
          hxL2S x.property hyL1S hyR2S
          h21 h23 h31 h32 hxL2_lt_x hyL1_lt_yR2

      have h_mid₁ :
          (((xL1 ⊗ y.val).add (x.val ⊗ yL1)).add (Game.neg (xL1 ⊗ yL1))) ≺
          (((xL2 ⊗ y.val).add (x.val ⊗ yL1)).add (Game.neg (xL2 ⊗ yL1))) := by
        let A := xL1 ⊗ y.val
        let B := xL2 ⊗ yL1
        let C := xL1 ⊗ yL1
        let D := xL2 ⊗ y.val
        let X := x.val ⊗ yL1

        have h1 : ((A.add B).add (Game.neg C)) ≺ ((C.add D).add (Game.neg C)) := by
          exact Game.add_lt_le ⟨hP₁, Game.le_congr⟩

        have h1_rhs_eq : ((C.add D).add (Game.neg C)).eq D := by
          have e1 : ((C.add D).add (Game.neg C)).eq ((D.add C).add (Game.neg C)) := by
            exact Game.add_equal ⟨Game.add_comm, Game.eq_congr⟩
          have e2 : ((D.add C).add (Game.neg C)).eq (D.add (C.add (Game.neg C))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e3 : (D.add (C.add (Game.neg C))).eq (D.add zero) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_neg C⟩
          have e4 : (D.add zero).eq D := by
            exact Game.eq_of_eq Game.add_zero
          exact game_eq_trans (game_eq_trans (game_eq_trans e1 e2) e3) e4

        have h2 : ((A.add B).add (Game.neg C)) ≺ D := by
          exact Game.lt_of_lt_of_le h1 h1_rhs_eq.1

        have h2_lhs_eq : ((A.add B).add (Game.neg C)).eq ((A.add (Game.neg C)).add B) := by
          have e1 : ((A.add B).add (Game.neg C)).eq (A.add (B.add (Game.neg C))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : (A.add (B.add (Game.neg C))).eq (A.add ((Game.neg C).add B)) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_comm⟩
          have e3 : ((A.add (Game.neg C)).add B).eq (A.add ((Game.neg C).add B)) := by
            exact Game.eq_of_eq Game.add_assoc
          exact game_eq_trans (game_eq_trans e1 e2) e3.symm

        have h3 : ((A.add (Game.neg C)).add B) ≺ D := by
          exact Game.lt_of_le_of_lt h2_lhs_eq.2 h2

        have h4 : (((A.add (Game.neg C)).add B).add (Game.neg B)) ≺ (D.add (Game.neg B)) := by
          exact Game.add_lt_le ⟨h3, Game.le_congr⟩

        have h4_lhs_eq :
        (((A.add (Game.neg C)).add B).add (Game.neg B)).eq (A.add (Game.neg C)) := by
          have e1 : (((A.add (Game.neg C)).add B).add (Game.neg B)).eq
              ((A.add (Game.neg C)).add (B.add (Game.neg B))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : ((A.add (Game.neg C)).add (B.add (Game.neg B))).eq
              ((A.add (Game.neg C)).add zero) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_neg B⟩
          have e3 : ((A.add (Game.neg C)).add zero).eq (A.add (Game.neg C)) := by
            exact Game.eq_of_eq Game.add_zero
          exact game_eq_trans (game_eq_trans e1 e2) e3

        have h5 : (A.add (Game.neg C)) ≺ (D.add (Game.neg B)) := by
          exact Game.lt_of_le_of_lt h4_lhs_eq.2 h4

        have h6 : ((A.add (Game.neg C)).add X) ≺ ((D.add (Game.neg B)).add X) := by
          exact Game.add_lt_le ⟨h5, Game.le_congr⟩

        have h6_lhs_eq : ((A.add (Game.neg C)).add X).eq ((A.add X).add (Game.neg C)) := by
          have e1 : ((A.add (Game.neg C)).add X).eq (A.add ((Game.neg C).add X)) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : (A.add ((Game.neg C).add X)).eq (A.add (X.add (Game.neg C))) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_comm⟩
          have e3 : ((A.add X).add (Game.neg C)).eq (A.add (X.add (Game.neg C))) := by
            exact Game.eq_of_eq Game.add_assoc
          exact game_eq_trans (game_eq_trans e1 e2) e3.symm

        have h6_rhs_eq : ((D.add (Game.neg B)).add X).eq ((D.add X).add (Game.neg B)) := by
          have e1 : ((D.add (Game.neg B)).add X).eq (D.add ((Game.neg B).add X)) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : (D.add ((Game.neg B).add X)).eq (D.add (X.add (Game.neg B))) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_comm⟩
          have e3 : ((D.add X).add (Game.neg B)).eq (D.add (X.add (Game.neg B))) := by
            exact Game.eq_of_eq Game.add_assoc
          exact game_eq_trans (game_eq_trans e1 e2) e3.symm

        exact Game.lt_of_le_of_lt h6_lhs_eq.2 (Game.lt_of_lt_of_le h6 h6_rhs_eq.1)

      have h_mid₂ :
          (((xL2 ⊗ y.val).add (x.val ⊗ yL1)).add (Game.neg (xL2 ⊗ yL1))) ≺
          (((xL2 ⊗ y.val).add (x.val ⊗ yR2)).add (Game.neg (xL2 ⊗ yR2))) := by
        let A := xL2 ⊗ yR2
        let B := x.val ⊗ yL1
        let C := xL2 ⊗ yL1
        let D := x.val ⊗ yR2
        let E := xL2 ⊗ y.val

        have h1 : ((A.add B).add (Game.neg C)) ≺ ((C.add D).add (Game.neg C)) := by
          exact Game.add_lt_le ⟨hP₂, Game.le_congr⟩

        have h1_rhs_eq : ((C.add D).add (Game.neg C)).eq D := by
          have e1 : ((C.add D).add (Game.neg C)).eq ((D.add C).add (Game.neg C)) := by
            exact Game.add_equal ⟨Game.add_comm, Game.eq_congr⟩
          have e2 : ((D.add C).add (Game.neg C)).eq (D.add (C.add (Game.neg C))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e3 : (D.add (C.add (Game.neg C))).eq (D.add zero) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_neg C⟩
          have e4 : (D.add zero).eq D := by
            exact Game.eq_of_eq Game.add_zero
          exact game_eq_trans (game_eq_trans (game_eq_trans e1 e2) e3) e4

        have h2 : ((A.add B).add (Game.neg C)) ≺ D := by
          exact Game.lt_of_lt_of_le h1 h1_rhs_eq.1

        have h2_lhs_eq : ((A.add B).add (Game.neg C)).eq ((B.add (Game.neg C)).add A) := by
          have e1 : ((A.add B).add (Game.neg C)).eq (A.add (B.add (Game.neg C))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : (A.add (B.add (Game.neg C))).eq ((B.add (Game.neg C)).add A) := by
            exact Game.add_comm
          exact game_eq_trans e1 e2

        have h3 : ((B.add (Game.neg C)).add A) ≺ D := by
          exact Game.lt_of_le_of_lt h2_lhs_eq.2 h2

        have h4 : (((B.add (Game.neg C)).add A).add (Game.neg A)) ≺ (D.add (Game.neg A)) := by
          exact Game.add_lt_le ⟨h3, Game.le_congr⟩

        have h4_lhs_eq :
        (((B.add (Game.neg C)).add A).add (Game.neg A)).eq (B.add (Game.neg C)) := by
          have e1 : (((B.add (Game.neg C)).add A).add (Game.neg A)).eq
              ((B.add (Game.neg C)).add (A.add (Game.neg A))) := by
            exact Game.eq_of_eq Game.add_assoc
          have e2 : ((B.add (Game.neg C)).add (A.add (Game.neg A))).eq
              ((B.add (Game.neg C)).add zero) := by
            exact Game.add_equal ⟨Game.eq_congr, Game.add_neg A⟩
          have e3 : ((B.add (Game.neg C)).add zero).eq (B.add (Game.neg C)) := by
            exact Game.eq_of_eq Game.add_zero
          exact game_eq_trans (game_eq_trans e1 e2) e3

        have h5 : (B.add (Game.neg C)) ≺ (D.add (Game.neg A)) := by
          exact Game.lt_of_le_of_lt h4_lhs_eq.2 h4

        have h6 : ((B.add (Game.neg C)).add E) ≺ ((D.add (Game.neg A)).add E) := by
          exact Game.add_lt_le ⟨h5, Game.le_congr⟩

        have h6_lhs_eq : ((B.add (Game.neg C)).add E).eq ((E.add B).add (Game.neg C)) := by
          have e1 : ((B.add (Game.neg C)).add E).eq ((E.add B).add (Game.neg C)) := by
            have e1a : ((B.add (Game.neg C)).add E).eq (E.add (B.add (Game.neg C))) := by
              exact Game.add_comm
            have e1b : ((E.add B).add (Game.neg C)).eq (E.add (B.add (Game.neg C))) := by
              exact Game.eq_of_eq Game.add_assoc
            exact game_eq_trans e1a e1b.symm
          exact e1

        have h6_rhs_eq : ((D.add (Game.neg A)).add E).eq ((E.add D).add (Game.neg A)) := by
          have e1 : ((D.add (Game.neg A)).add E).eq (E.add (D.add (Game.neg A))) := by
            exact Game.add_comm
          have e2 : ((E.add D).add (Game.neg A)).eq (E.add (D.add (Game.neg A))) := by
            exact Game.eq_of_eq Game.add_assoc
          exact game_eq_trans e1 e2.symm

        exact Game.lt_of_le_of_lt h6_lhs_eq.2 (Game.lt_of_lt_of_le h6 h6_rhs_eq.1)

      exact Game.lt_trans ⟨h_mid₁, h_mid₂⟩

    · by_cases h_eq : xL1 ≈ xL2
      · sorry
      · sorry
  · sorry
  · sorry
  · sorry



lemma prove_A_step (α : Nat)
    (ih_A : PropA α)
    (ih_B : PropB α) :
    PropA (α + 1) := by
  sorry


lemma prove_B_base_from_current_A (x y xL yL : Game)
    (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyL : yL ∈ y.left)
    {α : Nat} (hrank : prod_rank x y < α + 1)
    (hA : PropA (α + 1)) :
    ((xL ⊗ y) ⊕ (x ⊗ yL)) ≼ ((xL ⊗ yL) ⊕ (x ⊗ y)) := by

  sorry


lemma prove_B_step (α : Nat)
    (hA : PropA (α + 1))
    (ih_B : PropB α) :
    PropB (α + 1) := by
  sorry


theorem stage_induction (α : Nat) : PropA α ∧ PropB α := by
  induction α with
  | zero =>

      constructor
      · constructor
        · intro x y hx hy h_rank
          cases Nat.not_lt_zero _ h_rank
        · intro x1 x2 y hx1 hx2 hy h_eq h_rank
          cases Nat.not_lt_zero _ h_rank
      · intro x1 x2 y1 y2 h_sur_x1 h_sur_x2 h_sur_y1 h_sur_y2
          h11 h12 h21 h22 hx_le hy_le
        cases Nat.not_lt_zero _ h11

  | succ α ih =>
      have hA_prev : PropA α := ih.1
      have hB_prev : PropB α := ih.2
      have hA_curr : PropA (α + 1) := prove_A_step α hA_prev hB_prev
      have hB_curr : PropB (α + 1) := prove_B_step α hA_curr hB_prev
      exact ⟨hA_curr, hB_curr⟩

end ConwayStrategy
