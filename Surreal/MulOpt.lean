import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm
import Surreal.CommGroup


open Game

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y

abbrev M (a Y X b : Game) : Game := Game.mulOpt4 a Y X b

def CLeft (x1 x2 y yL : Game) : Prop :=
  ((x1 ⊗ y) ⊕ (x2 ⊗ yL)) ≺ ((x1 ⊗ yL) ⊕ (x2 ⊗ y))

def CRight (x1 x2 y yR : Game) : Prop :=
  ((x1 ⊗ yR) ⊕ (x2 ⊗ y)) ≺ ((x1 ⊗ y) ⊕ (x2 ⊗ yR))


/-! ### Some basic facts -/
/-
  “Adjacent C” comes from A: if `xL` is a left option of `x`, then the two C-inequalities
  for `(xL,x,y)` are exactly the facts that the corresponding `mulOpt4` terms are left/right
  options of `x ⊗ y`, hence sit on the correct side of `x ⊗ y`.
-/
lemma adjacentC_left_of_A
    {x xL y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxL : xL ∈ x.left) :
    (∀ yL ∈ y.left, CLeft xL x y yL) ∧
    (∀ yR ∈ y.right, CRight xL x y yR) := by
  sorry

lemma adjacentC_right_of_A
    {x xR y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxR : xR ∈ x.right) :
    (∀ yL ∈ y.left, CLeft x xR y yL) ∧
    (∀ yR ∈ y.right, CRight x xR y yR) := by
  sorry

lemma C_compose_left
    {x1 xm x2 y yL : Game}
    (h1 : CLeft x1 xm y yL)
    (h2 : CLeft xm x2 y yL) :
    CLeft x1 x2 y yL := by
  sorry

lemma C_compose_right
    {x1 xm x2 y yR : Game}
    (h1 : CRight x1 xm y yR)
    (h2 : CRight xm x2 y yR) :
    CRight x1 x2 y yR := by
  sorry

lemma C_replace_eq_left
    {x1 xm x2 y yL : Game}
    (hEqL : (xm ⊗ yL) ∼ (x2 ⊗ yL))
    (hEq  : (xm ⊗ y)  ∼ (x2 ⊗ y))
    (hAdj : CLeft x1 xm y yL) :
    CLeft x1 x2 y yL := by
  sorry

lemma C_replace_eq_right
    {x1 xm x2 y yR : Game}
    (hEqR : (xm ⊗ yR) ∼ (x2 ⊗ yR))
    (hEq  : (xm ⊗ y)  ∼ (x2 ⊗ y))
    (hAdj : CRight x1 xm y yR) :
    CRight x1 x2 y yR := by
  sorry


lemma C_replace_eq_left_first
    {x1 xm x2 y yL : Game}
    (hEqL : (x1 ⊗ yL) ∼ (xm ⊗ yL))
    (hEq  : (x1 ⊗ y)  ∼ (xm ⊗ y))
    (hAdj : CLeft xm x2 y yL) :
    CLeft x1 x2 y yL := by
  sorry

lemma C_replace_eq_right_first
    {x1 xm x2 y yR : Game}
    (hEqR : (x1 ⊗ yR) ∼ (xm ⊗ yR))
    (hEq  : (x1 ⊗ y)  ∼ (xm ⊗ y))
    (hAdj : CRight xm x2 y yR) :
    CRight x1 x2 y yR := by
  sorry



/-! ### Inequalities involving the MulOpt -/

lemma mulOpt4_congr_xslot
    {x1 x2 y x z : Game}
    (hy : (x1 ⊗ y) ∼ (x2 ⊗ y))
    (hz : (x1 ⊗ z) ∼ (x2 ⊗ z)) :
    M x1 y x z ∼ M x2 y x z := by
  sorry

/-- Congruence in the option-slot of `mulOpt4`. -/
lemma mulOpt4_congr_yslot
    {x y x' z1 z2 : Game}
    (hx  : (x  ⊗ z1) ∼ (x  ⊗ z2))
    (hx' : (x' ⊗ z1) ∼ (x' ⊗ z2)) :
    M x y x' z1 ∼ M x y x' z2 := by
  sorry

/-- Move from a left `y`-option to a right `y`-option. -/
lemma mulOpt4_move_y_left_to_right
    {xL y x yL yR : Game}
    (h : CLeft yL yR x xL) :
    M xL y x yL ≺ M xL y x yR := by
  sorry

/-- Move from a left `x`-option to a larger `x`-option, keeping a left `y`-option fixed. -/
lemma mulOpt4_move_x_left_to_right
    {xL xR y x yL : Game}
    (h : CLeft xL xR y yL) :
    M xL y x yL ≺ M xR y x yL := by
  sorry

/-- Move from a right `x`-option to a smaller `x`-option, keeping a right `y`-option fixed. -/
lemma mulOpt4_move_x_right_to_left
    {xL xR y x yR : Game}
    (h : CRight xL xR y yR) :
    M xR y x yR ≺ M xL y x yR := by
  sorry

/-- Move from a right `y`-option to a left `y`-option. -/
lemma mulOpt4_move_y_right_to_left
    {xR y x yL yR : Game}
    (h : CRight yL yR x xR) :
    M xR y x yR ≺ M xR y x yL := by
  sorry

/-! #### Algebraic branch-closing lemmas -/

lemma mulOpt4_LL_lt_product
    {a aL b y yL : Game}
    (hB : (a ⊗ yL) ∼ (b ⊗ yL))
    (hC : CLeft aL b y yL) :
    M aL y a yL ≺ (b ⊗ y) := by
  sorry

lemma mulOpt4_RR_lt_product
    {a aR b y yR : Game}
    (hB : (a ⊗ yR) ∼ (b ⊗ yR))
    (hC : CRight b aR y yR) :
    M aR y a yR ≺ (b ⊗ y) := by
  sorry

lemma product_lt_mulOpt4_LR
    {a b bL y yR : Game}
    (hB : (b ⊗ yR) ∼ (a ⊗ yR))
    (hC : CRight bL a y yR) :
    (a ⊗ y) ≺ M bL y b yR := by
  sorry

lemma product_lt_mulOpt4_RL
    {a b bR y yL : Game}
    (hB : (b ⊗ yL) ∼ (a ⊗ yL))
    (hC : CLeft a bR y yL) :
    (a ⊗ y) ≺ M bR y b yL := by
  sorry
