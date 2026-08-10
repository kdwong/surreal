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

def MulCrossLe (x1 x2 y1 y2 : Game) : Prop :=
  ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≼ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2))

def MulCrossLt (x1 x2 y1 y2 : Game) : Prop :=
  ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≺ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2))

/-! The two Conway C conditions are the corresponding strict cross relations. -/

abbrev CLeft (x1 x2 y yL : Game) : Prop :=
  ((x1 ⊗ y) ⊕ (x2 ⊗ yL)) ≺ ((x1 ⊗ yL) ⊕ (x2 ⊗ y))

abbrev CRight (x1 x2 y yR : Game) : Prop :=
  ((x1 ⊗ yR) ⊕ (x2 ⊗ y)) ≺ ((x1 ⊗ y) ⊕ (x2 ⊗ yR))


/-! ### Public bookkeeping lemmas -/

@[simp] theorem game_q_le {a b : Game} : (⟦a⟧ : GameQ) ≤ ⟦b⟧ ↔ a ≼ b := by
  rfl

@[simp] theorem game_q_lt {a b : Game} : (⟦a⟧ : GameQ) < ⟦b⟧ ↔ a ≺ b := by
  rfl

@[simp] theorem game_q_equiv {a b : Game} : (⟦a⟧ : GameQ) = ⟦b⟧ ↔ a ∼ b := by
  constructor
  · intro h
    constructor
    · exact game_q_le.mp (le_of_eq h)
    · exact game_q_le.mp (le_of_eq h.symm)
  · intro h
    exact le_antisymm (game_q_le.mpr h.1) (game_q_le.mpr h.2)

private theorem game_q_mul_comm (a b : Game) :
    (⟦a ⊗ b⟧ : GameQ) = ⟦b ⊗ a⟧ := by
  exact game_q_equiv.mpr Game.mul_comm

/-- Transpose a strict cross-product inequality using commutativity of multiplication. -/
lemma MulCrossLt.swap {x1 x2 y1 y2 : Game} (h : MulCrossLt x1 x2 y1 y2) :
    MulCrossLt y1 y2 x1 x2 := by
  unfold MulCrossLt at *
  apply game_q_lt.mp
  have hq := game_q_lt.mpr h
  simp only [q_add] at hq ⊢
  calc
    (⟦y1 ⊗ x2⟧ : GameQ) + ⟦y2 ⊗ x1⟧ = ⟦x2 ⊗ y1⟧ + ⟦x1 ⊗ y2⟧ := by
      rw [game_q_mul_comm y1 x2, game_q_mul_comm y2 x1]
    _ = ⟦x1 ⊗ y2⟧ + ⟦x2 ⊗ y1⟧ := by
      exact _root_.add_comm _ _
    _ < ⟦x1 ⊗ y1⟧ + ⟦x2 ⊗ y2⟧ := hq
    _ = ⟦y1 ⊗ x1⟧ + ⟦y2 ⊗ x2⟧ := by
      rw [game_q_mul_comm x1 y1, game_q_mul_comm x2 y2]

/-- Compose strict cross-product inequalities through an intermediate first coordinate. -/
lemma MulCrossLt.trans {x1 xm x2 y1 y2 : Game}
    (h1 : MulCrossLt x1 xm y1 y2)
    (h2 : MulCrossLt xm x2 y1 y2) :
    MulCrossLt x1 x2 y1 y2 := by
  unfold MulCrossLt at *
  apply game_q_lt.mp
  have hq1 := game_q_lt.mpr h1
  have hq2 := game_q_lt.mpr h2
  simp only [q_add] at hq1 hq2 ⊢
  have hs := _root_.add_lt_add hq1 hq2
  have hs' :=
    _root_.add_lt_add_right hs (-(⟦xm ⊗ y1⟧ + ⟦xm ⊗ y2⟧))
  convert hs' using 1 <;> abel

/-- Replace the right first-coordinate endpoint by equivalent products. -/
lemma MulCrossLt.congr_right {x1 xm x2 y1 y2 : Game}
    (hEq1 : (xm ⊗ y1) ∼ (x2 ⊗ y1))
    (hEq2 : (xm ⊗ y2) ∼ (x2 ⊗ y2))
    (h : MulCrossLt x1 xm y1 y2) :
    MulCrossLt x1 x2 y1 y2 := by
  unfold MulCrossLt at *
  apply game_q_lt.mp
  have hq := game_q_lt.mpr h
  have hEq1q := game_q_equiv.mpr hEq1
  have hEq2q := game_q_equiv.mpr hEq2
  simpa only [q_add, hEq1q, hEq2q] using hq

/-- Replace the left first-coordinate endpoint by equivalent products. -/
lemma MulCrossLt.congr_left {x1 xm x2 y1 y2 : Game}
    (hEq1 : (x1 ⊗ y1) ∼ (xm ⊗ y1))
    (hEq2 : (x1 ⊗ y2) ∼ (xm ⊗ y2))
    (h : MulCrossLt xm x2 y1 y2) :
    MulCrossLt x1 x2 y1 y2 := by
  unfold MulCrossLt at *
  apply game_q_lt.mp
  have hq := game_q_lt.mpr h
  have hEq1q := game_q_equiv.mpr hEq1
  have hEq2q := game_q_equiv.mpr hEq2
  simpa only [q_add, hEq1q, hEq2q] using hq

private lemma mulCrossLe_q {a c d e : Game}
    (h : MulCrossLe a c d e) :
    (⟦a ⊗ e⟧ : GameQ) + ⟦c ⊗ d⟧ ≤ ⟦a ⊗ d⟧ + ⟦c ⊗ e⟧ := by
  simpa only [q_add] using (game_q_le.mpr h)

private lemma mulCrossLt_q {a c d e : Game}
    (h : MulCrossLt a c d e) :
    (⟦a ⊗ e⟧ : GameQ) + ⟦c ⊗ d⟧ < ⟦a ⊗ d⟧ + ⟦c ⊗ e⟧ := by
  simpa only [q_add] using (game_q_lt.mpr h)

private lemma mulOpt4_xslot_mono_q
    {r : GameQ → GameQ → Prop}
    {a b c d e : Game}
    (hq : r (⟦a ⊗ e⟧ + ⟦c ⊗ d⟧) (⟦a ⊗ d⟧ + ⟦c ⊗ e⟧))
    (add_right : ∀ {x y}, r x y → ∀ z, r (x + z) (y + z)) :
    r ⟦M a e b d⟧ ⟦M c e b d⟧ := by
  simp only [M, Game.mulOpt4, q_add, q_neg]
  convert
    add_right hq ((-⟦a ⊗ d⟧ + ⟦b ⊗ d⟧) + -⟦c ⊗ d⟧)
    using 1 <;> abel

private lemma mulOpt4_xslot_antitone_q
    {r : GameQ → GameQ → Prop}
    {a b c d e : Game}
    (hq : r (⟦a ⊗ e⟧ + ⟦c ⊗ d⟧) (⟦a ⊗ d⟧ + ⟦c ⊗ e⟧))
    (add_right : ∀ {x y}, r x y → ∀ z, r (x + z) (y + z)) :
    r ⟦M c d b e⟧ ⟦M a d b e⟧ := by
  simp only [M, Game.mulOpt4, q_add, q_neg]
  convert
    add_right hq ((⟦b ⊗ e⟧ + -⟦c ⊗ e⟧) + -⟦a ⊗ e⟧)
    using 1 <;> abel

private lemma mulOpt4_yslot_mono_q
    {r : GameQ → GameQ → Prop}
    {a b c d e : Game}
    (hq : r (⟦a ⊗ e⟧ + ⟦c ⊗ d⟧) (⟦a ⊗ d⟧ + ⟦c ⊗ e⟧))
    (add_right : ∀ {x y}, r x y → ∀ z, r (x + z) (y + z)) :
    r ⟦M a b c d⟧ ⟦M a b c e⟧ := by
  simp only [M, Game.mulOpt4, q_add, q_neg]
  convert
    add_right hq ((⟦a ⊗ b⟧ + -⟦a ⊗ d⟧) + -⟦a ⊗ e⟧)
    using 1 <;> abel

private lemma mulOpt4_yslot_antitone_q
    {r : GameQ → GameQ → Prop}
    {a b c d e : Game}
    (hq : r (⟦a ⊗ e⟧ + ⟦c ⊗ d⟧) (⟦a ⊗ d⟧ + ⟦c ⊗ e⟧))
    (add_right : ∀ {x y}, r x y → ∀ z, r (x + z) (y + z)) :
    r ⟦M c b a e⟧ ⟦M c b a d⟧ := by
  simp only [M, Game.mulOpt4, q_add, q_neg]
  convert
    add_right hq ((⟦c ⊗ b⟧ + -⟦c ⊗ e⟧) + -⟦c ⊗ d⟧)
    using 1 <;> abel

lemma mulOpt4_xslot_mono_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M a e b d ≼ M c e b d := by
  exact game_q_le.mp <|
    mulOpt4_xslot_mono_q (mulCrossLe_q h) _root_.add_le_add_right

lemma mulOpt4_xslot_antitone_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M c d b e ≼ M a d b e := by
  exact game_q_le.mp <|
    mulOpt4_xslot_antitone_q (mulCrossLe_q h) _root_.add_le_add_right

lemma mulOpt4_yslot_mono_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M a b c d ≺ M a b c e := by
  exact game_q_lt.mp <|
    mulOpt4_yslot_mono_q (mulCrossLt_q h) _root_.add_lt_add_right

lemma mulOpt4_xslot_mono_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M a e b d ≺ M c e b d := by
  exact game_q_lt.mp <|
    mulOpt4_xslot_mono_q (mulCrossLt_q h) _root_.add_lt_add_right

lemma mulOpt4_xslot_antitone_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M c d b e ≺ M a d b e := by
  exact game_q_lt.mp <|
    mulOpt4_xslot_antitone_q (mulCrossLt_q h) _root_.add_lt_add_right

lemma mulOpt4_yslot_mono_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M a b c d ≼ M a b c e := by
  exact game_q_le.mp <|
    mulOpt4_yslot_mono_q (mulCrossLe_q h) _root_.add_le_add_right

lemma mulOpt4_yslot_antitone_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M c b a e ≼ M c b a d := by
  exact game_q_le.mp <|
    mulOpt4_yslot_antitone_q (mulCrossLe_q h) _root_.add_le_add_right

lemma mulOpt4_yslot_antitone_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M c b a e ≺ M c b a d := by
  exact game_q_lt.mp <|
    mulOpt4_yslot_antitone_q (mulCrossLt_q h) _root_.add_lt_add_right


/-! ### Some basic facts -/

lemma adjacentC_left_of_A
    {x xL y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxL : xL ∈ x.left) :
    (∀ yL ∈ y.left, CLeft xL x y yL) ∧
    (∀ yR ∈ y.right, CRight xL x y yR) := by
  constructor
  · intro yL hyL
    have hmem : M xL y x yL ∈ (x ⊗ y).left :=
      mem_mul_left_ll hxL hyL
    have hlt : M xL y x yL ≺ x ⊗ y :=
      IsSurreal.left_lt hxy hmem
    unfold CLeft
    apply game_q_lt.mp
    have hq' :=
      _root_.add_lt_add_right (game_q_lt.mpr hlt) ⟦xL ⊗ yL⟧
    convert hq' using 1 <;>
      simp [M, Game.mulOpt4, q_add, q_neg]; abel
  · intro yR hyR
    have hmem : M xL y x yR ∈ (x ⊗ y).right :=
      mem_mul_right_lr hxL hyR
    have hlt : (x ⊗ y) ≺ M xL y x yR :=
      IsSurreal.lt_right hxy hmem
    unfold CRight
    apply game_q_lt.mp
    have hq' :=
      _root_.add_lt_add_right (game_q_lt.mpr hlt) ⟦xL ⊗ yR⟧
    convert hq' using 1 <;>
      simp [M, Game.mulOpt4, q_add, q_neg]; abel

lemma adjacentC_right_of_A
    {x xR y : Game}
    (hxy : IsSurreal (x ⊗ y))
    (hxR : xR ∈ x.right) :
    (∀ yL ∈ y.left, CLeft x xR y yL) ∧
    (∀ yR ∈ y.right, CRight x xR y yR) := by
  constructor
  · intro yL hyL
    have hmem : M xR y x yL ∈ (x ⊗ y).right :=
      mem_mul_right_rl hxR hyL
    have hlt : (x ⊗ y) ≺ M xR y x yL :=
      IsSurreal.lt_right hxy hmem
    unfold CLeft
    apply game_q_lt.mp
    have hq' :=
      _root_.add_lt_add_right (game_q_lt.mpr hlt) ⟦xR ⊗ yL⟧
    convert hq' using 1;
      simp [M, Game.mulOpt4, q_add, q_neg]; abel
  · intro yR hyR
    have hmem : M xR y x yR ∈ (x ⊗ y).left :=
      mem_mul_left_rr hxR hyR
    have hlt : M xR y x yR ≺ x ⊗ y :=
      IsSurreal.left_lt hxy hmem
    unfold CRight
    apply game_q_lt.mp
    have hq' :=
      _root_.add_lt_add_right (game_q_lt.mpr hlt) ⟦xR ⊗ yR⟧
    convert hq' using 1;
      simp [M, Game.mulOpt4, q_add, q_neg]; abel

lemma C_compose_left
    {x1 xm x2 y yL : Game}
    (h1 : CLeft x1 xm y yL)
    (h2 : CLeft xm x2 y yL) :
    CLeft x1 x2 y yL := by
  exact MulCrossLt.trans h1 h2

lemma C_compose_right
    {x1 xm x2 y yR : Game}
    (h1 : CRight x1 xm y yR)
    (h2 : CRight xm x2 y yR) :
    CRight x1 x2 y yR := by
  exact MulCrossLt.trans h1 h2

lemma C_replace_eq_left
    {x1 xm x2 y yL : Game}
    (hEqL : (xm ⊗ yL) ∼ (x2 ⊗ yL))
    (hEq : (xm ⊗ y) ∼ (x2 ⊗ y))
    (hAdj : CLeft x1 xm y yL) :
    CLeft x1 x2 y yL := by
  exact MulCrossLt.congr_right hEqL hEq hAdj

lemma C_replace_eq_right
    {x1 xm x2 y yR : Game}
    (hEqR : (xm ⊗ yR) ∼ (x2 ⊗ yR))
    (hEq : (xm ⊗ y) ∼ (x2 ⊗ y))
    (hAdj : CRight x1 xm y yR) :
    CRight x1 x2 y yR := by
  exact MulCrossLt.congr_right hEq hEqR hAdj

lemma C_replace_eq_left_first
    {x1 xm x2 y yL : Game}
    (hEqL : (x1 ⊗ yL) ∼ (xm ⊗ yL))
    (hEq : (x1 ⊗ y) ∼ (xm ⊗ y))
    (hAdj : CLeft xm x2 y yL) :
    CLeft x1 x2 y yL := by
  exact MulCrossLt.congr_left hEqL hEq hAdj

lemma C_replace_eq_right_first
    {x1 xm x2 y yR : Game}
    (hEqR : (x1 ⊗ yR) ∼ (xm ⊗ yR))
    (hEq : (x1 ⊗ y) ∼ (xm ⊗ y))
    (hAdj : CRight xm x2 y yR) :
    CRight x1 x2 y yR := by
  exact MulCrossLt.congr_left hEq hEqR hAdj


/-! ### Inequalities involving the MulOpt -/

lemma mulOpt4_congr_xslot
    {x1 x2 y x z : Game}
    (hy : (x1 ⊗ y) ∼ (x2 ⊗ y))
    (hz : (x1 ⊗ z) ∼ (x2 ⊗ z)) :
    M x1 y x z ∼ M x2 y x z := by
  apply game_q_equiv.mp
  have hyq : (⟦x1 ⊗ y⟧ : GameQ) = ⟦x2 ⊗ y⟧ := game_q_equiv.mpr hy
  have hzq : (⟦x1 ⊗ z⟧ : GameQ) = ⟦x2 ⊗ z⟧ := game_q_equiv.mpr hz
  simp [M, Game.mulOpt4, q_add, q_neg, hyq, hzq]

/-- Congruence in the option-slot of `mulOpt4`. -/
lemma mulOpt4_congr_yslot
    {x y x' z1 z2 : Game}
    (hx : (x ⊗ z1) ∼ (x ⊗ z2))
    (hx' : (x' ⊗ z1) ∼ (x' ⊗ z2)) :
    M x y x' z1 ∼ M x y x' z2 := by
  apply game_q_equiv.mp
  have hxq : (⟦x ⊗ z1⟧ : GameQ) = ⟦x ⊗ z2⟧ := game_q_equiv.mpr hx
  have hx'q : (⟦x' ⊗ z1⟧ : GameQ) = ⟦x' ⊗ z2⟧ := game_q_equiv.mpr hx'
  simp [M, Game.mulOpt4, q_add, q_neg, hxq, hx'q]

/-- Move from a left `y`-option to a right `y`-option. -/
lemma MulCrossLt_of_CLeft_y
    {xL x yL yR : Game}
    (h : CLeft yL yR x xL) :
    MulCrossLt xL x yL yR := by
  exact MulCrossLt.swap h

/-- Move from a left `y`-option to a right `y`-option. -/
lemma mulOpt4_move_y_left_to_right
    {xL y x yL yR : Game}
    (h : CLeft yL yR x xL) :
    M xL y x yL ≺ M xL y x yR := by
  exact mulOpt4_yslot_mono_lt_of_cross
    (MulCrossLt_of_CLeft_y h)

/-- Move from a left `x`-option to a larger `x`-option, keeping a left `y`-option fixed. -/
lemma mulOpt4_move_x_left_to_right
    {xL xR y x yL : Game}
    (h : CLeft xL xR y yL) :
    M xL y x yL ≺ M xR y x yL := by
  exact mulOpt4_xslot_mono_lt_of_cross h

/-- Move from a right `x`-option to a smaller `x`-option, keeping a right `y`-option fixed. -/
lemma mulOpt4_move_x_right_to_left
    {xL xR y x yR : Game}
    (h : CRight xL xR y yR) :
    M xR y x yR ≺ M xL y x yR := by
  exact mulOpt4_xslot_antitone_lt_of_cross h

/-- Move from a right `y`-option to a left `y`-option. -/
lemma MulCrossLt_of_CRight_y
    {xR x yL yR : Game}
    (h : CRight yL yR x xR) :
    MulCrossLt x xR yL yR := by
  exact MulCrossLt.swap h

lemma mulOpt4_move_y_right_to_left
    {xR y x yL yR : Game}
    (h : CRight yL yR x xR) :
    M xR y x yR ≺ M xR y x yL := by
  exact mulOpt4_yslot_antitone_lt_of_cross
    (MulCrossLt_of_CRight_y h)

/-! #### Algebraic branch-closing lemmas -/

private lemma add_add_neg_lt_right
    {p q r s : GameQ} (h : p + q < r + s) :
    (p + q) + (-r) < s := by
  have h' := _root_.add_lt_add_right h (-r)
  convert h' using 1
  all_goals abel

private lemma left_lt_add_add_neg
    {p q r s : GameQ} (h : p + q < r + s) :
    p < (r + s) + (-q) := by
  have h' := _root_.add_lt_add_right h (-q)
  convert h' using 1
  all_goals abel

lemma mulOpt4_LL_lt_product
    {a aL b y yL : Game}
    (hB : (a ⊗ yL) ∼ (b ⊗ yL))
    (hC : CLeft aL b y yL) :
    M aL y a yL ≺ (b ⊗ y) := by
  unfold CLeft at hC
  apply game_q_lt.mp
  have hq := game_q_lt.mpr hC
  have hBq : (⟦a ⊗ yL⟧ : GameQ) = ⟦b ⊗ yL⟧ := game_q_equiv.mpr hB
  simp only [q_add] at hq
  have hq' := add_add_neg_lt_right hq
  convert hq' using 1
  all_goals simp [M, Game.mulOpt4, q_add, q_neg, hBq]

lemma mulOpt4_RR_lt_product
    {a aR b y yR : Game}
    (hB : (a ⊗ yR) ∼ (b ⊗ yR))
    (hC : CRight b aR y yR) :
    M aR y a yR ≺ (b ⊗ y) := by
  unfold CRight at hC
  apply game_q_lt.mp
  have hq := game_q_lt.mpr hC
  have hBq : (⟦a ⊗ yR⟧ : GameQ) = ⟦b ⊗ yR⟧ := game_q_equiv.mpr hB
  simp only [q_add] at hq
  have hq0 :
      (⟦aR ⊗ y⟧ : GameQ) + ⟦b ⊗ yR⟧ < ⟦aR ⊗ yR⟧ + ⟦b ⊗ y⟧ := by
    calc
      (⟦aR ⊗ y⟧ : GameQ) + ⟦b ⊗ yR⟧ = ⟦b ⊗ yR⟧ + ⟦aR ⊗ y⟧ :=
        _root_.add_comm _ _
      _ < ⟦b ⊗ y⟧ + ⟦aR ⊗ yR⟧ := hq
      _ = ⟦aR ⊗ yR⟧ + ⟦b ⊗ y⟧ := _root_.add_comm _ _
  have hq' := add_add_neg_lt_right hq0
  convert hq' using 1
  all_goals simp [M, Game.mulOpt4, q_add, q_neg, hBq]

lemma product_lt_mulOpt4_LR
    {a b bL y yR : Game}
    (hB : (b ⊗ yR) ∼ (a ⊗ yR))
    (hC : CRight bL a y yR) :
    (a ⊗ y) ≺ M bL y b yR := by
  unfold CRight at hC
  apply game_q_lt.mp
  have hq := game_q_lt.mpr hC
  have hBq : (⟦b ⊗ yR⟧ : GameQ) = ⟦a ⊗ yR⟧ := game_q_equiv.mpr hB
  simp only [q_add] at hq
  have hq0 :
      (⟦a ⊗ y⟧ : GameQ) + ⟦bL ⊗ yR⟧ < ⟦bL ⊗ y⟧ + ⟦a ⊗ yR⟧ := by
    calc
      (⟦a ⊗ y⟧ : GameQ) + ⟦bL ⊗ yR⟧ = ⟦bL ⊗ yR⟧ + ⟦a ⊗ y⟧ :=
        _root_.add_comm _ _
      _ < ⟦bL ⊗ y⟧ + ⟦a ⊗ yR⟧ := hq
  have hq' := left_lt_add_add_neg hq0
  convert hq' using 1
  all_goals simp [M, Game.mulOpt4, q_add, q_neg, hBq]

lemma product_lt_mulOpt4_RL
    {a b bR y yL : Game}
    (hB : (b ⊗ yL) ∼ (a ⊗ yL))
    (hC : CLeft a bR y yL) :
    (a ⊗ y) ≺ M bR y b yL := by
  unfold CLeft at hC
  apply game_q_lt.mp
  have hq := game_q_lt.mpr hC
  have hBq : (⟦b ⊗ yL⟧ : GameQ) = ⟦a ⊗ yL⟧ := game_q_equiv.mpr hB
  simp only [q_add] at hq
  have hq0 :
      (⟦a ⊗ y⟧ : GameQ) + ⟦bR ⊗ yL⟧ < ⟦bR ⊗ y⟧ + ⟦a ⊗ yL⟧ := by
    calc
      (⟦a ⊗ y⟧ : GameQ) + ⟦bR ⊗ yL⟧ < ⟦a ⊗ yL⟧ + ⟦bR ⊗ y⟧ := hq
      _ = ⟦bR ⊗ y⟧ + ⟦a ⊗ yL⟧ := _root_.add_comm _ _
  have hq' := left_lt_add_add_neg hq0
  convert hq' using 1
  all_goals simp [M, Game.mulOpt4, q_add, q_neg, hBq]
