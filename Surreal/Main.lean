import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Surreal.Game
import Surreal.Surreal
import Surreal.Addition
import Surreal.Mult_comm
import Surreal.Mult_asso
import Surreal.CommGroup
import Surreal.Mult_dist
import Surreal.NewProof

namespace Surreal

/-! ## Multiplication descends to surreal-number equivalence classes -/

local notation:70 x " ⊗ " y => Game.mul x y

/-- Product of two surreal games is surreal. -/
theorem mul_isSurreal (a b : Surreal) :
    IsSurreal (a.val ⊗ b.val) := by
  exact Conway.conway_A a.property b.property

/-- Multiplication of surreal representatives. -/
def mul (a b : Surreal) : Surreal :=
  ⟨a.val ⊗ b.val, mul_isSurreal a b⟩

/-- Multiplication respects surreal equivalence, so it descends to the quotient. -/
theorem mul_congr
    (a₁ a₂ : Surreal) (h₁ : a₁ ≈ a₂)
    (b₁ b₂ : Surreal) (h₂ : b₁ ≈ b₂) :
    Surreal.mul a₁ b₁ ≈ Surreal.mul a₂ b₂ := by
  change Game.eq (a₁.val ⊗ b₁.val) (a₂.val ⊗ b₂.val)
  change Game.eq a₁.val a₂.val at h₁
  change Game.eq b₁.val b₂.val at h₂
  exact Game.mul_congr
    a₁.property a₂.property
    b₁.property b₂.property
    h₁ h₂

/-- Multiplication on surreal numbers as equivalence classes. -/
def SurrealNumber.mul : SurrealNumber → SurrealNumber → SurrealNumber :=
  Quotient.map₂ Surreal.mul Surreal.mul_congr

instance : Mul SurrealNumber where
  mul := SurrealNumber.mul


/-! ## Ring multiplication theorems -/

theorem SurrealNumber.mul_comm (a b : SurrealNumber) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  apply Quotient.sound
  change Game.eq (a.val.mul b.val) (b.val.mul a.val)
  exact Game.mul_comm

theorem SurrealNumber.mul_assoc (a b c : SurrealNumber) : a * b * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c
  apply Quotient.sound
  change Game.eq ((a.val.mul b.val).mul c.val) (a.val.mul (b.val.mul c.val))
  exact Game.mul_assoc_of_isSurreal a.property b.property c.property

theorem SurrealNumber.one_mul (a : SurrealNumber) : 1 * a = a := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  change Game.eq (Game.one.mul a.val) a.val
  exact Game.one_mul

theorem SurrealNumber.mul_one (a : SurrealNumber) : a * 1 = a := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  change Game.eq (a.val.mul Game.one) a.val
  exact Game.mul_one

theorem SurrealNumber.zero_mul (a : SurrealNumber) : 0 * a = 0 := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  change Game.eq (Game.zero.mul a.val) Game.zero
  exact Game.zero_mul a.val

theorem SurrealNumber.mul_zero (a : SurrealNumber) : a * 0 = 0 := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  change Game.eq (a.val.mul Game.zero) Game.zero
  exact Game.mul_zero a.val


/-! ## Distributivity -/

theorem SurrealNumber.left_distrib (a b c : SurrealNumber) :
    a * (b + c) = a * b + a * c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c
  apply Quotient.sound
  change
    Game.eq
      (a.val.mul (b.val.add c.val))
      ((a.val.mul b.val).add (a.val.mul c.val))
  exact Game.mul_distrib

theorem SurrealNumber.right_distrib (a b c : SurrealNumber) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := SurrealNumber.mul_comm _ _
    _ = c * a + c * b := SurrealNumber.left_distrib _ _ _
    _ = a * c + c * b := by rw [SurrealNumber.mul_comm c a]
    _ = a * c + b * c := by rw [SurrealNumber.mul_comm c b]


/-! ## Commutative ring structure -/

noncomputable instance : CommRing SurrealNumber where
  add_assoc := by
    intro a b c
    exact add_assoc a b c
  add_comm := by
    intro a b
    exact add_comm a b
  zero_add := by
    intro a
    exact zero_add a
  add_zero := by
    intro a
    exact add_zero a
  neg_add_cancel := by
    intro a
    exact neg_add_cancel a
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


/-! ## Ordered-ring compatibility -/

theorem SurrealNumber.zero_le_one :
    (0 : SurrealNumber) ≤ 1 := by
  change Game.le Game.zero Game.one
  unfold Game.le
  simp [Game.zero, Game.one, Game.left, Game.right]

private lemma exists_left_nonneg_of_pos
    {y : Game} (hy : Game.lt Game.zero y) :
    ∃ yL ∈ y.left, Game.le Game.zero yL := by
  classical
  by_contra h
  have hy_le_zero : Game.le y Game.zero := by
    rw [Game.le]
    constructor
    · intro yL hyL h0le_yL
      exact h ⟨yL, hyL, h0le_yL⟩
    · intro r hr _
      simp [Game.zero, Game.right] at hr
  exact hy.2 hy_le_zero


theorem Game.mul_pos_of_isSurreal {x y : Game}
    (sx : IsSurreal x) (sy : IsSurreal y)
    (hx : Game.lt Game.zero x) (hy : Game.lt Game.zero y) :
    Game.lt Game.zero (x ⊗ y) := by
  classical
  refine
    (Game.wf_R.induction
      (C := fun y => IsSurreal y → Game.lt Game.zero y → Game.lt Game.zero (x ⊗ y))
      y ?_) sy hy
  intro y IH sy hy
  obtain ⟨yL, hyL, h0le_yL⟩ := exists_left_nonneg_of_pos hy
  have syL : IsSurreal yL := IsSurreal.isSurreal_left sy hyL
  have h0le_xyL : Game.le Game.zero (x ⊗ yL) := by
    by_cases hyL_le_zero : Game.le yL Game.zero
    · have hyL_eq_zero : Game.eq yL Game.zero := by
        exact ⟨hyL_le_zero, h0le_yL⟩
      have hxyL_eq_zero : Game.eq (x ⊗ yL) Game.zero := by
        have hcomm₁ : Game.eq (x ⊗ yL) (yL ⊗ x) := by
          exact Game.mul_comm (a := x) (b := yL)
        have hcong : Game.eq (yL ⊗ x) (Game.zero ⊗ x) := by
          exact Conway.conway_B
            syL IsSurreal.isSurreal_zero sx hyL_eq_zero
        have hzero : Game.eq (Game.zero ⊗ x) Game.zero := by
          exact Game.zero_mul x
        exact Game.eq_trans ⟨hcomm₁, Game.eq_trans ⟨hcong, hzero⟩⟩
      exact hxyL_eq_zero.2
    · have hyL_pos : Game.lt Game.zero yL := by
        exact ⟨h0le_yL, hyL_le_zero⟩
      exact (IH yL (Game.birthday_lt_left hyL) syL hyL_pos).1
  have hC :=
    Conway.conway_C (x1 := Game.zero) (x2 := x) (y := y) IsSurreal.isSurreal_zero sx sy hx
  have hCL := hC.1 yL hyL
  have hxyL_lt_xy : Game.lt (x ⊗ yL) (x ⊗ y) := by
    have hCL' : Game.lt (Game.add Game.zero (x ⊗ yL)) (Game.add Game.zero (x ⊗ y)) := by
      simpa [CLeft, Game.mulOpt4, Game.zero_mul_eq, Game.add_zero, Game.neg_zero]
        using hCL
    have hL : Game.eq (x ⊗ yL) (Game.add Game.zero (x ⊗ yL)) := by
      exact Game.eq_symm (Game.zero_add (a := x ⊗ yL))
    have hR : Game.eq (x ⊗ y) (Game.add Game.zero (x ⊗ y)) := by
      exact Game.eq_symm (Game.zero_add (a := x ⊗ y))
    constructor
    · exact Game.le_trans
        ⟨hL.1, Game.le_trans ⟨hCL'.1, hR.2⟩⟩
    · intro hcontra
      exact hCL'.2
        (Game.le_trans
          ⟨hR.2, Game.le_trans ⟨hcontra, hL.1⟩⟩)
  constructor
  · exact Game.le_trans ⟨h0le_xyL, hxyL_lt_xy.1⟩
  · intro hxy_le_zero
    exact hxyL_lt_xy.2 (Game.le_trans ⟨hxy_le_zero, h0le_xyL⟩)


theorem SurrealNumber.mul_pos
    {a b : SurrealNumber} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  revert ha hb
  refine Quotient.inductionOn₂ a b ?_
  intro a b ha hb
  change Game.lt Game.zero a.val at ha
  change Game.lt Game.zero b.val at hb
  change Game.lt Game.zero (a.val.mul b.val)
  exact Game.mul_pos_of_isSurreal a.property b.property ha hb

theorem SurrealNumber.mul_nonneg
    {a b : SurrealNumber} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rcases _root_.lt_or_eq_of_le ha with ha_lt | ha_eq
  · rcases _root_.lt_or_eq_of_le hb with hb_lt | hb_eq
    · exact (SurrealNumber.mul_pos ha_lt hb_lt).le
    · simp [← hb_eq]
  · simp [← ha_eq]

/-- Optional but useful: `0 ≤ 1`. -/
noncomputable instance SurrealNumber.instZeroLEOneClass :
    ZeroLEOneClass SurrealNumber where
  zero_le_one := SurrealNumber.zero_le_one


/-! ### Multiplication monotonicity from `mul_nonneg` and `mul_pos` -/

theorem SurrealNumber.mul_le_mul_of_nonneg_left'
    {a b c : SurrealNumber} (ha : 0 ≤ a) (hbc : b ≤ c) : a * b ≤ a * c := by
  have hdiff : 0 ≤ c - b := by
    exact _root_.sub_nonneg.mpr hbc
  have hprod : 0 ≤ a * (c - b) := by
    exact SurrealNumber.mul_nonneg ha hdiff
  have hprod' : 0 ≤ a * c - a * b := by
    simpa [mul_sub] using hprod
  exact _root_.sub_nonneg.mp hprod'

theorem SurrealNumber.mul_le_mul_of_nonneg_right'
    {a b c : SurrealNumber} (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hdiff : 0 ≤ b - a := by
    exact _root_.sub_nonneg.mpr hab
  have hprod : 0 ≤ (b - a) * c := by
    exact SurrealNumber.mul_nonneg hdiff hc
  have hprod' : 0 ≤ b * c - a * c := by
    simpa [sub_mul] using hprod
  exact _root_.sub_nonneg.mp hprod'

theorem SurrealNumber.mul_lt_mul_of_pos_left'
    {a b c : SurrealNumber} (ha : 0 < a) (hbc : b < c) : a * b < a * c := by
  have hdiff : 0 < c - b := by
    exact _root_.sub_pos.mpr hbc
  have hprod : 0 < a * (c - b) := by
    exact SurrealNumber.mul_pos ha hdiff
  have hprod' : 0 < a * c - a * b := by
    simpa [mul_sub] using hprod
  exact _root_.sub_pos.mp hprod'

theorem SurrealNumber.mul_lt_mul_of_pos_right'
    {a b c : SurrealNumber} (hc : 0 < c) (hab : a < b) : a * c < b * c := by
  have hdiff : 0 < b - a := by
    exact _root_.sub_pos.mpr hab
  have hprod : 0 < (b - a) * c := by
    exact SurrealNumber.mul_pos hdiff hc
  have hprod' : 0 < b * c - a * c := by
    simpa [sub_mul] using hprod
  exact _root_.sub_pos.mp hprod'


/-! ### The actual Mathlib order-multiplication mixins -/

noncomputable instance SurrealNumber.instPosMulMono :
    PosMulMono SurrealNumber where
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    have hdiff : 0 ≤ c - b := by
      exact _root_.sub_nonneg.mpr hbc
    have hprod : 0 ≤ a * (c - b) := by
      exact SurrealNumber.mul_nonneg ha hdiff
    have hprod' : 0 ≤ a * c - a * b := by
      simpa [mul_sub] using hprod
    exact _root_.sub_nonneg.mp hprod'

noncomputable instance SurrealNumber.instMulPosMono :
    MulPosMono SurrealNumber where
  mul_le_mul_of_nonneg_right := by
    intro c hc a b hab
    have hdiff : 0 ≤ b - a := by
      exact _root_.sub_nonneg.mpr hab
    have hprod : 0 ≤ (b - a) * c := by
      exact SurrealNumber.mul_nonneg hdiff hc
    have hprod' : 0 ≤ b * c - a * c := by
      simpa [sub_mul] using hprod
    exact _root_.sub_nonneg.mp hprod'

noncomputable instance SurrealNumber.instPosMulStrictMono :
    PosMulStrictMono SurrealNumber where
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    have hdiff : 0 < c - b := by
      exact _root_.sub_pos.mpr hbc
    have hprod : 0 < a * (c - b) := by
      exact SurrealNumber.mul_pos ha hdiff
    have hprod' : 0 < a * c - a * b := by
      simpa [mul_sub] using hprod
    exact _root_.sub_pos.mp hprod'

noncomputable instance SurrealNumber.instMulPosStrictMono :
    MulPosStrictMono SurrealNumber where
  mul_lt_mul_of_pos_right := by
    intro c hc a b hab
    have hdiff : 0 < b - a := by
      exact _root_.sub_pos.mpr hab
    have hprod : 0 < (b - a) * c := by
      exact SurrealNumber.mul_pos hdiff hc
    have hprod' : 0 < b * c - a * c := by
      simpa [sub_mul] using hprod
    exact _root_.sub_pos.mp hprod'

noncomputable instance : IsOrderedRing SurrealNumber where
  __ := inferInstanceAs (IsOrderedAddMonoid SurrealNumber)
  __ := inferInstanceAs (PosMulMono SurrealNumber)
  __ := inferInstanceAs (MulPosMono SurrealNumber)

private lemma SurrealNumber.not_one_le_zero : ¬ ((1 : SurrealNumber) ≤ 0) := by
  intro h
  change Game.le Game.one Game.zero at h
  rw [Game.le] at h
  have hz_left : Game.zero ∈ Game.one.left := by
    simp [Game.one, Game.left]
  exact h.1 Game.zero hz_left Game.le_congr

noncomputable instance : IsStrictOrderedRing SurrealNumber where
  __ := inferInstanceAs (IsOrderedRing SurrealNumber)
  __ := inferInstanceAs (PosMulStrictMono SurrealNumber)
  __ := inferInstanceAs (MulPosStrictMono SurrealNumber)
  le_of_add_le_add_left := by
    intro a b c h
    have h' : (-a) + (a + b) ≤ (-a) + (a + c) := by
      exact add_le_add_left h (-a)
    simpa [add_assoc] using h'
  exists_pair_ne := by
    refine ⟨(0 : SurrealNumber), (1 : SurrealNumber), ?_⟩
    intro h01
    have hle10 : (1 : SurrealNumber) ≤ 0 := by
      rw [← h01]
    exact SurrealNumber.not_one_le_zero hle10

/-! ## Examples -/

example (a b c : SurrealNumber) :
    a * (b + c) = a * b + a * c := by
  exact mul_add a b c

example (a b c : SurrealNumber) :
    (a + b) * c = a * c + b * c := by
  exact add_mul a b c

example (a : SurrealNumber) :
    a * 1 = a := by
  exact mul_one a

example (a b : SurrealNumber) :
    a * b = b * a := by
  exact mul_comm a b

example (a b : SurrealNumber) (ha : 0 < a) (hb : 0 < b) :
    0 < a * b := by
  exact mul_pos ha hb

end Surreal
