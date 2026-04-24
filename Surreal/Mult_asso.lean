import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm
import Surreal.CommGroup
import Surreal.mult_dist

namespace Game

open scoped Game

local notation:70 x " ⊕ " y => Game.add x y
local notation:70 x " ⊗ " y => Game.mul x y


/-!
This file is follows the proof strategy in `strategy.md`:
* `StageA n`: product of surreal games is surreal, and left congruence,
  for all pairs of product-rank `< n`.
* `StageB n`: the Conway `P`-inequalities for all quadruples whose four
  relevant product-ranks are `< n`.
Then:
* prove `StageA n` from all earlier stages;
* prove `StageB n` from `StageA n` by an inner induction on quadruple complexity;
* extract the final theorems.
-/

/-! ## Product-rank -/
/-- Complexity of a product. -/
def prodRank (x y : Game) : Nat := x.birthday + y.birthday

lemma prodRank_comm {x y : Game} : prodRank x y = prodRank y x := by
  dsimp [prodRank]
  rw [Nat.add_comm]

lemma prodRank_left_lt {x x' y : Game} (hx : x'.birthday < x.birthday) :
    prodRank x' y < prodRank x y := by
  dsimp [prodRank]
  exact add_lt_add_right hx _

lemma prodRank_right_lt {x y y' : Game} (hy : y'.birthday < y.birthday) :
    prodRank x y' < prodRank x y := by
  dsimp [prodRank]
  exact add_lt_add_left hy _

lemma prodRank_of_mem_left₁ {x y xl : Game} (hxl : xl ∈ x.left) :
    prodRank xl y < prodRank x y := by
  exact prodRank_left_lt (Game.birthday_lt_left hxl)

lemma prodRank_of_mem_right₁ {x y xr : Game} (hxr : xr ∈ x.right) :
    prodRank xr y < prodRank x y := by
  exact prodRank_left_lt (Game.birthday_lt_right hxr)

lemma prodRank_of_mem_left₂ {x y yl : Game} (hyl : yl ∈ y.left) :
    prodRank x yl < prodRank x y := by
  exact prodRank_right_lt (Game.birthday_lt_left hyl)

lemma prodRank_of_mem_right₂ {x y yr : Game} (hyr : yr ∈ y.right) :
    prodRank x yr < prodRank x y := by
  exact prodRank_right_lt (Game.birthday_lt_right hyr)

/-! ## Statement (iii): the `P`-inequalities -/

def MulCrossLe (x1 x2 y1 y2 : Game) : Prop :=
  ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≼ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2))

def MulCrossLt (x1 x2 y1 y2 : Game) : Prop :=
  ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≺ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2))

structure CrossRanksLT (n : Nat) (x1 x2 y1 y2 : Game) : Prop where
  h11 : prodRank x1 y1 < n
  h12 : prodRank x1 y2 < n
  h21 : prodRank x2 y1 < n
  h22 : prodRank x2 y2 < n

/-! ## Stage-indexed assertions `A(n)` and `B(n)` -/

/-- Stage `A(n)`: product is surreal, and multiplication respects equivalence
in the left factor, for all products of rank `< n`. -/
structure StageA (n : Nat) : Prop where
  surreal :
  ∀ {x y : Game}, IsSurreal x → IsSurreal y → prodRank x y < n → IsSurreal (x ⊗ y)
  congr_left :
  ∀ {x1 x2 y : Game},
    IsSurreal x1 → IsSurreal x2 → IsSurreal y → x1 ∼ x2 →
    prodRank x1 y < n → prodRank x2 y < n → (x1 ⊗ y) ∼ (x2 ⊗ y)

/-- Stage `B(n)`: all `P`-inequalities with the four relevant ranks `< n`. -/
structure StageB (n : Nat) : Prop where
  weak :
  ∀ {x1 x2 y1 y2 : Game},
    IsSurreal x1 → IsSurreal x2 → IsSurreal y1 → IsSurreal y2 →
    CrossRanksLT n x1 x2 y1 y2 → x1 ≼ x2 → y1 ≼ y2 → MulCrossLe x1 x2 y1 y2
  strict :
  ∀ {x1 x2 y1 y2 : Game},
    IsSurreal x1 → IsSurreal x2 → IsSurreal y1 → IsSurreal y2 →
    CrossRanksLT n x1 x2 y1 y2 → x1 ≺ x2 → y1 ≺ y2 → MulCrossLt x1 x2 y1 y2

abbrev StageData (n : Nat) : Prop := StageA n ∧ StageB n

lemma StageA.congr_right {n : Nat} {x y1 y2 : Game}
  (hA : StageA n) (hx : IsSurreal x) (hy1 : IsSurreal y1) (hy2 : IsSurreal y2)
  (hEq : y1 ∼ y2) (h1 : prodRank x y1 < n) (h2 : prodRank x y2 < n) :
    (x ⊗ y1) ∼ (x ⊗ y2) := by
  have h1' : prodRank y1 x < n := by
    simpa [prodRank_comm] using h1
  have h2' : prodRank y2 x < n := by
    simpa [prodRank_comm] using h2
  exact Game.eq_trans
    ⟨Game.mul_comm (a := x) (b := y1),
    Game.eq_trans ⟨hA.congr_left hy1 hy2 hx hEq h1' h2', Game.mul_comm (a := y2) (b := x)⟩⟩

/-! ## Access to previous stages -/

private lemma prevA {n m : Nat}
    (hprev : ∀ k < n, StageData k) (hm : m < n) : StageA m := by
  exact (hprev m hm).1

private lemma prevB {n m : Nat}
    (hprev : ∀ k < n, StageData k) (hm : m < n) : StageB m := by
  exact (hprev m hm).2

/-! ## Step A: proving product surreality and congruence from earlier stages -/

section StageAStep

variable {n : Nat}

/-!
The next four lemmas are the heart of statement (i):
use the `P`-inequalities from earlier stages to show that every left option
of `x ⊗ y` is `<` every right option of `x ⊗ y`.
-/

private lemma surreal_left_option {x L : Game}
  (hx : IsSurreal x) (hL : L ∈ x.left) : IsSurreal L := by
  unfold IsSurreal at hx
  exact hx.2.1 _ hL

private lemma surreal_right_option {x R : Game}
  (hx : IsSurreal x) (hR : R ∈ x.right) : IsSurreal R := by
  unfold IsSurreal at hx
  exact hx.2.2 _ hR

private lemma transport_le_of_eqv_add {u v t lhs rhs : Game}
    (h : u ≼ v) (hL : lhs ∼ (u ⊕ t)) (hR : (v ⊕ t) ∼ rhs) :
    lhs ≼ rhs := by
  exact Game.le_trans ⟨hL.1, Game.le_trans (Game.add_le_right_right t h) hR.1⟩

private lemma transport_lt_of_eqv_add {u v t lhs rhs : Game}
    (h : u ≺ v) (hL : lhs ∼ (u ⊕ t)) (hR : (v ⊕ t) ∼ rhs) :
    lhs ≺ rhs := by
  exact Game.lt_of_lt_of_le
    (Game.lt_of_le_of_lt hL.1 (Game.add_lt_right_right t h)) hR.1

private abbrev M (a b c d : Game) : Game := Game.mulOpt4 a b c d

private lemma transport_le_of_eqv_add {u v t lhs rhs : Game}
    (h : u ≼ v) (hL : lhs ∼ (u ⊕ t)) (hR : (v ⊕ t) ∼ rhs) :
    lhs ≼ rhs := by
  exact Game.le_trans ⟨hL.1, Game.le_trans (Game.add_le_right_right t h) hR.1⟩

private lemma transport_lt_of_eqv_add {u v t lhs rhs : Game}
    (h : u ≺ v) (hL : lhs ∼ (u ⊕ t)) (hR : (v ⊕ t) ∼ rhs) :
    lhs ≺ rhs := by
  exact Game.lt_of_lt_of_le
    (Game.lt_of_le_of_lt hL.1 (Game.add_lt_right_right t h)) hR.1


private lemma mulOpt4_xslot_mono_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M a e b d ≼ M c e b d := by
  sorry

private lemma mulOpt4_xslot_mono_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M a e b d ≺ M c e b d := by
  sorry

private lemma mulOpt4_xslot_antitone_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M c d b e ≼ M a d b e := by
  sorry

private lemma mulOpt4_xslot_antitone_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M c d b e ≺ M a d b e := by
  sorry

private lemma mulOpt4_yslot_mono_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M a b c d ≼ M a b c e := by
  sorry

private lemma mulOpt4_yslot_mono_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M a b c d ≺ M a b c e := by
  let u : Game := (a ⊗ e) ⊕ (c ⊗ d)
  let v : Game := (a ⊗ d) ⊕ (c ⊗ e)
  let t : Game := ((a ⊗ b) ⊕ (a ⊗ d).neg) ⊕ (a ⊗ e).neg
  have h' : u ≺ v := by
    simpa [u, v] using h
  have hL : M a b c d ∼ (u ⊕ t) := by
    refine Game.eq_of_q_eq ?_
    simp [M, mulOpt4, u, t]
    abel
  have hR : (v ⊕ t) ∼ M a b c e := by
    refine Game.eq_of_q_eq ?_
    simp [M, mulOpt4, v, t]
    abel
  exact transport_lt_of_eqv_add h' hL hR

private lemma mulOpt4_yslot_antitone_le_of_cross {a b c d e : Game}
    (h : MulCrossLe a c d e) :
    M c b a e ≼ M c b a d := by
  sorry

private lemma mulOpt4_yslot_antitone_lt_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    M c b a e ≺ M c b a d := by
  sorry

private lemma mul_left_right_case_LL {x y xL yL yR : Game}
  (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
  (hxL : xL ∈ x.left) (hyL : yL ∈ y.left) (hyR : yR ∈ y.right)
  (hxy : prodRank x y < n) :
  Game.mulOpt4 xL y x yL ≺ Game.mulOpt4 xL y x yR := by
  let m := prodRank x y
  have hm : m < n := hxy
  have hB : StageB m := prevB hprev hm
  have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
  have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
  have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
  have hxLx : xL ≺ x := by
    exact IsSurreal.left_lt hx hxL
  have hyLyR : yL ≺ yR := by
    exact Game.lt_trans ⟨(IsSurreal.left_lt hy hyL), (IsSurreal.lt_right hy hyR)⟩
  have hRanks : CrossRanksLT m xL x yL yR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL) hxL)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR) hxL)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR
  have hcross : MulCrossLt xL x yL yR :=
    hB.strict hxL_sur hx hyL_sur hyR_sur hRanks hxLx hyLyR
  exact mulOpt4_yslot_mono_lt_of_cross hcross

private lemma mulOpt4_yL_le_of_left_le {x y xL₁ xL₂ yL : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL₁ : xL₁ ∈ x.left) (hxL₂ : xL₂ ∈ x.left) (hyL : yL ∈ y.left)
    (hxy : prodRank x y < n) (h12 : xL₁ ≼ xL₂) :
    M xL₁ y x yL ≼ M xL₂ y x yL := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxL₁_sur : IsSurreal xL₁ := surreal_left_option hx hxL₁
  have hxL₂_sur : IsSurreal xL₂ := surreal_left_option hx hxL₂
  have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
  have hRanks : CrossRanksLT (prodRank x y) xL₁ xL₂ yL y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL) hxL₁)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL₁
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL) hxL₂)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL₂
  have hcross : MulCrossLe xL₁ xL₂ yL y :=
    hB.weak hxL₁_sur hxL₂_sur hyL_sur hy hRanks h12 (IsSurreal.left_lt hy hyL).1
  exact mulOpt4_xslot_mono_le_of_cross hcross

private lemma mulOpt4_yR_le_of_left_le {x y xL₁ xL₂ yR : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL₁ : xL₁ ∈ x.left) (hxL₂ : xL₂ ∈ x.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) (h21 : xL₂ ≼ xL₁) :
    M xL₁ y x yR ≼ M xL₂ y x yR := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxL₁_sur : IsSurreal xL₁ := surreal_left_option hx hxL₁
  have hxL₂_sur : IsSurreal xL₂ := surreal_left_option hx hxL₂
  have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
  have hRanks : CrossRanksLT (prodRank x y) xL₂ xL₁ y yR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL₂
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR) hxL₂)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL₁
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR) hxL₁)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
  have hcross : MulCrossLe xL₂ xL₁ y yR :=
    hB.weak hxL₂_sur hxL₁_sur hy hyR_sur hRanks h21 (IsSurreal.lt_right hy hyR).1
  exact mulOpt4_xslot_antitone_le_of_cross hcross

private lemma mul_left_right_case_LL_gen {x y xL₁ xL₂ yL yR : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL₁ : xL₁ ∈ x.left) (hxL₂ : xL₂ ∈ x.left)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xL₁ y x yL ≺ Game.mulOpt4 xL₂ y x yR := by
  change M xL₁ y x yL ≺ M xL₂ y x yR
  have hxL₁_sur : IsSurreal xL₁ := surreal_left_option hx hxL₁
  have hxL₂_sur : IsSurreal xL₂ := surreal_left_option hx hxL₂
  rcases IsSurreal.totality hxL₁_sur hxL₂_sur with h12 | h21
  · exact Game.lt_of_le_of_lt
      (mulOpt4_yL_le_of_left_le hprev hx hy hxL₁ hxL₂ hyL hxy h12)
      (by simpa [M] using mul_left_right_case_LL hprev hx hy hxL₂ hyL hyR hxy)
  · exact Game.lt_of_lt_of_le
      (by simpa [M] using mul_left_right_case_LL hprev hx hy hxL₁ hyL hyR hxy)
      (mulOpt4_yR_le_of_left_le hprev hx hy hxL₁ hxL₂ hyR hxy h21)

private lemma mul_left_right_case_LR {x y xL xR yL : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right) (hyL : yL ∈ y.left)
    (hxy : prodRank x y < n) :
    M xL y x yL ≺ M xR y x yL := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
  have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
  have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
  have hxLxR : xL ≺ xR := by
    exact Game.lt_trans ⟨IsSurreal.left_lt hx hxL, IsSurreal.lt_right hx hxR⟩
  have hyLy : yL ≺ y := IsSurreal.left_lt hy hyL
  have hRanks : CrossRanksLT (prodRank x y) xL xR yL y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL) hxL)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL) hxR)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR
  have hcross : MulCrossLt xL xR yL y :=
    hB.strict hxL_sur hxR_sur hyL_sur hy hRanks hxLxR hyLy
  exact mulOpt4_xslot_mono_lt_of_cross hcross

private lemma mulOpt4_xL_le_of_left_le {x y xL yL₁ yL₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyL₁ : yL₁ ∈ y.left) (hyL₂ : yL₂ ∈ y.left)
    (hxy : prodRank x y < n) (h12 : yL₁ ≼ yL₂) :
    M xL y x yL₁ ≼ M xL y x yL₂ := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
  have hyL₁_sur : IsSurreal yL₁ := surreal_left_option hy hyL₁
  have hyL₂_sur : IsSurreal yL₂ := surreal_left_option hy hyL₂
  have hRanks : CrossRanksLT (prodRank x y) xL x yL₁ yL₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL₁) hxL)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL₁)
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL₂) hxL)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL₂)
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL₁
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL₂
  have hcross : MulCrossLe xL x yL₁ yL₂ :=
    hB.weak hxL_sur hx hyL₁_sur hyL₂_sur hRanks (IsSurreal.left_lt hx hxL).1 h12
  exact mulOpt4_yslot_mono_le_of_cross hcross

private lemma mulOpt4_xR_le_of_left_le {x y xR yL₁ yL₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hyL₁ : yL₁ ∈ y.left) (hyL₂ : yL₂ ∈ y.left)
    (hxy : prodRank x y < n) (h21 : yL₂ ≼ yL₁) :
    M xR y x yL₁ ≼ M xR y x yL₂ := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
  have hyL₁_sur : IsSurreal yL₁ := surreal_left_option hy hyL₁
  have hyL₂_sur : IsSurreal yL₂ := surreal_left_option hy hyL₂
  have hRanks : CrossRanksLT (prodRank x y) x xR yL₂ yL₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL₂
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL₁
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL₂) hxR)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL₂)
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL₁) hxR)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL₁)
  have hcross : MulCrossLe x xR yL₂ yL₁ :=
    hB.weak hx hxR_sur hyL₂_sur hyL₁_sur hRanks (IsSurreal.lt_right hx hxR).1 h21
  exact mulOpt4_yslot_antitone_le_of_cross hcross

private lemma mul_left_right_case_LR_gen {x y xL xR yL₁ yL₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL₁ : yL₁ ∈ y.left) (hyL₂ : yL₂ ∈ y.left)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xL y x yL₁ ≺ Game.mulOpt4 xR y x yL₂ := by
  change M xL y x yL₁ ≺ M xR y x yL₂
  have hyL₁_sur : IsSurreal yL₁ := surreal_left_option hy hyL₁
  have hyL₂_sur : IsSurreal yL₂ := surreal_left_option hy hyL₂
  rcases IsSurreal.totality hyL₁_sur hyL₂_sur with h12 | h21
  · exact Game.lt_of_le_of_lt
      (mulOpt4_xL_le_of_left_le hprev hx hy hxL hyL₁ hyL₂ hxy h12)
      (by simpa [M] using mul_left_right_case_LR hprev hx hy hxL hxR hyL₂ hxy)
  · exact Game.lt_of_lt_of_le
      (by simpa [M] using mul_left_right_case_LR hprev hx hy hxL hxR hyL₁ hxy)
      (mulOpt4_xR_le_of_left_le hprev hx hy hxR hyL₁ hyL₂ hxy h21)


private lemma mul_left_right_case_RL {x y xR xL yR : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hxL : xL ∈ x.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) :
    M xR y x yR ≺ M xL y x yR := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
  have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
  have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
  have hxLxR : xL ≺ xR :=
    Game.lt_trans ⟨IsSurreal.left_lt hx hxL, IsSurreal.lt_right hx hxR⟩
  have hyyR : y ≺ yR := IsSurreal.lt_right hy hyR
  have hRanks : CrossRanksLT (prodRank x y) xL xR y yR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_left₁ (x := x) (y := y) hxL
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR) hxL)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR) hxR)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
  have hcross : MulCrossLt xL xR y yR :=
    hB.strict hxL_sur hxR_sur hy hyR_sur hRanks hxLxR hyyR
  exact mulOpt4_xslot_antitone_lt_of_cross hcross

private lemma mul_left_right_case_RR {x y xR yR yL : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hyR : yR ∈ y.right) (hyL : yL ∈ y.left)
    (hxy : prodRank x y < n) :
    M xR y x yR ≺ M xR y x yL := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
  have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
  have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
  have hxxR : x ≺ xR := IsSurreal.lt_right hx hxR
  have hyLyR : yL ≺ yR :=
    Game.lt_trans ⟨IsSurreal.left_lt hy hyL, IsSurreal.lt_right hy hyR⟩
  have hRanks : CrossRanksLT (prodRank x y) x xR yL yR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_left₂ (x := x) (y := y) hyL
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL) hxR)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR) hxR)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
  have hcross : MulCrossLt x xR yL yR :=
    hB.strict hx hxR_sur hyL_sur hyR_sur hRanks hxxR hyLyR
  exact mulOpt4_yslot_antitone_lt_of_cross hcross

  private lemma mulOpt4_xL_le_of_right_le {x y xL yR₁ yR₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyR₁ : yR₁ ∈ y.right) (hyR₂ : yR₂ ∈ y.right)
    (hxy : prodRank x y < n) (h12 : yR₁ ≼ yR₂) :
    M xL y x yR₁ ≼ M xL y x yR₂ := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxL_sur  : IsSurreal xL  := surreal_left_option  hx hxL
  have hyR₁_sur : IsSurreal yR₁ := surreal_right_option hy hyR₁
  have hyR₂_sur : IsSurreal yR₂ := surreal_right_option hy hyR₂
  have hRanks : CrossRanksLT (prodRank x y) xL x yR₁ yR₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR₁) hxL)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR₁)
    · exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR₂) hxL)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR₂)
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR₁
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR₂
  have hcross : MulCrossLe xL x yR₁ yR₂ :=
    hB.weak hxL_sur hx hyR₁_sur hyR₂_sur hRanks
      (IsSurreal.left_lt hx hxL).1 h12
  exact mulOpt4_yslot_mono_le_of_cross hcross

private lemma mulOpt4_xR_le_of_right_le {x y xR yR₁ yR₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hyR₁ : yR₁ ∈ y.right) (hyR₂ : yR₂ ∈ y.right)
    (hxy : prodRank x y < n) (h21 : yR₂ ≼ yR₁) :
    M xR y x yR₁ ≼ M xR y x yR₂ := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR_sur  : IsSurreal xR  := surreal_right_option hx hxR
  have hyR₁_sur : IsSurreal yR₁ := surreal_right_option hy hyR₁
  have hyR₂_sur : IsSurreal yR₂ := surreal_right_option hy hyR₂
  have hRanks : CrossRanksLT (prodRank x y) x xR yR₂ yR₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR₂
    · exact prodRank_of_mem_right₂ (x := x) (y := y) hyR₁
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR₂) hxR)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR₂)
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR₁) hxR)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR₁)
  have hcross : MulCrossLe x xR yR₂ yR₁ :=
    hB.weak hx hxR_sur hyR₂_sur hyR₁_sur hRanks
      (IsSurreal.lt_right hx hxR).1 h21
  exact mulOpt4_yslot_antitone_le_of_cross hcross

private lemma mulOpt4_yL_le_of_right_le {x y xR₁ xR₂ yL : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR₁ : xR₁ ∈ x.right) (hxR₂ : xR₂ ∈ x.right) (hyL : yL ∈ y.left)
    (hxy : prodRank x y < n) (h12 : xR₁ ≼ xR₂) :
    M xR₁ y x yL ≼ M xR₂ y x yL := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR₁_sur : IsSurreal xR₁ := surreal_right_option hx hxR₁
  have hxR₂_sur : IsSurreal xR₂ := surreal_right_option hx hxR₂
  have hyL_sur  : IsSurreal yL  := surreal_left_option  hy hyL
  have hRanks : CrossRanksLT (prodRank x y) xR₁ xR₂ yL y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL) hxR₁)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR₁
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL) hxR₂)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR₂
  have hcross : MulCrossLe xR₁ xR₂ yL y :=
    hB.weak hxR₁_sur hxR₂_sur hyL_sur hy hRanks
      h12 (IsSurreal.left_lt hy hyL).1
  exact mulOpt4_xslot_mono_le_of_cross hcross

private lemma mulOpt4_yR_le_of_right_le {x y xR₁ xR₂ yR : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR₁ : xR₁ ∈ x.right) (hxR₂ : xR₂ ∈ x.right) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) (h21 : xR₂ ≼ xR₁) :
    M xR₁ y x yR ≼ M xR₂ y x yR := by
  have hB : StageB (prodRank x y) := prevB hprev hxy
  have hxR₁_sur : IsSurreal xR₁ := surreal_right_option hx hxR₁
  have hxR₂_sur : IsSurreal xR₂ := surreal_right_option hx hxR₂
  have hyR_sur  : IsSurreal yR  := surreal_right_option hy hyR
  have hRanks : CrossRanksLT (prodRank x y) xR₂ xR₁ y yR := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR₂
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR) hxR₂)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    · exact prodRank_of_mem_right₁ (x := x) (y := y) hxR₁
    · exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR) hxR₁)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
  have hcross : MulCrossLe xR₂ xR₁ y yR :=
    hB.weak hxR₂_sur hxR₁_sur hy hyR_sur hRanks
      h21 (IsSurreal.lt_right hy hyR).1
  exact mulOpt4_xslot_antitone_le_of_cross hcross

private lemma mul_left_right_case_RL_gen {x y xR₁ xL₂ yR₁ yR₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR₁ : xR₁ ∈ x.right) (hxL₂ : xL₂ ∈ x.left)
    (hyR₁ : yR₁ ∈ y.right) (hyR₂ : yR₂ ∈ y.right)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xR₁ y x yR₁ ≺ Game.mulOpt4 xL₂ y x yR₂ := by
  change M xR₁ y x yR₁ ≺ M xL₂ y x yR₂
  have hyR₁_sur : IsSurreal yR₁ := surreal_right_option hy hyR₁
  have hyR₂_sur : IsSurreal yR₂ := surreal_right_option hy hyR₂
  rcases IsSurreal.totality hyR₁_sur hyR₂_sur with h12 | h21
  · -- yR₁ ≼ yR₂ :  M xR₁ y x yR₁ ≺ M xL₂ y x yR₁ ≼ M xL₂ y x yR₂
    exact Game.lt_of_lt_of_le
      (by simpa [M] using
        mul_left_right_case_RL hprev hx hy hxR₁ hxL₂ hyR₁ hxy)
      (mulOpt4_xL_le_of_right_le hprev hx hy hxL₂ hyR₁ hyR₂ hxy h12)
  · -- yR₂ ≼ yR₁ :  M xR₁ y x yR₁ ≼ M xR₁ y x yR₂ ≺ M xL₂ y x yR₂
    exact Game.lt_of_le_of_lt
      (mulOpt4_xR_le_of_right_le hprev hx hy hxR₁ hyR₁ hyR₂ hxy h21)
      (by simpa [M] using
        mul_left_right_case_RL hprev hx hy hxR₁ hxL₂ hyR₂ hxy)

private lemma mul_left_right_case_RR_gen {x y xR₁ xR₂ yR₁ yL₂ : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR₁ : xR₁ ∈ x.right) (hxR₂ : xR₂ ∈ x.right)
    (hyR₁ : yR₁ ∈ y.right) (hyL₂ : yL₂ ∈ y.left)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xR₁ y x yR₁ ≺ Game.mulOpt4 xR₂ y x yL₂ := by
  change M xR₁ y x yR₁ ≺ M xR₂ y x yL₂
  have hxR₁_sur : IsSurreal xR₁ := surreal_right_option hx hxR₁
  have hxR₂_sur : IsSurreal xR₂ := surreal_right_option hx hxR₂
  rcases IsSurreal.totality hxR₁_sur hxR₂_sur with h12 | h21
  · -- xR₁ ≼ xR₂ :  M xR₁ y x yR₁ ≺ M xR₁ y x yL₂ ≼ M xR₂ y x yL₂
    exact Game.lt_of_lt_of_le
      (by simpa [M] using
        mul_left_right_case_RR hprev hx hy hxR₁ hyR₁ hyL₂ hxy)
      (mulOpt4_yL_le_of_right_le hprev hx hy hxR₁ hxR₂ hyL₂ hxy h12)
  · -- xR₂ ≼ xR₁ :  M xR₁ y x yR₁ ≼ M xR₂ y x yR₁ ≺ M xR₂ y x yL₂
    exact Game.lt_of_le_of_lt
      (mulOpt4_yR_le_of_right_le hprev hx hy hxR₁ hxR₂ hyR₁ hxy h21)
      (by simpa [M] using
        mul_left_right_case_RR hprev hx hy hxR₂ hyR₁ hyL₂ hxy)


private lemma mul_left_lt_right_of_prevB {x y L R : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hL : L ∈ (x ⊗ y).left) (hR : R ∈ (x ⊗ y).right) :
    ¬ (R ≼ L) := by
  rw [mem_mul_left] at hL
  rw [mem_mul_right] at hR
  rcases hL with
    ⟨xL₁, hxL₁, yL₁, hyL₁, rfl⟩ | ⟨xR₁, hxR₁, yR₁, hyR₁, rfl⟩
  · rcases hR with
      ⟨xL₂, hxL₂, yR₂, hyR₂, rfl⟩ | ⟨xR₂, hxR₂, yL₂, hyL₂, rfl⟩
    · exact (mul_left_right_case_LL_gen hprev hx hy hxL₁ hxL₂ hyL₁ hyR₂ hxy).2
    · exact (mul_left_right_case_LR_gen hprev hx hy hxL₁ hxR₂ hyL₁ hyL₂ hxy).2
  · rcases hR with
      ⟨xL₂, hxL₂, yR₂, hyR₂, rfl⟩ | ⟨xR₂, hxR₂, yL₂, hyL₂, rfl⟩
    · exact (mul_left_right_case_RL_gen hprev hx hy hxR₁ hxL₂ hyR₁ hyR₂ hxy).2
    · exact (mul_left_right_case_RR_gen hprev hx hy hxR₁ hxR₂ hyR₁ hyL₂ hxy).2

/-!
Next: recursive surreality of the options of `x ⊗ y`.
Each option is a sum/negative of smaller products, so this uses only
earlier instances of `StageA`.
-/

private lemma mul_left_option_isSurreal_of_prevA {x y L : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hL : L ∈ (x ⊗ y).left) :
    IsSurreal L := by
  have hA : StageA (prodRank x y) := prevA hprev hxy
  rw [mem_mul_left] at hL
  rcases hL with ⟨xL, hxL, yL, hyL, rfl⟩ | ⟨xR, hxR, yR, hyR, rfl⟩
  · have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
    have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
    have h₁ : IsSurreal (xL ⊗ y) := by
      exact hA.surreal hxL_sur hy (prodRank_of_mem_left₁ (x := x) (y := y) hxL)
    have h₂ : IsSurreal (x ⊗ yL) := by
      exact hA.surreal hx hyL_sur (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    have h₃rank : prodRank xL yL < prodRank x y := by
      exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yL) hxL)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    have h₃ : IsSurreal (xL ⊗ yL) := by
      exact hA.surreal hxL_sur hyL_sur h₃rank
    have h₁₂ : IsSurreal ((xL ⊗ y) ⊕ (x ⊗ yL)) := by
      simpa using
        (Surreal.add_isSurreal
          (a := ⟨xL ⊗ y, h₁⟩)
          (b := ⟨x ⊗ yL, h₂⟩))
    have hneg : IsSurreal (Game.neg (xL ⊗ yL)) := by
      simpa using (Surreal.neg_isSurreal ⟨xL ⊗ yL, h₃⟩)
    simpa [Game.mulOpt4] using
      (Surreal.add_isSurreal
        (a := ⟨(xL ⊗ y) ⊕ (x ⊗ yL), h₁₂⟩)
        (b := ⟨Game.neg (xL ⊗ yL), hneg⟩))
  · have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
    have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
    have h₁ : IsSurreal (xR ⊗ y) := by
      exact hA.surreal hxR_sur hy (prodRank_of_mem_right₁ (x := x) (y := y) hxR)
    have h₂ : IsSurreal (x ⊗ yR) := by
      exact hA.surreal hx hyR_sur (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    have h₃rank : prodRank xR yR < prodRank x y := by
      exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yR) hxR)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    have h₃ : IsSurreal (xR ⊗ yR) := by
      exact hA.surreal hxR_sur hyR_sur h₃rank
    have h₁₂ : IsSurreal ((xR ⊗ y) ⊕ (x ⊗ yR)) := by
      simpa using
        (Surreal.add_isSurreal
          (a := ⟨xR ⊗ y, h₁⟩)
          (b := ⟨x ⊗ yR, h₂⟩))
    have hneg : IsSurreal (Game.neg (xR ⊗ yR)) := by
      simpa using (Surreal.neg_isSurreal ⟨xR ⊗ yR, h₃⟩)
    simpa [Game.mulOpt4] using
      (Surreal.add_isSurreal
        (a := ⟨(xR ⊗ y) ⊕ (x ⊗ yR), h₁₂⟩)
        (b := ⟨Game.neg (xR ⊗ yR), hneg⟩))

private lemma mul_right_option_isSurreal_of_prevA {x y R : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hR : R ∈ (x ⊗ y).right) :
    IsSurreal R := by
  have hA : StageA (prodRank x y) := prevA hprev hxy
  rw [mem_mul_right] at hR
  rcases hR with ⟨xL, hxL, yR, hyR, rfl⟩ | ⟨xR, hxR, yL, hyL, rfl⟩
  · have hxL_sur : IsSurreal xL := surreal_left_option hx hxL
    have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
    have h₁ : IsSurreal (xL ⊗ y) := by
      exact hA.surreal hxL_sur hy (prodRank_of_mem_left₁ (x := x) (y := y) hxL)
    have h₂ : IsSurreal (x ⊗ yR) := by
      exact hA.surreal hx hyR_sur (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    have h₃rank : prodRank xL yR < prodRank x y := by
      exact Nat.lt_trans
        (prodRank_of_mem_left₁ (x := x) (y := yR) hxL)
        (prodRank_of_mem_right₂ (x := x) (y := y) hyR)
    have h₃ : IsSurreal (xL ⊗ yR) := by
      exact hA.surreal hxL_sur hyR_sur h₃rank
    have h₁₂ : IsSurreal ((xL ⊗ y) ⊕ (x ⊗ yR)) := by
      simpa using
        (Surreal.add_isSurreal
          (a := ⟨xL ⊗ y, h₁⟩)
          (b := ⟨x ⊗ yR, h₂⟩))
    have hneg : IsSurreal (Game.neg (xL ⊗ yR)) := by
      simpa using (Surreal.neg_isSurreal ⟨xL ⊗ yR, h₃⟩)
    simpa [Game.mulOpt4] using
      (Surreal.add_isSurreal
        (a := ⟨(xL ⊗ y) ⊕ (x ⊗ yR), h₁₂⟩)
        (b := ⟨Game.neg (xL ⊗ yR), hneg⟩))
  · have hxR_sur : IsSurreal xR := surreal_right_option hx hxR
    have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
    have h₁ : IsSurreal (xR ⊗ y) := by
      exact hA.surreal hxR_sur hy (prodRank_of_mem_right₁ (x := x) (y := y) hxR)
    have h₂ : IsSurreal (x ⊗ yL) := by
      exact hA.surreal hx hyL_sur (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    have h₃rank : prodRank xR yL < prodRank x y := by
      exact Nat.lt_trans
        (prodRank_of_mem_right₁ (x := x) (y := yL) hxR)
        (prodRank_of_mem_left₂ (x := x) (y := y) hyL)
    have h₃ : IsSurreal (xR ⊗ yL) := by
      exact hA.surreal hxR_sur hyL_sur h₃rank
    have h₁₂ : IsSurreal ((xR ⊗ y) ⊕ (x ⊗ yL)) := by
      simpa using
        (Surreal.add_isSurreal
          (a := ⟨xR ⊗ y, h₁⟩)
          (b := ⟨x ⊗ yL, h₂⟩))
    have hneg : IsSurreal (Game.neg (xR ⊗ yL)) := by
      simpa using (Surreal.neg_isSurreal ⟨xR ⊗ yL, h₃⟩)
    simpa [Game.mulOpt4] using
      (Surreal.add_isSurreal
        (a := ⟨(xR ⊗ y) ⊕ (x ⊗ yL), h₁₂⟩)
        (b := ⟨Game.neg (xR ⊗ yL), hneg⟩))

private theorem stageA_surreal_of_prev {x y : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) : IsSurreal (x ⊗ y) := by
  unfold IsSurreal
  constructor
  · intro L hL R hR
    exact mul_left_lt_right_of_prevB hprev hx hy hxy hL hR
  · constructor
    · intro L hL
      exact mul_left_option_isSurreal_of_prevA hprev hx hy hxy hL
    · intro R hR
      exact mul_right_option_isSurreal_of_prevA hprev hx hy hxy hR

/-!
Now statement (ii): multiplication respects equivalence in the left factor.
As in your strategy note, this is proved by matching left/right options and
using:

* strict `P`-inequalities from earlier `StageB`,
* congruence on the simpler factor from earlier `StageA`.
-/


private lemma lt_max4_succ₁ (a b c d : Nat) :
    a < max (max a b) (max c d) + 1 := by
  exact Nat.lt_succ_of_le <|
    (le_max_left a b).trans (le_max_left (max a b) (max c d))

private lemma lt_max4_succ₂ (a b c d : Nat) :
    b < max (max a b) (max c d) + 1 := by
  exact Nat.lt_succ_of_le <|
    (le_max_right a b).trans (le_max_left (max a b) (max c d))

private lemma lt_max4_succ₃ (a b c d : Nat) :
    c < max (max a b) (max c d) + 1 := by
  exact Nat.lt_succ_of_le <|
    (le_max_left c d).trans (le_max_right (max a b) (max c d))

private lemma lt_max4_succ₄ (a b c d : Nat) :
    d < max (max a b) (max c d) + 1 := by
  exact Nat.lt_succ_of_le <|
    (le_max_right c d).trans (le_max_right (max a b) (max c d))

private lemma stageB_strict_of_prev
    (hprev : ∀ m < n, StageData m)
    {x1 x2 y1 y2 : Game}
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2)
    (hy1 : IsSurreal y1) (hy2 : IsSurreal y2)
    (hxy : x1 ≺ x2) (hyy : y1 ≺ y2)
    (h11 : prodRank x1 y1 < n) (h12 : prodRank x1 y2 < n)
    (h21 : prodRank x2 y1 < n) (h22 : prodRank x2 y2 < n) :
    ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≺ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2)) := by
  let m :=
    max (max (prodRank x1 y1) (prodRank x1 y2))
      (max (prodRank x2 y1) (prodRank x2 y2)) + 1
  have hm_lt_n : m < n := by
    dsimp [m]
    sorry
  have hm11 : prodRank x1 y1 < m := by
    dsimp [m]
    exact lt_max4_succ₁
      (prodRank x1 y1) (prodRank x1 y2) (prodRank x2 y1) (prodRank x2 y2)
  have hm12 : prodRank x1 y2 < m := by
    dsimp [m]
    exact lt_max4_succ₂
      (prodRank x1 y1) (prodRank x1 y2) (prodRank x2 y1) (prodRank x2 y2)
  have hm21 : prodRank x2 y1 < m := by
    dsimp [m]
    exact lt_max4_succ₃
      (prodRank x1 y1) (prodRank x1 y2) (prodRank x2 y1) (prodRank x2 y2)
  have hm22 : prodRank x2 y2 < m := by
    dsimp [m]
    exact lt_max4_succ₄
      (prodRank x1 y1) (prodRank x1 y2) (prodRank x2 y1) (prodRank x2 y2)
  have hBₘ : StageB m := (hprev m hm_lt_n).2
  have hCross : CrossRanksLT m x1 x2 y1 y2 := by exact ⟨hm11, hm12, hm21, hm22⟩
  simpa [MulCrossLt] using
    hBₘ.strict hx1 hx2 hy1 hy2 hCross hxy hyy

private lemma lt_max2_succ_left (a b : Nat) :
    a < max a b + 1 := by
  exact Nat.lt_succ_of_le (le_max_left a b)

private lemma lt_max2_succ_right (a b : Nat) :
    b < max a b + 1 := by
  exact Nat.lt_succ_of_le (le_max_right a b)

private lemma stageA_eq_of_prev
    (hprev : ∀ m < n, StageData m)
    {x1 x2 y : Game}
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2)
    (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  let m := max (prodRank x1 y) (prodRank x2 y) + 1
  have hm_lt_n : m < n := by
    dsimp [m]
    sorry
  have hm1 : prodRank x1 y < m := by
    dsimp [m]
    exact lt_max2_succ_left (prodRank x1 y) (prodRank x2 y)
  have hm2 : prodRank x2 y < m := by
    dsimp [m]
    exact lt_max2_succ_right (prodRank x1 y) (prodRank x2 y)
  have hAₘ : StageA m := (hprev m hm_lt_n).1
  exact hAₘ.congr_left hx1 hx2 hy hEq hm1 hm2


private lemma lt_of_add_lt_add_cancel_right
    {A B C D : Game}
    (h : (A ⊕ B) ≺ (C ⊕ D)) :
    ((A ⊕ B) ⊕ (C.neg)) ≺ D := by
  have hshift : ((A ⊕ B) ⊕ (C.neg)) ≺ ((C ⊕ D) ⊕ (C.neg)) := by
    exact Game.add_lt_add_right h (C.neg)

  have hcancel : ((C ⊕ D) ⊕ (C.neg)) ≼ D := by
    have h₁ : ((C ⊕ D) ⊕ (C.neg)) ≼ (C ⊕ (D ⊕ (C.neg))) :=
      (Game.add_assoc (a := C) (b := D) (c := C.neg)).1

    have h₂ : (C ⊕ (D ⊕ (C.neg))) ≼ (C ⊕ ((C.neg) ⊕ D)) := by
      exact
        (Game.add_equal
          ⟨Game.eq_congr, Game.add_comm (a := D) (b := C.neg)⟩).1

    have h₃ : (C ⊕ ((C.neg) ⊕ D)) ≼ (C ⊕ (C.neg)) ⊕ D :=
      (Game.add_assoc (a := C) (b := C.neg) (c := D)).2

    have h₄ : (C ⊕ (C.neg)) ⊕ D ≼ ((0 : Game) ⊕ D) := by
      exact
        (Game.add_equal
          ⟨Game.add_right_neg C, Game.eq_congr⟩).1

    have h₅ : (0 : Game) ⊕ D ≼ D :=
      (Game.zero_add D).1

    exact Game.le_trans h₁ <|
      Game.le_trans h₂ <|
      Game.le_trans h₃ <|
      Game.le_trans h₄ h₅

  exact Game.lt_of_lt_of_le hshift hcancel


private lemma left_option_mul_lt_of_prev {x1 x2 y L : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hL : L ∈ (x1 ⊗ y).left) :
    L ≺ (x2 ⊗ y) := by
  rw [mem_mul_left] at hL
  rcases hL with
    ⟨x1L, hx1L, yL, hyL, rfl⟩ |
    ⟨x1R, hx1R, yR, hyR, rfl⟩
  · have hx1L_sur : IsSurreal x1L := IsSurreal.isSurreal_left hx1 hx1L
    have hyL_sur : IsSurreal yL := IsSurreal.isSurreal_left hy hyL
    have h1_yL : prodRank x1 yL < n := by
      have h : prodRank x1 yL < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_left (Game.birthday_lt_left hyL) _
      exact Nat.lt_trans h h1

    have h2_yL : prodRank x2 yL < n := by
      have h : prodRank x2 yL < prodRank x2 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_left (Game.birthday_lt_left hyL) _
      exact Nat.lt_trans h h2

    have h1L_y : prodRank x1L y < n := by
      have h : prodRank x1L y < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_right (Game.birthday_lt_left hx1L) _
      exact Nat.lt_trans h h1

    have h1L_yL : prodRank x1L yL < n := by
      have h : prodRank x1L yL < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add (Game.birthday_lt_left hx1L) (Game.birthday_lt_left hyL)
      exact Nat.lt_trans h h1

    have hsmall : (x1 ⊗ yL) ∼ (x2 ⊗ yL) := by
      exact stageA_eq_of_prev hprev
        (x1 := x1) (x2 := x2) (y := yL)
        hx1 hx2 hyL_sur hEq h1_yL h2_yL

    have hrewrite : M x1L y x1 yL ∼ M x1L y x2 yL := by
      change Game.mulOpt4 x1L y x1 yL ∼ Game.mulOpt4 x1L y x2 yL
      dsimp [Game.mulOpt4]
      exact Game.add_equal ⟨Game.add_equal ⟨Game.eq_congr, hsmall⟩, Game.eq_congr⟩

    have hx1L_lt_x2 : x1L ≺ x2 := by
      exact Game.lt_of_lt_of_le (IsSurreal.left_lt hx1 hx1L) hEq.1

    have hyL_lt_y : yL ≺ y := by
      exact IsSurreal.left_lt hy hyL

    have hsum :
        ((x1L ⊗ y) ⊕ (x2 ⊗ yL)) ≺ ((x1L ⊗ yL) ⊕ (x2 ⊗ y)) := by
      exact stageB_strict_of_prev hprev
        (x1 := x1L) (x2 := x2) (y1 := yL) (y2 := y)
        hx1L_sur hx2 hyL_sur hy
        hx1L_lt_x2 hyL_lt_y
        h1L_yL h1L_y h2_yL h2

    have hstrict : M x1L y x2 yL ≺ (x2 ⊗ y) := by
      simpa [M, Game.mulOpt4] using
        lt_of_add_lt_add_cancel_right
          (A := x1L ⊗ y) (B := x2 ⊗ yL)
          (C := x1L ⊗ yL) (D := x2 ⊗ y) hsum

    exact Game.lt_of_le_of_lt hrewrite.1 hstrict

  · have hx1R_sur : IsSurreal x1R := IsSurreal.isSurreal_right hx1 hx1R
    have hyR_sur : IsSurreal yR := IsSurreal.isSurreal_right hy hyR

    have h1_yR : prodRank x1 yR < n := by
      have h : prodRank x1 yR < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_left (Game.birthday_lt_right hyR) _
      exact Nat.lt_trans h h1

    have h2_yR : prodRank x2 yR < n := by
      have h : prodRank x2 yR < prodRank x2 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_left (Game.birthday_lt_right hyR) _
      exact Nat.lt_trans h h2

    have h1R_y : prodRank x1R y < n := by
      have h : prodRank x1R y < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add_right (Game.birthday_lt_right hx1R) _
      exact Nat.lt_trans h h1

    have h1R_yR : prodRank x1R yR < n := by
      have h : prodRank x1R yR < prodRank x1 y := by
        dsimp [prodRank]
        exact Nat.add_lt_add (Game.birthday_lt_right hx1R) (Game.birthday_lt_right hyR)
      exact Nat.lt_trans h h1

    have hsmall : (x1 ⊗ yR) ∼ (x2 ⊗ yR) := by
      exact stageA_eq_of_prev hprev
        (x1 := x1) (x2 := x2) (y := yR)
        hx1 hx2 hyR_sur hEq h1_yR h2_yR

    have hrewrite : M x1R y x1 yR ∼ M x1R y x2 yR := by
      change Game.mulOpt4 x1R y x1 yR ∼ Game.mulOpt4 x1R y x2 yR
      dsimp [Game.mulOpt4]
      exact Game.add_equal ⟨Game.add_equal ⟨Game.eq_congr, hsmall⟩, Game.eq_congr⟩

    have hx2_lt_x1R : x2 ≺ x1R := by
      exact Game.lt_of_le_of_lt hEq.2 (IsSurreal.lt_right hx1 hx1R)

    have hy_lt_yR : y ≺ yR := by
      exact IsSurreal.lt_right hy hyR

    have hsum₀ :
        ((x2 ⊗ yR) ⊕ (x1R ⊗ y)) ≺ ((x2 ⊗ y) ⊕ (x1R ⊗ yR)) := by
      exact stageB_strict_of_prev hprev
        (x1 := x2) (x2 := x1R) (y1 := y) (y2 := yR)
        hx2 hx1R_sur hy hyR_sur
        hx2_lt_x1R hy_lt_yR
        h2 h2_yR h1R_y h1R_yR

    have hsum :
        ((x1R ⊗ y) ⊕ (x2 ⊗ yR)) ≺ ((x1R ⊗ yR) ⊕ (x2 ⊗ y)) := by
      have hleft :
          ((x1R ⊗ y) ⊕ (x2 ⊗ yR)) ≼ ((x2 ⊗ yR) ⊕ (x1R ⊗ y)) :=
        (Game.add_comm (a := x1R ⊗ y) (b := x2 ⊗ yR)).1
      have hright :
          ((x2 ⊗ y) ⊕ (x1R ⊗ yR)) ≼ ((x1R ⊗ yR) ⊕ (x2 ⊗ y)) :=
        (Game.add_comm (a := x2 ⊗ y) (b := x1R ⊗ yR)).1
      exact Game.lt_of_lt_of_le (Game.lt_of_le_of_lt hleft hsum₀) hright

    have hstrict : M x1R y x2 yR ≺ (x2 ⊗ y) := by
      simpa [M, Game.mulOpt4] using
        lt_of_add_lt_add_cancel_right
          (A := x1R ⊗ y) (B := x2 ⊗ yR)
          (C := x1R ⊗ yR) (D := x2 ⊗ y) hsum

    exact Game.lt_of_le_of_lt hrewrite.1 hstrict











private lemma mul_lt_right_option_of_prev {x1 x2 y R : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x2 ∼ x1) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hR : R ∈ (x2 ⊗ y).right) :
    (x1 ⊗ y) ≺ R := by
  rw [mem_mul_right] at hR
  rcases hR with
    ⟨x2L, hx2L, yR, hyR, rfl⟩ |
    ⟨x2R, hx2R, yL, hyL, rfl⟩
  · have hx2L_sur : IsSurreal x2L := surreal_left_option hx2 hx2L
    have hyR_sur : IsSurreal yR := surreal_right_option hy hyR
    have hsmall : (x1 ⊗ yR) ∼ (x2 ⊗ yR) := by
      sorry
    have hrewrite : M x2L y x1 yR ∼ M x2L y x2 yR := by
      sorry
    have hstrict : (x1 ⊗ y) ≺ M x2L y x1 yR := by
      /-
      Here one uses `StageB` at a suitable smaller rank, with:
        x2L ≺ x1   and   y ≺ yR.
      -/
      sorry
    exact Game.lt_of_lt_of_le hstrict hrewrite.1
  · have hx2R_sur : IsSurreal x2R := surreal_right_option hx2 hx2R
    have hyL_sur : IsSurreal yL := surreal_left_option hy hyL
    have hsmall : (x1 ⊗ yL) ∼ (x2 ⊗ yL) := by
      sorry
    have hrewrite : M x2R y x1 yL ∼ M x2R y x2 yL := by
      sorry
    have hstrict : (x1 ⊗ y) ≺ M x2R y x1 yL := by
      /-
      Here one uses `StageB` at a suitable smaller rank, with:
        x1 ≺ x2R   and   yL ≺ y.
      -/
      sorry
    exact Game.lt_of_lt_of_le hstrict hrewrite.1

private lemma stageA_le_left_of_prev {x1 x2 y : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n) :
    (x1 ⊗ y) ≼ (x2 ⊗ y) := by
  rw [Game.le]
  constructor
  · intro L hL hcontra
    exact (left_option_mul_lt_of_prev hprev hx1 hx2 hy hEq h1 h2 hL).2 hcontra
  · intro R hR hcontra
    exact (mul_lt_right_option_of_prev hprev hx1 hx2 hy (Game.eq_symm hEq) h1 h2 hR).2 hcontra

private theorem stageA_congr_left_of_prev {x1 x2 y : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  constructor
  · exact stageA_le_left_of_prev hprev hx1 hx2 hy hEq h1 h2
  · exact stageA_le_left_of_prev hprev hx2 hx1 hy (Game.eq_symm hEq) h2 h1

theorem stageA_of_prev (hprev : ∀ m < n, StageData m) : StageA n := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy hxy
    exact stageA_surreal_of_prev hprev hx hy hxy
  · intro x1 x2 y hx1 hx2 hy hEq h1 h2
    exact stageA_congr_left_of_prev hprev hx1 hx2 hy hEq h1 h2

end StageAStep

/-! ## Inner induction for `StageB` -/

structure QuadResult (q : QuadGame) : Prop where
  weak :
    q.x1 ≼ q.x2 → q.y1 ≼ q.y2 →
    MulCrossLe q.x1 q.x2 q.y1 q.y2
  strict :
    q.x1 ≺ q.x2 → q.y1 ≺ q.y2 →
    MulCrossLt q.x1 q.x2 q.y1 q.y2

section StageBStep

variable {n : Nat}

/-!
Base cases for the inner induction:
these are exactly the inequalities of the form `P(xL, x : yL, y)` etc.,
reduced to “a left option of `x ⊗ y` is `< x ⊗ y`”, using `StageA n`.
-/

private lemma add_back_cancel_le
    {A B C : Game} :
    (A ⊕ B) ≼ (((A ⊕ B) ⊕ (C.neg)) ⊕ C) := by
  sorry

private lemma mulCrossLt_of_M_lt
    {x1 x2 y1 y2 : Game}
    (h : M x1 y2 x2 y1 ≺ (x2 ⊗ y2)) :
    MulCrossLt x1 x2 y1 y2 := by
  have h' : (M x1 y2 x2 y1 ⊕ (x1 ⊗ y1)) ≺ ((x2 ⊗ y2) ⊕ (x1 ⊗ y1)) := by
    exact Game.add_lt_add_right h (x1 ⊗ y1)
  have hleft :
      ((x1 ⊗ y2) ⊕ (x2 ⊗ y1)) ≼ (M x1 y2 x2 y1 ⊕ (x1 ⊗ y1)) := by
    simpa [M, Game.mulOpt4] using
      (add_back_cancel_le
        (A := x1 ⊗ y2) (B := x2 ⊗ y1) (C := x1 ⊗ y1))
  have hright :
      ((x2 ⊗ y2) ⊕ (x1 ⊗ y1)) ≼ ((x1 ⊗ y1) ⊕ (x2 ⊗ y2)) := by
    exact (Game.add_comm (a := x2 ⊗ y2) (b := x1 ⊗ y1)).1
  exact Game.lt_of_lt_of_le (Game.lt_of_le_of_lt hleft h') hright

private lemma base_P_LL {x y xL yL : Game}
    (hA : StageA n) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyL : yL ∈ y.left) (hxy : prodRank x y < n) :
    MulCrossLt xL x yL y := by
  have hxy_sur : IsSurreal (x ⊗ y) := by
    exact hA.surreal hx hy hxy
  have hmem : M xL y x yL ∈ (x ⊗ y).left := by
    rw [mem_mul_left]
    exact Or.inl ⟨xL, hxL, yL, hyL, rfl⟩
  have hlt : M xL y x yL ≺ (x ⊗ y) := by
    exact IsSurreal.left_lt hxy_sur hmem
  exact mulCrossLt_of_M_lt hlt




private lemma base_P_LR {x y xL yR : Game}
    (hA : StageA n) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyR : yR ∈ y.right) (hxy : prodRank x y < n) :
    MulCrossLt xL x y yR := by
  sorry

private lemma base_P_RL {x y xR yL : Game}
    (hA : StageA n) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hyL : yL ∈ y.left) (hxy : prodRank x y < n) :
    MulCrossLt x xR yL y := by
  sorry

private lemma base_P_RR {x y xR yR : Game}
    (hA : StageA n) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxR : xR ∈ x.right) (hyR : yR ∈ y.right) (hxy : prodRank x y < n) :
    MulCrossLt x xR y yR := by
  sorry


/-! ### Step (2): one-sided generalizations

Here the idea is:
* from the base cases, prove `P(xL,x,y1,y2)` and `P(x,xR,y1,y2)` for arbitrary `y1,y2`,
* and symmetrically prove `P(x1,x2,yL,y)` and `P(x1,x2,y,yR)` for arbitrary `x1,x2`.

These are the “anchored” versions of `P`, where one side is still an immediate option.
-/

/-- Generalize `P(xL, x, y1, y2)` from the base cases and smaller quadruples. -/
private lemma step2_xLx_weak {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hxL : q.x1 ∈ q.x2.left)
    (hy : q.y1 ≼ q.y2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  sorry

private lemma step2_xLx_strict {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hxL : q.x1 ∈ q.x2.left)
    (hy : q.y1 ≺ q.y2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  sorry

/-- Generalize `P(x, xR, y1, y2)` from the base cases and smaller quadruples. -/
private lemma step2_xxR_weak {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hxR : q.x2 ∈ q.x1.right)
    (hy : q.y1 ≼ q.y2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  sorry

private lemma step2_xxR_strict {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hxR : q.x2 ∈ q.x1.right)
    (hy : q.y1 ≺ q.y2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  sorry

/-- Generalize `P(x1, x2, yL, y)` from the base cases and smaller quadruples. -/
private lemma step2_yLy_weak {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hyL : q.y1 ∈ q.y2.left)
    (hx : q.x1 ≼ q.x2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  sorry

private lemma step2_yLy_strict {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hyL : q.y1 ∈ q.y2.left)
    (hx : q.x1 ≺ q.x2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  sorry

/-- Generalize `P(x1, x2, y, yR)` from the base cases and smaller quadruples. -/
private lemma step2_yyR_weak {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hyR : q.y2 ∈ q.y1.right)
    (hx : q.x1 ≼ q.x2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  sorry

private lemma step2_yyR_strict {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hyR : q.y2 ∈ q.y1.right)
    (hx : q.x1 ≺ q.x2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  sorry

/-! ### Step (3): full generalization to arbitrary quadruples

At this point one proves that every left option of the left-hand side of `P`
is `<` the full right-hand side, and symmetrically that the full left-hand side
is `<` every right option of the right-hand side.

The reduction of a general option lands in one of the Step (2) anchored cases.
-/

/-- Every left option of the left side of `P(q)` is `<` the right side. -/
private lemma left_option_mulCross_lt_of_smaller {q : QuadGame} {L : Game}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≼ q.x2) (hy : q.y1 ≼ q.y2)
    (hL : L ∈ (((q.x1 ⊗ q.y2) ⊕ (q.x2 ⊗ q.y1)).left)) :
    L ≺ ((q.x1 ⊗ q.y1) ⊕ (q.x2 ⊗ q.y2)) := by
  /-
  Planned proof:
  * split `hL` using `mem_add_left_iff`;
  * then split the resulting product-option membership using `mem_mul_left`;
  * each of the resulting cases is handled by one of the Step (2) lemmas
    (`step2_xLx_*`, `step2_xxR_*`, `step2_yLy_*`, `step2_yyR_*`),
    together with the induction hypothesis on smaller quadruples.
  -/
  sorry

/-- The left side of `P(q)` is `<` every right option of the right side. -/
private lemma mulCross_lt_right_option_of_smaller {q : QuadGame} {R : Game}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≼ q.x2) (hy : q.y1 ≼ q.y2)
    (hR : R ∈ (((q.x1 ⊗ q.y1) ⊕ (q.x2 ⊗ q.y2)).right)) :
    ((q.x1 ⊗ q.y2) ⊕ (q.x2 ⊗ q.y1)) ≺ R := by
  /-
  Planned proof:
  * split `hR` using `mem_add_right_iff`;
  * then split the resulting product-option membership using `mem_mul_right`;
  * each case reduces to one of the anchored Step (2) lemmas,
    again using the induction hypothesis on smaller quadruples.
  -/
  sorry

private lemma quad_result_weak_of_smaller {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≼ q.x2) (hy : q.y1 ≼ q.y2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  /-
  Planned proof:
  unfold `MulCrossLe`, rewrite with `Game.le`,
  then use the two option lemmas above.
  -/
  sorry

private lemma quad_result_strict_of_smaller {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 →
        IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≺ q.x2) (hy : q.y1 ≺ q.y2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  /-
  Planned proof:
  either prove this directly by the same option analysis,
  or derive it from the weak result plus strictness witnesses.
  -/
  sorry

private theorem quad_result_of_A
    (hA : StageA n) :
    ∀ q : QuadGame,
      IsSurreal q.x1 → IsSurreal q.x2 →
      IsSurreal q.y1 → IsSurreal q.y2 →
      CrossRanksLT n q.x1 q.x2 q.y1 q.y2 →
      QuadResult q := by
  intro q
  refine wf_Q.induction
    (C := fun q : QuadGame =>
      IsSurreal q.x1 → IsSurreal q.x2 →
      IsSurreal q.y1 → IsSurreal q.y2 →
      CrossRanksLT n q.x1 q.x2 q.y1 q.y2 →
      QuadResult q) q ?_
  intro q IH hx1 hx2 hy1 hy2 hRanks
  refine ⟨?_, ?_⟩
  · intro hleX hleY
    exact quad_result_weak_of_smaller hA IH hx1 hx2 hy1 hy2 hRanks hleX hleY
  · intro hltX hltY
    exact quad_result_strict_of_smaller hA IH hx1 hx2 hy1 hy2 hRanks hltX hltY

theorem stageB_of_prev (hA : StageA n) : StageB n := by
  refine ⟨?_, ?_⟩
  · intro x1 x2 y1 y2 hx1 hx2 hy1 hy2 hRanks hleX hleY
    let q : QuadGame := ⟨x1, x2, y1, y2⟩
    exact (quad_result_of_A (n := n) hA q hx1 hx2 hy1 hy2 hRanks).weak hleX hleY
  · intro x1 x2 y1 y2 hx1 hx2 hy1 hy2 hRanks hltX hltY
    let q : QuadGame := ⟨x1, x2, y1, y2⟩
    exact (quad_result_of_A (n := n) hA q hx1 hx2 hy1 hy2 hRanks).strict hltX hltY


end StageBStep

/-! ## Main stage induction -/

theorem mul_stage (n : Nat) : StageA n ∧ StageB n := by
  refine Nat.strong_induction_on n ?_
  intro n IH
  have hA : StageA n := stageA_of_prev (n := n) (fun m hm => IH m hm)
  have hB : StageB n := stageB_of_prev (n := n) hA
  exact ⟨hA, hB⟩

/-! ## Final extracted theorems -/

theorem mul_isSurreal {x y : Game}
    (hx : IsSurreal x) (hy : IsSurreal y) :
    IsSurreal (x ⊗ y) := by
  let n := prodRank x y + 1
  have hA : StageA n := (mul_stage n).1
  have hxy : prodRank x y < n := by
    dsimp [n]
    exact Nat.lt_succ_self _
  exact hA.surreal hx hy hxy

theorem mul_congr_left
    {x1 x2 y : Game}
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  let n := max (prodRank x1 y) (prodRank x2 y) + 1
  have hA : StageA n := (mul_stage n).1
  have h1 : prodRank x1 y < n := by
    dsimp [n]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have h2 : prodRank x2 y < n := by
    dsimp [n]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact hA.congr_left hx1 hx2 hy hEq h1 h2

theorem mul_congr_right
    {x y1 y2 : Game}
    (hx : IsSurreal x) (hy1 : IsSurreal y1) (hy2 : IsSurreal y2)
    (hEq : y1 ∼ y2) :
    (x ⊗ y1) ∼ (x ⊗ y2) := by
  let n := max (prodRank x y1) (prodRank x y2) + 1
  have hA : StageA n := (mul_stage n).1
  have h1 : prodRank x y1 < n := by
    dsimp [n]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have h2 : prodRank x y2 < n := by
    dsimp [n]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact hA.congr_right hx hy1 hy2 hEq h1 h2

end Game

namespace Surreal

open scoped Game

/-- Product of surreal numbers: outline endpoint after `Game.mul_isSurreal`. -/
def mul (a b : Surreal) : Surreal :=
  ⟨Game.mul a.val b.val, Game.mul_isSurreal a.property b.property⟩

/-- Well-definedness on surreal numbers, left factor. -/
theorem mul_congr_left
    {x1 x2 y : Surreal}
    (hEq : (x1 : Game) ∼ (x2 : Game)) :
    (Game.mul (x1 : Game) (y : Game)) ∼ (Game.mul (x2 : Game) (y : Game)) := by
  exact Game.mul_congr_left x1.property x2.property y.property hEq

/-- Well-definedness on surreal numbers, right factor. -/
theorem mul_congr_right
    {x y1 y2 : Surreal}
    (hEq : (y1 : Game) ∼ (y2 : Game)) :
    (Game.mul (x : Game) (y1 : Game)) ∼ (Game.mul (x : Game) (y2 : Game)) := by
  exact Game.mul_congr_right x.property y1.property y2.property hEq

end Surreal
