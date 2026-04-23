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
  exact
    Game.eq_trans
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
variable (hprev : ∀ m < n, StageData m)

/-!
The next four lemmas are the heart of statement (i):
use the `P`-inequalities from earlier stages to show that every left option
of `x ⊗ y` is `<` every right option of `x ⊗ y`.
-/

theorem add_lt_left_left {u v : Game} (t : Game) : u ≺ v → (t ⊕ u) ≺ (t ⊕ v) := by
  intro huv
  exact Game.add_le_lt ⟨Game.le_congr, huv⟩

theorem Game.add_lt_right_right {u v : Game} (t : Game) : u ≺ v → (u ⊕ t) ≺ (v ⊕ t) := by
  sorry

theorem Game.add_lt_left_right {u v : Game} (t : Game) : u ≺ v → (t ⊕ u) ≺ (v ⊕ t) := by
  sorry

theorem Game.add_lt_right_left {u v : Game} (t : Game) : u ≺ v → (u ⊕ t) ≺ (t ⊕ v) := by
  sorry

private lemma surreal_left_option
    {x L : Game}
    (hx : IsSurreal x) (hL : L ∈ x.left) :
    IsSurreal L := by
  unfold IsSurreal at hx
  exact hx.2.1 _ hL

private lemma surreal_right_option {x R : Game}
    (hx : IsSurreal x) (hR : R ∈ x.right) : IsSurreal R := by
  unfold IsSurreal at hx
  exact hx.2.2 _ hR

private lemma mulOpt4_LL_of_cross {a b c d e : Game}
    (h : MulCrossLt a c d e) :
    Game.mulOpt4 a b c d ≺ Game.mulOpt4 a b c e := by
  unfold MulCrossLt at h
  sorry

private lemma mul_left_right_case_LL {x y xL xR yL yR : Game}
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
  exact mulOpt4_LL_of_cross hcross

private lemma mul_left_right_case_LR {x y xL xR yL yR : Game}
    (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xL y x yL ≺ Game.mulOpt4 xR y x yL := by
  sorry

private lemma mul_left_right_case_R {x y xL xR yL yR : Game}
    (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xR y x yR ≺ Game.mulOpt4 xL y x yR := by
  sorry

private lemma mul_left_right_case_RR {x y xL xR yL yR : Game}
    (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hxR : xR ∈ x.right)
    (hyL : yL ∈ y.left) (hyR : yR ∈ y.right)
    (hxy : prodRank x y < n) :
    Game.mulOpt4 xR y x yR ≺ Game.mulOpt4 xR y x yL := by
  sorry

private lemma mul_left_lt_right_of_prevB {x y L R : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hL : L ∈ (x ⊗ y).left) (hR : R ∈ (x ⊗ y).right) :
    ¬ (R ≼ L) := by
  sorry

/-!
Next: recursive surreality of the options of `x ⊗ y`.
Each option is a sum/negative of smaller products, so this uses only
earlier instances of `StageA`.
-/

private lemma mul_left_option_isSurreal_of_prevA {x y L : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hL : L ∈ (x ⊗ y).left) :
    IsSurreal L := by
  sorry

private lemma mul_right_option_isSurreal_of_prevA {x y R : Game}
    (hprev : ∀ m < n, StageData m) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxy : prodRank x y < n) (hR : R ∈ (x ⊗ y).right) :
    IsSurreal R := by
  sorry

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

private lemma left_option_mul_congr_of_prev {x1 x2 y L : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hL : L ∈ (x1 ⊗ y).left) :
    ∃ L' ∈ (x2 ⊗ y).left, L ∼ L' := by
  sorry

private lemma left_option_mul_congr_symm_of_prev {x1 x2 y L : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hL : L ∈ (x2 ⊗ y).left) :
    ∃ L' ∈ (x1 ⊗ y).left, L ∼ L' := by
  sorry

private lemma right_option_mul_congr_of_prev {x1 x2 y R : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hR : R ∈ (x1 ⊗ y).right) :
    ∃ R' ∈ (x2 ⊗ y).right, R ∼ R' := by
  sorry

private lemma right_option_mul_congr_symm_of_prev {x1 x2 y R : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n)
    (hR : R ∈ (x2 ⊗ y).right) :
    ∃ R' ∈ (x1 ⊗ y).right, R ∼ R' := by
  sorry

private theorem stageA_congr_left_of_prev {x1 x2 y : Game}
    (hprev : ∀ m < n, StageData m)
    (hx1 : IsSurreal x1) (hx2 : IsSurreal x2) (hy : IsSurreal y)
    (hEq : x1 ∼ x2) (h1 : prodRank x1 y < n) (h2 : prodRank x2 y < n) :
    (x1 ⊗ y) ∼ (x2 ⊗ y) := by
  refine Game.eq_of_equiv_options
    (fun L hL => left_option_mul_congr_of_prev hprev hx1 hx2 hy hEq h1 h2 hL)
    (fun L hL => left_option_mul_congr_symm_of_prev hprev hx1 hx2 hy hEq h1 h2 hL)
    (fun R hR => right_option_mul_congr_of_prev hprev hx1 hx2 hy hEq h1 h2 hR)
    (fun R hR => right_option_mul_congr_symm_of_prev hprev hx1 hx2 hy hEq h1 h2 hR)

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

private lemma base_P_LL {x y xL yL : Game}
    (hA : StageA n) (hx : IsSurreal x) (hy : IsSurreal y)
    (hxL : xL ∈ x.left) (hyL : yL ∈ y.left) (hxy : prodRank x y < n) :
    MulCrossLt xL x yL y := by
  sorry

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

/-!
Recursive reductions for the inner induction.
These are the “Conway reductions” from a general `P(x1,x2:y1,y2)`
to smaller quadruples.
-/

private lemma quad_result_weak_of_smaller {q : QuadGame}
    (hA : StageA n)
    (IH : ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 → IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 → QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≼ q.x2) (hy : q.y1 ≼ q.y2) :
    MulCrossLe q.x1 q.x2 q.y1 q.y2 := by
  sorry

private lemma quad_result_strict_of_smaller {q : QuadGame}
    (hA : StageA n)
    (IH :
      ∀ q', Q q' q →
        IsSurreal q'.x1 → IsSurreal q'.x2 → IsSurreal q'.y1 → IsSurreal q'.y2 →
        CrossRanksLT n q'.x1 q'.x2 q'.y1 q'.y2 →
        QuadResult q')
    (hx1 : IsSurreal q.x1) (hx2 : IsSurreal q.x2)
    (hy1 : IsSurreal q.y1) (hy2 : IsSurreal q.y2)
    (hRanks : CrossRanksLT n q.x1 q.x2 q.y1 q.y2)
    (hx : q.x1 ≺ q.x2) (hy : q.y1 ≺ q.y2) :
    MulCrossLt q.x1 q.x2 q.y1 q.y2 := by
  sorry

private theorem quad_result_of_A
    (hA : StageA n) :
    ∀ q : QuadGame,
      IsSurreal q.x1 → IsSurreal q.x2 → IsSurreal q.y1 → IsSurreal q.y2 →
      CrossRanksLT n q.x1 q.x2 q.y1 q.y2 →
      QuadResult q := by
  intro q
  refine wf_Q.induction
    (C := fun q : QuadGame =>
      IsSurreal q.x1 → IsSurreal q.x2 → IsSurreal q.y1 → IsSurreal q.y2 →
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
