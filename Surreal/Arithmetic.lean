import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal

-- We wish to define addition on surreal numbers. But first we need
-- to define addition on games.
def Game.add : Game → Game → Game
  | x, y =>
    let L := (x.left.map (fun xl => Game.add xl y)) ++ (y.left.map (fun yl => Game.add x yl))
    let R := (x.right.map (fun xr => Game.add xr y)) ++ (y.right.map (fun yr => Game.add x yr))
    Game.mk L R
  termination_by x y => x.birthday + y.birthday
  decreasing_by
    · sorry
    · sorry
    · sorry
    · sorry

theorem Game.add_zero (a : Game) : Game.add a zero = a := by
  sorry

theorem Game.zero_add (a : Game) : Game.add zero a = a := by
  sorry


-- These two lemmas must be proved hand-in-hand by induction on
-- birthday(a) + birthday(b) + birthday(a') + birthday(b').
theorem Game.AddThm1 (a b a' b' : Game) :
  (a.le a) ∧ (b.le b) → (Game.add a b).le (Game.add a' b') := by
  sorry

theorem Game.AddThm2  (a b a' b' : Game) :
  (Game.add a' b').le (Game.add a b) ∧ (b.le b') → (a'.le a) := by
  sorry


theorem Game.add_equal (a b a' b' : Game) :
  (a.eq a') ∧ (b.eq b') → (Game.add a b).eq (Game.add a' b') := by
  sorry

theorem Game.add_lt (a b a' b' : Game) :
  (a.lt a') ∧ (b.le b') → (Game.add a b).lt (Game.add a' b') := by
  sorry

-- addition is commutative: check whether one needs a, b to be surreal
theorem Game.add_comm (a b : Game) :
  Game.add a b = Game.add b a := by
  sorry

theorem Game.add_assoc (a b c : Game) :
  Game.add (Game.add a b) c = Game.add a (Game.add b c) := by
  sorry

def Game.neg : Game → Game
  | g =>
    let L := g.right.map (fun r => Game.neg r)
    let R := g.left.map (fun l => Game.neg l)
    Game.mk L R
  termination_by g => g.birthday
  decreasing_by
    · sorry
    · sorry

theorem Game.add_neg (a : Game) :
  (Game.add a (Game.neg a)).eq zero := by
  sorry

theorem Game.neg_add (a : Game) :
  (Game.add (Game.neg a) a).eq zero := by
  sorry

theorem Game.neg_isSurreal (a : Surreal) :
  IsSurreal (Game.neg a) := by
  sorry

theorem Game.add_isSurreal (a b : Surreal) :
  IsSurreal (Game.add a b) := by
  sorry
