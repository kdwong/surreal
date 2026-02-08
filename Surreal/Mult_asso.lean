import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition
import Surreal.mult_comm_dist



-------------------------------------------
----------- (a*b)*c = a*(b*c) -------------
-------------------------------------------

-- The proof shall be quite involved.
theorem Game.mul_assoc_tri (x : TriGame) :
  (Game.mul (Game.mul x.a x.b) x.c).eq (Game.mul x.a (Game.mul x.b x.c)) := by
  sorry

theorem Game.mul_assoc {a b c : Game} :
  (Game.mul (Game.mul a b) c).eq (Game.mul a (Game.mul b c)) := by
  let tri : TriGame := {a:=a , b:= b , c:=c}
  exact Game.mul_assoc_tri tri



-------------------------------------------
------ (a = c and b = d) → a*b = c*d ------
-------------------------------------------

lemma Game.mul_eq_zero_of {a b : Game} : a.eq zero → (a.mul b).eq zero := by
  sorry

lemma neg_mul_right (b c : Game) : ((Game.neg b).mul c).eq (Game.neg (b.mul c)) := by
  have hz : ((b.add (Game.neg b)).mul c).eq zero :=
    Game.mul_eq_zero_of (a := b.add (Game.neg b)) (b := c) (Game.add_neg b)
  have hdist :
      ((b.add (Game.neg b)).mul c).eq ((b.mul c).add ((Game.neg b).mul c)) :=
    Game.mul_distrib_right (a := b) (b := Game.neg b) (c := c)
  have hsum : ((b.mul c).add ((Game.neg b).mul c)).eq zero :=
    Game.eq_trans ⟨⟨hdist.2, hdist.1⟩, hz⟩
  have hq : (Game.q ((b.mul c).add ((Game.neg b).mul c)) : Game.GameQ) = Game.q zero := by
    refine Quotient.sound (a := ((b.mul c).add ((Game.neg b).mul c))) (b := zero) ?_
    simpa [Setoid.r] using hsum
  have hq' : (Game.q (b.mul c) : Game.GameQ) + (Game.q ((Game.neg b).mul c) : Game.GameQ) = 0 := by
    simpa [q_add] using hq
  have hq'' : (Game.q ((Game.neg b).mul c) : Game.GameQ) + (Game.q (b.mul c) : Game.GameQ) = 0 := by
    simpa [add_comm] using hq'
  have hsol :
      (Game.q ((Game.neg b).mul c) : Game.GameQ) = - (Game.q (b.mul c) : Game.GameQ) :=
    eq_neg_of_add_eq_zero_left hq''
  apply Game.eq_of_q_eq
  calc
    (Game.q ((Game.neg b).mul c) : Game.GameQ)
        = - (Game.q (b.mul c) : Game.GameQ) := hsol
    _   = Game.q (Game.neg (b.mul c)) := by simp

theorem mul_equal_three {a b c : Game} : (a.eq b) → (a.mul c).eq (b.mul c) := by
  intro hab
  have hneg_refl : (Game.neg b).eq (Game.neg b) := ⟨Game.le_congr, Game.le_congr⟩
  have hadd : (a.add (Game.neg b)).eq (b.add (Game.neg b)) :=
    Game.add_equal ⟨hab, hneg_refl⟩
  have hdiff0 : (a.add (Game.neg b)).eq zero :=
    Game.eq_trans ⟨hadd, Game.add_neg b⟩
  have hz : ((a.add (Game.neg b)).mul c).eq zero :=
    Game.mul_eq_zero_of (a := a.add (Game.neg b)) (b := c) hdiff0
  have hdist :
      ((a.add (Game.neg b)).mul c).eq
        ((a.mul c).add ((Game.neg b).mul c)) :=
    Game.mul_distrib_right (a := a) (b := Game.neg b) (c := c)
  have hsum : ((a.mul c).add ((Game.neg b).mul c)).eq zero :=
    Game.eq_trans ⟨⟨hdist.2, hdist.1⟩, hz⟩
  have hnegmul : ((Game.neg b).mul c).eq (Game.neg (b.mul c)) := by
    -- helper: turn `Game.eq` into equality in the quotient
    have q_eq_of_eq {u v : Game} (h : u.eq v) : (Game.q u : Game.GameQ) = Game.q v := by
      refine Quotient.sound ?_
      change Game.eq u v
      exact h

    -- (b + -b) * c = 0
    have hz0 : ((b.add (Game.neg b)).mul c).eq zero :=
      Game.mul_eq_zero_of (a := b.add (Game.neg b)) (b := c) (Game.add_neg b)

    -- distribute on the right: (b + -b) * c = b*c + (-b)*c
    have hdist0 :
        ((b.add (Game.neg b)).mul c).eq ((b.mul c).add ((Game.neg b).mul c)) :=
      Game.mul_distrib_right (a := b) (b := Game.neg b) (c := c)

    have hsum0 : ((b.mul c).add ((Game.neg b).mul c)).eq zero :=
      Game.eq_trans ⟨⟨hdist0.2, hdist0.1⟩, hz0⟩

    -- move to GameQ: q(b*c) + q((-b)*c) = 0
    have hqsum0 : (Game.q ((b.mul c).add ((Game.neg b).mul c)) : Game.GameQ) = 0 := by
      simpa [q_zero] using (q_eq_of_eq (u := (b.mul c).add ((Game.neg b).mul c)) (v := zero) hsum0)

    have hq0 :
        (Game.q (b.mul c) : Game.GameQ) + (Game.q ((Game.neg b).mul c) : Game.GameQ) = 0 := by
      simpa [q_add] using hqsum0

    -- solve for q((-b)*c) = - q(b*c)
    have hq_comm :
        (Game.q ((Game.neg b).mul c) : Game.GameQ) + (Game.q (b.mul c) : Game.GameQ) = 0 := by
      simpa [add_comm] using hq0

    have hsolve :
        (Game.q ((Game.neg b).mul c) : Game.GameQ) = - (Game.q (b.mul c) : Game.GameQ) :=
      eq_neg_of_add_eq_zero_left hq_comm

    -- pull back to `Game.eq`
    apply Game.eq_of_q_eq
    calc
      (Game.q ((Game.neg b).mul c) : Game.GameQ)
          = - (Game.q (b.mul c) : Game.GameQ) := hsolve
      _   = Game.q (Game.neg (b.mul c)) := by simp

  have hsum' : ((a.mul c).add (Game.neg (b.mul c))).eq zero := by
    have hrepl :
        ((a.mul c).add ((Game.neg b).mul c)).eq
          ((a.mul c).add (Game.neg (b.mul c))) :=
      Game.add_equal ⟨⟨Game.le_congr, Game.le_congr⟩, hnegmul⟩
    exact Game.eq_trans ⟨⟨hrepl.2, hrepl.1⟩, hsum⟩

  -- cancel in the quotient group: q(a*c) + (-q(b*c)) = 0  ⇒  q(a*c)=q(b*c)
  have hq :
      (Game.q ((a.mul c).add (Game.neg (b.mul c))) : Game.GameQ) = 0 := by
        refine Quotient.sound (a := ((a.mul c).add (Game.neg (b.mul c)))) (b := zero) ?_
        simpa [Setoid.r] using hsum'

  have hq' :
      (Game.q (a.mul c) : Game.GameQ) + (- (Game.q (b.mul c) : Game.GameQ)) = 0 := by
    simpa [q_add, q_neg] using hq

  have htmp := congrArg (fun t : Game.GameQ => t + (Game.q (b.mul c) : Game.GameQ)) hq'
  have hqeq : (Game.q (a.mul c) : Game.GameQ) = Game.q (b.mul c) := by
    simpa [add_assoc] using htmp

  exact Game.eq_of_q_eq hqeq



theorem Game.mul_equal {a b c d : Game} : (a.eq c) ∧ (b.eq d) → (a.mul b).eq (c.mul d) := by
  intro h
  rcases h with ⟨hac, hbd⟩
  have h1 : (a.mul b).eq (c.mul b) :=
    mul_equal_three (a := a) (b := c) (c := b) hac
  have hcb : (c.mul b).eq (b.mul c) := by
    simpa using (Game.mul_comm (a := c) (b := b))
  have hbc_to_dc : (b.mul c).eq (d.mul c) :=
    mul_equal_three (a := b) (b := d) (c := c) hbd
  have hdc : (d.mul c).eq (c.mul d) := by
    simpa using (Game.mul_comm (a := d) (b := c))
  have h2 : (c.mul b).eq (c.mul d) := by
    refine Game.eq_trans ⟨hcb, ?_⟩
    exact Game.eq_trans ⟨hbc_to_dc, hdc⟩
  exact Game.eq_trans ⟨h1, h2⟩




-------------------------------------------
----- a, b IsSurreal → a*b IsSurreal ------
-------------------------------------------
theorem Surreal.mul_isSurreal {a b : Surreal} : IsSurreal (Game.mul a.val b.val) := by
  sorry


def Surreal.mul (a b : Surreal) :
  Surreal := ⟨(a.val).mul b.val, Surreal.mul_isSurreal⟩
