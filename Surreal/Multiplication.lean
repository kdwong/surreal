import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal
import Surreal.addition

-------------------------------------------
---------- Definition of a*b --------------
-------------------------------------------

-- define flatten to simplify list
def flatten {α : Type} : List (List α) → List α
  | [] => []
  | (x :: xs) => x ++ flatten xs


def Game.mul : Game → Game → Game
  | x, y =>
  match _hx : x, _hy : y with
  | mk XL XR, mk YL YR =>
    let L :=
      flatten (XL.attach.map (fun lx =>
        let xl := lx.val
        let _hxl := lx.property
        YL.attach.map (fun ly =>
          let yl := ly.val
          let _hyl := ly.property
          ((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg
        )
      )) ++
      flatten (XR.attach.map (fun rx =>
        let xr := rx.val
        let _hxr := rx.property
        YR.attach.map (fun ry =>
          let yr := ry.val
          let _hyr := ry.property
          ((xr.mul y).add (x.mul yr)).add (xr.mul yr).neg
        )
      ))

    let R :=
      flatten (XL.attach.map (fun lx =>
        let xl := lx.val
        let _hxl := lx.property
        YR.attach.map (fun ry =>
          let yr := ry.val
          let _hyr := ry.property
          ((xl.mul y).add (x.mul yr)).add (xl.mul yr).neg
        )
      )) ++
      flatten (XR.attach.map (fun rx =>
        let xr := rx.val
        let _hxr := rx.property
        YL.attach.map (fun ly =>
          let yl := ly.val
          let _hyl := ly.property
          ((xr.mul y).add (x.mul yl)).add (xr.mul yl).neg
        )
      ))
    Game.mk L R
  termination_by x y => Game.birthday x + Game.birthday y
  decreasing_by
  -- 1. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 2. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 3. xl * yl
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : xl.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyl_lt
    assumption

  -- 4. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 5. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 6. xr * yr
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : xr.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyr_lt
    assumption

  -- 7. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 8. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 9. xl * yr
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : xl.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyr_lt
    assumption

  -- 10. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 11. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 12. xr * yl
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : xr.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyl_lt
    assumption

-------------------------------------------
--------------- a*0 = 0 -------------------
-------------------------------------------



-- flatten (List.replicate n []) = []
lemma flatten_replicate_nil {α} (n : Nat) : flatten (List.replicate n ([] : List α)) = [] := by
  induction n with
  | zero =>
    -- replicate 0 [] 是 []
    simp [List.replicate, flatten]
  | succ n ih =>
    -- replicate (n+1) [] 是 [] :: replicate n []
    -- flatten ([] :: xs) 是 [] ++ flatten xs
    simp [List.replicate, flatten, ih]

theorem Game.mul_zero (a : Game) : Game.mul a zero = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    -- simplify to List.replicate
    simp
    simp [flatten_replicate_nil]

theorem Game.zero_mul (a : Game) : Game.mul zero a = zero := by
    -- well-ordered Induction
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    -- simplify to List.replicate
    simp
    rfl



-------------------------------------------
--------------- a*b = b*a -----------------
-------------------------------------------
theorem Game.mul_comm (a b : Game) : Game.mul a b = Game.mul b a := by
  sorry


-------------------------------------------
------ (a = c and b = d) → a*b = c*d ------
-------------------------------------------
theorem Game.mul_equal (a b c d : Game) :
(a.eq c) ∧ (b.eq d) → (a.mul b).eq (c.mul d) := by
  sorry


-------------------------------------------
----- a, b IsSurreal → a*b IsSurreal ------
-------------------------------------------
theorem Surreal.mul_isSurreal (a b : Surreal) : IsSurreal (Game.mul a.val b.val) := by
  sorry


def Surreal.mul (a b : Surreal) :
  Surreal := ⟨(a.val).mul b.val, Surreal.mul_isSurreal a b⟩

-------------------------------------------
--------------- a*1 = 1 -------------------
-------------------------------------------

theorem Game.neg_zero : zero.neg = zero := by
  rw [Game.neg]
  simp [zero]
  unfold Game.right Game.left
  simp

-- Related lemma for mul_one
lemma flatten_map_singleton {α β} (l : List α) (f : α → β) :
  flatten (l.map (fun x => [f x])) = l.map f := by
  induction l with
  | nil => simp [flatten]
  | cons h t ih => simp [flatten, ih]

theorem Game.mul_one (a : Game) : Game.mul a one = a := by
  apply wf_R.induction a
  intro x IH
  unfold R at IH
  rw [one]
  unfold mul
  match hx : x with
  | mk XL XR =>
    -- turn flatten (List.replicate ... []) to [] and use [] ++ L = L
    simp [flatten_replicate_nil]
    simp [zero]

    -- put flatten (map [...]) back to map
    rw [flatten_map_singleton]
    rw [flatten_map_singleton]

    constructor
    · rw [map_id_iff,← zero, ← one, ← hx]
      intro lx lx_
      simp [Game.mul_zero, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_left (mk XL XR) lx lx_

    · rw [map_id_iff,← zero, ← one, ← hx]
      intro rx rx_
      simp [Game.mul_zero, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_right (mk XL XR) rx rx_

-- Perhaps one can use commutativity of multiplication below to get this?
theorem Game.one_mul (a : Game) : Game.mul one a = a := by
  rw [Game.mul_comm]
  rw [Game.mul_one]


-------------------------------------------
----------- (a*b)*c = a*(b*c) -------------
-------------------------------------------

-- The proof shall be quite involved. May need AI to help.
theorem Game.mul_assoc (a b c : Game) : Game.mul (Game.mul a b) c = Game.mul a (Game.mul b c) := by
  sorry


-------------------------------------------
---------- a*(b+c) = a*b + a*c ------------
-------------------------------------------
theorem Game.mul_distrib (a b c : Game) :
    Game.mul a (Game.add b c) = Game.add (Game.mul a b) (Game.mul a c) := by
  sorry
