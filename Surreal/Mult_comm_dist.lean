import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition

-------------------------------------------
---------- Definition of a*b --------------
-------------------------------------------
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
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 2. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 3. xl * yl
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : xl.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyl_lt
    assumption

  -- 4. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 5. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 6. xr * yr
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right  (by simpa [Game.right] using _hyr)
    have hmeasure : xr.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyr_lt
    assumption

  -- 7. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 8. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 9. xl * yr
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right  (by simpa [Game.right] using _hyr)
    have hmeasure : xl.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyr_lt
    assumption

  -- 10. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 11. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 12. xr * yl
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : xr.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyl_lt
    assumption

-------------------------------------------
--------------- a*0 = 0 -------------------
-------------------------------------------

lemma flatten_replicate_nil {α} (n : Nat) : flatten (List.replicate n ([] : List α)) = [] := by
  induction n with
  | zero =>
    simp [List.replicate, flatten]
  | succ n ih =>
    simp [List.replicate, flatten, ih]

lemma Game.mul_zero_eq (a : Game) : Game.mul a zero = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    simp [flatten_replicate_nil]

lemma Game.zero_mul_eq (a : Game) : Game.mul zero a = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    rfl

theorem Game.mul_zero (a : Game) : (Game.mul a zero).eq zero := by
  exact Game.eq_of_eq (Game.mul_zero_eq a)

theorem Game.zero_mul (a : Game) : (Game.mul zero a).eq zero := by
  exact Game.eq_of_eq (Game.zero_mul_eq a)

-------------------------------------------
--------------- a*b = b*a -----------------
-------------------------------------------
theorem mem_flatten_iff {α : Type} {x : α} {xss : List (List α)} :
    x ∈ flatten xss ↔ ∃ xs ∈ xss, x ∈ xs := by
  induction xss with
  | nil => simp [flatten]
  | cons h t ih => simp [flatten, List.mem_append, ih]


theorem mul_term_comm_aux (x y xl yl : Game)
  (IH_xyl : (x.mul yl).eq (yl.mul x))
  (IH_xly : (xl.mul y).eq (y.mul xl))
  (IH_xlyl : (xl.mul yl).eq (yl.mul xl)) :
  (((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg).eq
  (((yl.mul x).add (y.mul xl)).add (yl.mul xl).neg) := by
  apply Game.add_equal
  constructor
  · have h : ((xl.mul y).add (x.mul yl)).eq ((x.mul yl).add (xl.mul y)) := by
      exact Game.add_comm
    refine Game.eq_trans  ⟨h, ?_⟩
    apply Game.add_equal
    constructor
    · exact IH_xyl
    · exact IH_xly
  · apply (Game.neg_congr).mp
    apply Game.eq_refl
    exact IH_xlyl


lemma Game.bigame_mul_comm (x : BiGame) : ((x.a).mul x.b).eq ((x.b).mul x.a) := by
  apply wf_B.induction x
  intro x IH
  match ha : x.a, hb : x.b with
  | mk AL AR, mk BL BR =>
    apply Game.eq_of_equiv_options
    -- ==========================================================
    -- CASE 1: Left Options Forward (x * y).left ⊆ (y * x).left
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.left] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.left] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 1A: g from AL * BL
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨la, h_la, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨lb, h_lb, rfl⟩
        exists ((lb.val.mul x.a).add (x.b.mul la.val)).add (lb.val.mul la.val).neg
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        constructor
        · -- Show witness exists in (y * x).left
          rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (la' : {x // x ∈ AL}) =>
             ((lb.val.mul x.a).add (x.b.mul la'.val)).add (lb.val.mul la'.val).neg) AL.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_lb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_la
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_left h_b))
            exact IH_call
      }

      -- Subcase 1B: g from XR * YR
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨ra, h_ra, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨rb, h_rb, rfl⟩
        -- Witness: The corresponding term in (y * x).left (YR * XR)
        exists ((rb.val.mul x.a).add (x.b.mul ra.val)).add (rb.val.mul ra.val).neg
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        constructor
        · -- Show witness exists in (y * x).left (second part)
          rw [Game.mul, hb, ha]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (ra' : {x // x ∈ AR}) =>
             ((rb.val.mul x.a).add (x.b.mul ra'.val)).add (rb.val.mul ra'.val).neg) AR.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_rb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_ra
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_right h_b))
            exact IH_call
      }
    }
   -- ==========================================================
    -- CASE 2: Left Options Backward (y * x).left ⊆ (x * y).left
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.left] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.left] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 2A: g from YL * XL (matches Part 1 of Target)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨lb, h_lb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨la, h_la, rfl⟩
        exists ((la.val.mul x.b).add (x.a.mul lb.val)).add (la.val.mul lb.val).neg
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (lb' : {x // x ∈ BL}) =>
             ((la.val.mul x.b).add (x.a.mul lb'.val)).add (la.val.mul lb'.val).neg) BL.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_la
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_lb
        · apply Game.eq_refl
          dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_left h_b))
            exact IH_call
      }
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨rb, h_rb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨ra, h_ra, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((ra.val.mul x.b).add (x.a.mul rb.val)).add (ra.val.mul rb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (rb' : {x // x ∈ BR}) =>
             ((ra.val.mul x.b).add (x.a.mul rb'.val)).add (ra.val.mul rb'.val).neg) BR.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_ra
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_rb
        · apply Game.eq_refl
          dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_right h_b))
            exact IH_call
      }
    }

    -- ==========================================================
    -- CASE 3: Right Options Forward (x * y).right ⊆ (y * x).right
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.right] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.right] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 3A: g comes from (XL × YR)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨la, h_la, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨rb, h_rb, rfl⟩
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((rb.val.mul x.a).add (x.b.mul la.val)).add (rb.val.mul la.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (la' : {x // x ∈ AL}) =>
             ((rb.val.mul x.a).add (x.b.mul la'.val)).add (rb.val.mul la'.val).neg) AL.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_rb
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_la
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_right h_b))
            exact IH_call
      }

      -- Subcase 3B: g comes from (XR × YL)
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨ra, h_ra, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨lb, h_lb, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        exists ((lb.val.mul x.a).add (x.b.mul ra.val)).add (lb.val.mul ra.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (ra' : {x // x ∈ AR}) =>
             ((lb.val.mul x.a).add (x.b.mul ra'.val)).add (lb.val.mul ra'.val).neg) AR.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_lb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_ra
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_left h_b))
            exact IH_call
      }
    }
    -- ==========================================================
    -- CASE 4: Right Options Backward (y * x).right ⊆ (x * y).right
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.right] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.right] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right

      -- Subcase 4A: g from (YL * XR) -> Matches Part 2 of Target (XR * YL)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨lb, h_lb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨ra, h_ra, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        exists ((ra.val.mul x.b).add (x.a.mul lb.val)).add (ra.val.mul lb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (lb' : {x // x ∈ BL}) =>
             ((ra.val.mul x.b).add (x.a.mul lb'.val)).add (ra.val.mul lb'.val).neg) BL.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_ra
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_lb
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.b, b := ra}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := lb, b := x.a}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := lb, b := ra}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_b) (birthday_lt_right h_a))
            exact IH_call
      }
      -- Subcase 4B: g from (YR * XL) -> Matches Part 1 of Target (XL * YR)
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨rb, h_rb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨la, h_la, rfl⟩
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((la.val.mul x.b).add (x.a.mul rb.val)).add (la.val.mul rb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (rb' : {x // x ∈ BR}) =>
             ((la.val.mul x.b).add (x.a.mul rb'.val)).add (la.val.mul rb'.val).neg) BR.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_la
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_rb
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.b, b := la}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := rb, b := x.a}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := rb, b := la}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_b) (birthday_lt_left h_a))
            exact IH_call
      }
    }


theorem Game.mul_comm {a b : Game} : (a.mul b).eq (b.mul a) := by
  let bi : BiGame := {a := a, b := b}
  apply Game.bigame_mul_comm bi

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


-------------------------------------------
--------------- a*1 = 1 -------------------
-------------------------------------------
theorem Game.mul_one_eq {a : Game} : Game.mul a one = a := by
  apply wf_R.induction a
  intro x IH
  unfold R at IH
  rw [one]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp [flatten_replicate_nil]
    simp [zero]
    rw [flatten_map_singleton]
    rw [flatten_map_singleton]
    constructor
    · rw [map_id_iff,← zero, ← one, ← hx]
      intro lx lx_
      simp [Game.mul_zero_eq, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_left lx_

    · rw [map_id_iff,← zero, ← one, ← hx]
      intro rx rx_
      simp [Game.mul_zero_eq, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_right rx_


theorem Game.mul_one {a : Game} : (Game.mul a one).eq a := by
    unfold eq
    rw [Game.mul_one_eq]
    exact ⟨Game.le_congr, Game.le_congr⟩

theorem Game.one_mul {a : Game} : (Game.mul one a).eq a := by
  exact Game.eq_trans ⟨Game.mul_comm, Game.mul_one⟩

-------------------------------------------
---------- a*(b+c) = a*b + a*c ------------
-------------------------------------------
instance : Setoid Game where
  r a b := Game.eq a b
  iseqv := {
    refl  := fun _ => ⟨Game.le_congr, Game.le_congr⟩
    symm  := fun h => ⟨h.2, h.1⟩
    trans := fun h1 h2 =>
    ⟨Game.le_trans ⟨h1.1, h2.1⟩, Game.le_trans ⟨h2.2, h1.2⟩⟩}

abbrev Game.GameQ := Quotient (inferInstance : Setoid Game)

def Game.q : Game → GameQ := Quotient.mk _

instance : Zero Game.GameQ := ⟨Game.q zero⟩

instance : Add Game.GameQ :=
  ⟨Quotient.map₂ Game.add (by
      intro a a' ha b b' hb
      exact Game.add_equal ⟨ha, hb⟩)⟩

instance : Neg Game.GameQ :=
  ⟨Quotient.map Game.neg (by
      intro a b hab
      exact Game.neg_congr_left hab)⟩

@[simp] lemma q_zero : (Game.q zero : Game.GameQ) = 0 := rfl
@[simp] lemma q_add (a b : Game) : (Game.q (a.add b) : Game.GameQ) = (Game.q a + Game.q b) := rfl
@[simp] lemma q_neg (a : Game) : (Game.q (Game.neg a) : Game.GameQ) = (- Game.q a) := rfl

instance : AddCommGroup Game.GameQ where
  zero_add := by
    intro x
    refine Quotient.inductionOn x (fun a : Game => ?_)
    -- goal: (0 + q a) = q a
    change (Game.q (Game.add zero a) : Game.GameQ) = Game.q a
    apply Quotient.sound
    exact Game.eq_of_eq (Game.zero_add (a := a))
  add_zero := by
    intro x
    refine Quotient.inductionOn x (fun a : Game => ?_)
    change (Game.q (Game.add a zero) : Game.GameQ) = Game.q a
    apply Quotient.sound
    exact Game.eq_of_eq (Game.add_zero (a := a))

  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x (fun a : Game => ?_)
    refine Quotient.inductionOn y (fun b : Game => ?_)
    refine Quotient.inductionOn z (fun c : Game => ?_)
    change (Game.q (Game.add (Game.add a b) c) : Game.GameQ)
        = Game.q (Game.add a (Game.add b c))
    apply Quotient.sound
    exact Game.eq_of_eq (Game.add_assoc (a := a) (b := b) (c := c))

  add_comm := by
    intro x y
    refine Quotient.inductionOn x (fun a : Game => ?_)
    refine Quotient.inductionOn y (fun b : Game => ?_)
    change (Game.q (Game.add a b) : Game.GameQ) = Game.q (Game.add b a)
    apply Quotient.sound
    simpa using (Game.add_comm (a := a) (b := b))

 -- these two are required fields
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x (fun a : Game => ?_)
    change (Game.q (Game.add (Game.neg a) a) : Game.GameQ) = 0
    apply Quotient.sound
    simpa using (Game.neg_add a)



lemma Game.T_left {a a' b c : Game} (ha : birthday a' < birthday a) : T ⟨a', b, c⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_mid {a b b' c : Game} (hb : birthday b' < birthday b) : T ⟨a, b', c⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_right {a b c c' : Game} (hc : birthday c' < birthday c) : T ⟨a, b, c'⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_left_mid {a a' b b' c : Game}
    (ha : birthday a' < birthday a) (hb : birthday b' < birthday b) :
    T ⟨a', b', c⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_left_right {a a' b c c' : Game}
    (ha : birthday a' < birthday a) (hc : birthday c' < birthday c) : T ⟨a', b, c'⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_mid_right {a b b' c c' : Game}
    (hb : birthday b' < birthday b) (hc : birthday c' < birthday c) : T ⟨a, b', c'⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.T_left_mid_right {a a' b b' c c' : Game}
    (ha : birthday a' < birthday a) (hb : birthday b' < birthday b)
    (hc : birthday c' < birthday c) : T ⟨a', b', c'⟩ ⟨a, b, c⟩ := by
  simp [T]; linarith

lemma Game.eq_of_q_eq {u v : Game} (h : (q u : GameQ) = q v) : u.eq v :=
  Quotient.exact h


lemma mem_flatten_map_map_iff {α β γ : Type} (f : α → β → γ) (z : γ)
    (A : List α) (B : List β) :
    z ∈ flatten (A.map (fun a => B.map (fun b => f a b))) ↔
      ∃ a ∈ A, ∃ b ∈ B, z = f a b := by
  induction A with
  | nil =>
      simp [flatten]
  | cons a As ih =>
      constructor
      · intro hz
        -- one-step unfold of flatten/map and split membership
        simp [flatten, List.mem_append] at hz
        rcases hz with hz | hz
        · -- head block: simp has turned membership into an ∃ already
          rcases hz with ⟨b, hbB, hbEq⟩  -- hbEq : f a b = z
          refine ⟨a, by simp, b, hbB, ?_⟩
          exact hbEq.symm
        · -- tail block: use IH
          rcases (ih.1 hz) with ⟨a', ha', b, hbB, hzEq⟩
          refine ⟨a', ?_, b, hbB, hzEq⟩
          simp [ha']
      · intro hz
        rcases hz with ⟨a', ha', b, hbB, hzEq⟩
        -- split whether a' is head or in tail
        simp [List.mem_cons] at ha'
        rcases ha' with rfl | haTail
        · -- a' = a: show z is in head block
          simp [flatten, List.mem_append]
          left
          refine ⟨b, hbB, ?_⟩
          exact hzEq.symm  -- need f a b = z
        · -- a' in tail: use IH
          have : z ∈ flatten (As.map (fun a0 => B.map (fun b0 => f a0 b0))) :=
            (ih.2 ⟨a', haTail, b, hbB, hzEq⟩)
          simp [flatten, List.mem_append, this]

lemma mem_mul_left {x y z : Game} :
    z ∈ (x.mul y).left ↔
      (∃ xl ∈ x.left, ∃ yl ∈ y.left,
          z = (((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg)) ∨
      (∃ xr ∈ x.right, ∃ yr ∈ y.right,
          z = (((xr.mul y).add (x.mul yr)).add (xr.mul yr).neg)) := by
  cases x with
  | mk XL XR =>
    cases y with
    | mk YL YR =>
      simp [Game.mul, Game.left, Game.right, mem_flatten_map_map_iff]

lemma mem_mul_right {x y z : Game} :
    z ∈ (x.mul y).right ↔
      (∃ xl ∈ x.left, ∃ yr ∈ y.right,
          z = (((xl.mul y).add (x.mul yr)).add (xl.mul yr).neg)) ∨
      (∃ xr ∈ x.right, ∃ yl ∈ y.left,
          z = (((xr.mul y).add (x.mul yl)).add (xr.mul yl).neg)) := by
  cases x with
  | mk XL XR =>
    cases y with
    | mk YL YR =>
      simp [Game.mul, Game.left, Game.right, mem_flatten_map_map_iff]

def Game.mulOpt4 (xOpt Y X yOpt : Game) : Game :=
  (((xOpt.mul Y).add (X.mul yOpt)).add (xOpt.mul yOpt).neg)

lemma Game.mulOpt4_congr
    {xOpt Y X yOpt A B C : Game}
    (h1 : (xOpt.mul Y).eq A)
    (h2 : (X.mul yOpt).eq B)
    (h3 : (xOpt.mul yOpt).eq C) :
    (mulOpt4 xOpt Y X yOpt).eq ((A.add B).add C.neg) := by
  dsimp [mulOpt4]
  have hsum : ((xOpt.mul Y).add (X.mul yOpt)).eq (A.add B) :=
    Game.add_equal ⟨h1, h2⟩
  have hneg : (xOpt.mul yOpt).neg.eq C.neg :=
    Game.neg_congr_left h3
  exact Game.add_equal ⟨hsum, hneg⟩

theorem Game.mul_distrib_tri (x : TriGame) :
    (x.a.mul (x.b.add x.c)).eq ((x.a.mul x.b).add (x.a.mul x.c)) := by
  classical
  apply wf_T.induction x ?_
  intro x IH
  rcases x with ⟨a, b, c⟩
  let P : TriGame → Prop :=
    fun t => (t.a.mul (t.b.add t.c)).eq ((t.a.mul t.b).add (t.a.mul t.c))
  have IH3 (a' b' c' : Game) (hT : T ⟨a', b', c'⟩ ⟨a, b, c⟩) :
      (a'.mul (b'.add c')).eq ((a'.mul b').add (a'.mul c')) := by
    simpa [P] using IH ⟨a', b', c'⟩ hT
  have IHa (a' : Game) (ha : birthday a' < birthday a) :
      (a'.mul (b.add c)).eq ((a'.mul b).add (a'.mul c)) :=
    IH3 a' b c (Game.T_left (a := a) (b := b) (c := c) ha)
  have IHb (b' : Game) (hb : birthday b' < birthday b) :
      (a.mul (b'.add c)).eq ((a.mul b').add (a.mul c)) :=
    IH3 a b' c (Game.T_mid (a := a) (b := b) (c := c) hb)
  have IHc (c' : Game) (hc : birthday c' < birthday c) :
      (a.mul (b.add c')).eq ((a.mul b).add (a.mul c')) :=
    IH3 a b c' (Game.T_right (a := a) (b := b) (c := c) hc)
  have IHab (a' b' : Game) (ha : birthday a' < birthday a) (hb : birthday b' < birthday b) :
      (a'.mul (b'.add c)).eq ((a'.mul b').add (a'.mul c)) :=
    IH3 a' b' c (Game.T_left_mid (a := a) (b := b) (c := c) ha hb)
  have IHac (a' c' : Game) (ha : birthday a' < birthday a) (hc : birthday c' < birthday c) :
      (a'.mul (b.add c')).eq ((a'.mul b).add (a'.mul c')) :=
    IH3 a' b c' (Game.T_left_right (a := a) (b := b) (c := c) ha hc)
  have IHbc (b' c' : Game) (hb : birthday b' < birthday b) (hc : birthday c' < birthday c) :
      (a.mul (b'.add c')).eq ((a.mul b').add (a.mul c')) :=
    IH3 a b' c' (Game.T_mid_right (a := a) (b := b) (c := c) hb hc)

  apply Game.eq_of_equiv_options

  · -- (1) Left options forward
    intro L hL
    have hL' : L ∈ (a.mul (b.add c)).left := hL
    rw [mem_mul_left] at hL'
    rcases hL' with hLL | hRR

    · -- L from (aL ∈ a.left, yL ∈ (b+c).left)
      rcases hLL with ⟨aL, haL, yL, hyL, rfl⟩
      have ha : birthday aL < birthday a := Game.birthday_lt_left haL

      have hyL' : yL ∈ (b.add c).left := hyL
      rw [mem_add_left] at hyL'
      rcases hyL' with ⟨bL, hbL, rfl⟩ | ⟨cL, hcL, rfl⟩

      · -- yL = bL + c
        have hb : birthday bL < birthday b := Game.birthday_lt_left hbL
        refine ⟨(((aL.mul b).add (a.mul bL)).add (aL.mul bL).neg).add (a.mul c),?_, ?_⟩
        · have hopt :
              (((aL.mul b).add (a.mul bL)).add (aL.mul bL).neg) ∈ (a.mul b).left := by
            rw [mem_mul_left]
            exact Or.inl ⟨aL, haL, bL, hbL, rfl⟩
          rw [mem_add_left]
          exact Or.inl ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (bL.add c)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul bL).add (a.mul c))).add
                  (((aL.mul bL).add (aL.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := bL.add c)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul bL).add (a.mul c))
                (C := (aL.mul bL).add (aL.mul c))
                (IHa aL ha)
                (IHb bL hb)
                (IHab aL bL ha hb)
          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel
      · -- yL = b + cL
        have hc : birthday cL < birthday c := Game.birthday_lt_left hcL
        refine ⟨
          (a.mul b).add (((aL.mul c).add (a.mul cL)).add (aL.mul cL).neg),
          ?_, ?_⟩
        · have hopt :
              (((aL.mul c).add (a.mul cL)).add (aL.mul cL).neg) ∈ (a.mul c).left := by
            rw [mem_mul_left]
            exact Or.inl ⟨aL, haL, cL, hcL, rfl⟩
          rw [mem_add_left]
          exact Or.inr ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (b.add cL)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cL))).add
                  (((aL.mul b).add (aL.mul cL)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := b.add cL)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul b).add (a.mul cL))
                (C := (aL.mul b).add (aL.mul cL))
                (IHa aL ha)
                (IHc cL hc)
                (IHac aL cL ha hc)
          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel
    · -- L from (aR ∈ a.right, yR ∈ (b+c).right)
      rcases hRR with ⟨aR, haR, yR, hyR, rfl⟩
      have ha : birthday aR < birthday a := Game.birthday_lt_right haR

      have hyR' : yR ∈ (b.add c).right := hyR
      rw [mem_add_right] at hyR'
      rcases hyR' with ⟨bR, hbR, rfl⟩ | ⟨cR, hcR, rfl⟩
      · -- yR = bR + c
        have hb : birthday bR < birthday b := Game.birthday_lt_right hbR
        refine ⟨
          (((aR.mul b).add (a.mul bR)).add (aR.mul bR).neg).add (a.mul c),
          ?_, ?_⟩
        · have hopt :
              (((aR.mul b).add (a.mul bR)).add (aR.mul bR).neg) ∈ (a.mul b).left := by
            rw [mem_mul_left]
            exact Or.inr ⟨aR, haR, bR, hbR, rfl⟩
          rw [mem_add_left]
          exact Or.inl ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (bR.add c)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul bR).add (a.mul c))).add
                  (((aR.mul bR).add (aR.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := bR.add c)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul bR).add (a.mul c))
                (C := (aR.mul bR).add (aR.mul c))
                (IHa aR ha)
                (IHb bR hb)
                (IHab aR bR ha hb)
          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel
      · -- yR = b + cR
        have hc : birthday cR < birthday c := Game.birthday_lt_right hcR
        refine ⟨(a.mul b).add (((aR.mul c).add (a.mul cR)).add (aR.mul cR).neg),?_, ?_⟩
        · have hopt :
              (((aR.mul c).add (a.mul cR)).add (aR.mul cR).neg) ∈ (a.mul c).left := by
            rw [mem_mul_left]
            exact Or.inr ⟨aR, haR, cR, hcR, rfl⟩
          rw [mem_add_left]
          exact Or.inr ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (b.add cR)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cR))).add
                  (((aR.mul b).add (aR.mul cR)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := b.add cR)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul b).add (a.mul cR))
                (C := (aR.mul b).add (aR.mul cR))
                (IHa aR ha)
                (IHc cR hc)
                (IHac aR cR ha hc)
          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel
  · -- (2) Left options backward
    intro L hL
    have hL' : L ∈ ((a.mul b).add (a.mul c)).left := hL
    rw [mem_add_left] at hL'
    rcases hL' with ⟨abL, habL, rfl⟩ | ⟨acL, hacL, rfl⟩
    · -- Case A: L = abL + (a*c), with abL ∈ (a*b).left
      have habL' : abL ∈ (a.mul b).left := habL
      rw [mem_mul_left] at habL'
      rcases habL' with hLL | hRR
      · -- Subcase A1: abL from (aL ∈ a.left, bL ∈ b.left)
        rcases hLL with ⟨aL, haL, bL, hbL, rfl⟩
        have ha : birthday aL < birthday a := Game.birthday_lt_left haL
        have hb : birthday bL < birthday b := Game.birthday_lt_left hbL
        let yL : Game := bL.add c
        have hyL : yL ∈ (b.add c).left := by
          rw [mem_add_left]
          exact Or.inl ⟨bL, hbL, rfl⟩
        refine ⟨Game.mulOpt4 aL (b.add c) a yL, ?_, ?_⟩
        · rw [mem_mul_left]
          exact Or.inl ⟨aL, haL, yL, hyL, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (bL.add c)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul bL).add (a.mul c))).add
                  (((aL.mul bL).add (aL.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := bL.add c)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul bL).add (a.mul c))
                (C := (aL.mul bL).add (aL.mul c))
                (IHa aL ha)
                (IHb bL hb)
                (IHab aL bL ha hb)

          have h_alg :
              ((((aL.mul b).add (aL.mul c)).add ((a.mul bL).add (a.mul c))).add
                ((aL.mul bL).add (aL.mul c)).neg).eq
              ((((aL.mul b).add (a.mul bL)).add (aL.mul bL).neg).add (a.mul c)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aL (b.add c) a (bL.add c)).eq
                ((((aL.mul b).add (a.mul bL)).add (aL.mul bL).neg).add (a.mul c)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩

          exact Game.eq_refl hw

      · -- Subcase A2: abL from (aR ∈ a.right, bR ∈ b.right)
        rcases hRR with ⟨aR, haR, bR, hbR, rfl⟩
        have ha : birthday aR < birthday a := Game.birthday_lt_right haR
        have hb : birthday bR < birthday b := Game.birthday_lt_right hbR
        let yR : Game := bR.add c
        have hyR : yR ∈ (b.add c).right := by
          rw [mem_add_right]
          exact Or.inl ⟨bR, hbR, rfl⟩
        refine ⟨Game.mulOpt4 aR (b.add c) a yR, ?_, ?_⟩
        · rw [mem_mul_left]
          exact Or.inr ⟨aR, haR, yR, hyR, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (bR.add c)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul bR).add (a.mul c))).add
                  (((aR.mul bR).add (aR.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := bR.add c)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul bR).add (a.mul c))
                (C := (aR.mul bR).add (aR.mul c))
                (IHa aR ha)
                (IHb bR hb)
                (IHab aR bR ha hb)
          have h_alg :
              ((((aR.mul b).add (aR.mul c)).add ((a.mul bR).add (a.mul c))).add
                ((aR.mul bR).add (aR.mul c)).neg).eq
              ((((aR.mul b).add (a.mul bR)).add (aR.mul bR).neg).add (a.mul c)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel
          have hw :
              (Game.mulOpt4 aR (b.add c) a (bR.add c)).eq
                ((((aR.mul b).add (a.mul bR)).add (aR.mul bR).neg).add (a.mul c)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩

          exact Game.eq_refl hw

    · -- Case B: L = (a*b) + acL, with acL ∈ (a*c).left
      have hacL' : acL ∈ (a.mul c).left := hacL
      rw [mem_mul_left] at hacL'
      rcases hacL' with hLL | hRR
      · -- Subcase B1: acL from (aL ∈ a.left, cL ∈ c.left)
        rcases hLL with ⟨aL, haL, cL, hcL, rfl⟩
        have ha : birthday aL < birthday a := Game.birthday_lt_left haL
        have hc : birthday cL < birthday c := Game.birthday_lt_left hcL

        let yL : Game := b.add cL
        have hyL : yL ∈ (b.add c).left := by
          rw [mem_add_left]
          exact Or.inr ⟨cL, hcL, rfl⟩
        refine ⟨Game.mulOpt4 aL (b.add c) a yL, ?_, ?_⟩
        · rw [mem_mul_left]
          exact Or.inl ⟨aL, haL, yL, hyL, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (b.add cL)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cL))).add
                  (((aL.mul b).add (aL.mul cL)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := b.add cL)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul b).add (a.mul cL))
                (C := (aL.mul b).add (aL.mul cL))
                (IHa aL ha)
                (IHc cL hc)
                (IHac aL cL ha hc)

          have h_alg :
              ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cL))).add
                ((aL.mul b).add (aL.mul cL)).neg).eq
              ((a.mul b).add (((aL.mul c).add (a.mul cL)).add (aL.mul cL).neg)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aL (b.add c) a (b.add cL)).eq
                ((a.mul b).add (((aL.mul c).add (a.mul cL)).add (aL.mul cL).neg)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩
          exact Game.eq_refl hw

      · -- Subcase B2: acL from (aR ∈ a.right, cR ∈ c.right)
        rcases hRR with ⟨aR, haR, cR, hcR, rfl⟩
        have ha : birthday aR < birthday a := Game.birthday_lt_right haR
        have hc : birthday cR < birthday c := Game.birthday_lt_right hcR
        let yR : Game := b.add cR
        have hyR : yR ∈ (b.add c).right := by
          rw [mem_add_right]
          exact Or.inr ⟨cR, hcR, rfl⟩
        refine ⟨Game.mulOpt4 aR (b.add c) a yR, ?_, ?_⟩
        · rw [mem_mul_left]
          exact Or.inr ⟨aR, haR, yR, hyR, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (b.add cR)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cR))).add
                  (((aR.mul b).add (aR.mul cR)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := b.add cR)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul b).add (a.mul cR))
                (C := (aR.mul b).add (aR.mul cR))
                (IHa aR ha)
                (IHc cR hc)
                (IHac aR cR ha hc)

          have h_alg :
              ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cR))).add
                ((aR.mul b).add (aR.mul cR)).neg).eq
              ((a.mul b).add (((aR.mul c).add (a.mul cR)).add (aR.mul cR).neg)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aR (b.add c) a (b.add cR)).eq
                ((a.mul b).add (((aR.mul c).add (a.mul cR)).add (aR.mul cR).neg)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩

          exact Game.eq_refl hw

  · -- (3) Right options forward
    intro R hR
    have hR' : R ∈ (a.mul (b.add c)).right := hR
    rw [mem_mul_right] at hR'
    rcases hR' with hLR | hRL

    · -- Case 1: R from (aL ∈ a.left, yR ∈ (b+c).right)
      rcases hLR with ⟨aL, haL, yR, hyR, rfl⟩
      have ha : birthday aL < birthday a := Game.birthday_lt_left haL

      have hyR' : yR ∈ (b.add c).right := hyR
      rw [mem_add_right] at hyR'
      rcases hyR' with ⟨bR, hbR, rfl⟩ | ⟨cR, hcR, rfl⟩

      · -- Subcase 1.1: yR = bR + c
        have hb : birthday bR < birthday b := Game.birthday_lt_right hbR
        refine ⟨
          (((aL.mul b).add (a.mul bR)).add (aL.mul bR).neg).add (a.mul c),
          ?_, ?_⟩
        · have hopt :
              (((aL.mul b).add (a.mul bR)).add (aL.mul bR).neg) ∈ (a.mul b).right := by
            rw [mem_mul_right]
            exact Or.inl ⟨aL, haL, bR, hbR, rfl⟩
          rw [mem_add_right]
          exact Or.inl ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (bR.add c)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul bR).add (a.mul c))).add
                  (((aL.mul bR).add (aL.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := bR.add c)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul bR).add (a.mul c))
                (C := (aL.mul bR).add (aL.mul c))
                (IHa aL ha)
                (IHb bR hb)
                (IHab aL bR ha hb)

          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine Game.eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel

      · -- Subcase 1.2: yR = b + cR
        have hc : birthday cR < birthday c := Game.birthday_lt_right hcR
        refine ⟨
          (a.mul b).add (((aL.mul c).add (a.mul cR)).add (aL.mul cR).neg),
          ?_, ?_⟩
        · have hopt :
              (((aL.mul c).add (a.mul cR)).add (aL.mul cR).neg) ∈ (a.mul c).right := by
            rw [mem_mul_right]
            exact Or.inl ⟨aL, haL, cR, hcR, rfl⟩
          rw [mem_add_right]
          exact Or.inr ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (b.add cR)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cR))).add
                  (((aL.mul b).add (aL.mul cR)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := b.add cR)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul b).add (a.mul cR))
                (C := (aL.mul b).add (aL.mul cR))
                (IHa aL ha)
                (IHc cR hc)
                (IHac aL cR ha hc)
          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine Game.eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel

    · -- Case 2: R from (aR ∈ a.right, yL ∈ (b+c).left)
      rcases hRL with ⟨aR, haR, yL, hyL, rfl⟩
      have ha : birthday aR < birthday a := Game.birthday_lt_right haR

      have hyL' : yL ∈ (b.add c).left := hyL
      rw [mem_add_left] at hyL'
      rcases hyL' with ⟨bL, hbL, rfl⟩ | ⟨cL, hcL, rfl⟩

      · -- Subcase 2.1: yL = bL + c
        have hb : birthday bL < birthday b := Game.birthday_lt_left hbL
        refine ⟨
          (((aR.mul b).add (a.mul bL)).add (aR.mul bL).neg).add (a.mul c),
          ?_, ?_⟩
        · have hopt :
              (((aR.mul b).add (a.mul bL)).add (aR.mul bL).neg) ∈ (a.mul b).right := by
            rw [mem_mul_right]
            exact Or.inr ⟨aR, haR, bL, hbL, rfl⟩
          rw [mem_add_right]
          exact Or.inl ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (bL.add c)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul bL).add (a.mul c))).add
                  (((aR.mul bL).add (aR.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := bL.add c)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul bL).add (a.mul c))
                (C := (aR.mul bL).add (aR.mul c))
                (IHa aR ha)
                (IHb bL hb)
                (IHab aR bL ha hb)

          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine Game.eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel
      · -- Subcase 2.2: yL = b + cL
        have hc : birthday cL < birthday c := Game.birthday_lt_left hcL
        refine ⟨
          (a.mul b).add (((aR.mul c).add (a.mul cL)).add (aR.mul cL).neg),
          ?_, ?_⟩
        · have hopt :
              (((aR.mul c).add (a.mul cL)).add (aR.mul cL).neg) ∈ (a.mul c).right := by
            rw [mem_mul_right]
            exact Or.inr ⟨aR, haR, cL, hcL, rfl⟩
          rw [mem_add_right]
          exact Or.inr ⟨_, hopt, rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (b.add cL)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cL))).add
                  (((aR.mul b).add (aR.mul cL)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := b.add cL)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul b).add (a.mul cL))
                (C := (aR.mul b).add (aR.mul cL))
                (IHa aR ha)
                (IHc cL hc)
                (IHac aR cL ha hc)

          refine Game.eq_trans ⟨hrewrite, ?_⟩
          refine Game.eq_of_q_eq (u := _) (v := _) ?_
          · simp
            abel

  · -- (4) Right options backward
    intro R hR
    have hR' : R ∈ ((a.mul b).add (a.mul c)).right := hR
    rw [mem_add_right] at hR'
    rcases hR' with ⟨abR, habR, rfl⟩ | ⟨acR, hacR, rfl⟩

    · -- Case A: R = abR + (a*c), where abR ∈ (a*b).right
      have habR' : abR ∈ (a.mul b).right := habR
      rw [mem_mul_right] at habR'
      rcases habR' with hLR | hRL

      · -- Subcase A1: abR from (aL ∈ a.left, bR ∈ b.right)
        rcases hLR with ⟨aL, haL, bR, hbR, rfl⟩
        have ha : birthday aL < birthday a := Game.birthday_lt_left haL
        have hb : birthday bR < birthday b := Game.birthday_lt_right hbR

        let yR : Game := bR.add c
        have hyR : yR ∈ (b.add c).right := by
          rw [mem_add_right]
          exact Or.inl ⟨bR, hbR, rfl⟩

        refine ⟨Game.mulOpt4 aL (b.add c) a yR, ?_, ?_⟩
        · rw [mem_mul_right]
          exact Or.inl ⟨aL, haL, yR, hyR, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (bR.add c)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul bR).add (a.mul c))).add
                  (((aL.mul bR).add (aL.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := bR.add c)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul bR).add (a.mul c))
                (C := (aL.mul bR).add (aL.mul c))
                (IHa aL ha)
                (IHb bR hb)
                (IHab aL bR ha hb)

          have h_alg :
              ((((aL.mul b).add (aL.mul c)).add ((a.mul bR).add (a.mul c))).add
                ((aL.mul bR).add (aL.mul c)).neg).eq
              ((((aL.mul b).add (a.mul bR)).add (aL.mul bR).neg).add (a.mul c)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aL (b.add c) a (bR.add c)).eq
                ((((aL.mul b).add (a.mul bR)).add (aL.mul bR).neg).add (a.mul c)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩

          exact Game.eq_refl hw

      · -- Subcase A2: abR from (aR ∈ a.right, bL ∈ b.left)
        rcases hRL with ⟨aR, haR, bL, hbL, rfl⟩
        have ha : birthday aR < birthday a := Game.birthday_lt_right haR
        have hb : birthday bL < birthday b := Game.birthday_lt_left hbL
        let yL : Game := bL.add c
        have hyL : yL ∈ (b.add c).left := by
          rw [mem_add_left]
          exact Or.inl ⟨bL, hbL, rfl⟩
        refine ⟨Game.mulOpt4 aR (b.add c) a yL, ?_, ?_⟩
        · rw [mem_mul_right]
          exact Or.inr ⟨aR, haR, yL, hyL, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (bL.add c)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul bL).add (a.mul c))).add
                  (((aR.mul bL).add (aR.mul c)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := bL.add c)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul bL).add (a.mul c))
                (C := (aR.mul bL).add (aR.mul c))
                (IHa aR ha)
                (IHb bL hb)
                (IHab aR bL ha hb)

          have h_alg :
              ((((aR.mul b).add (aR.mul c)).add ((a.mul bL).add (a.mul c))).add
                ((aR.mul bL).add (aR.mul c)).neg).eq
              ((((aR.mul b).add (a.mul bL)).add (aR.mul bL).neg).add (a.mul c)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aR (b.add c) a (bL.add c)).eq
                ((((aR.mul b).add (a.mul bL)).add (aR.mul bL).neg).add (a.mul c)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩
          exact Game.eq_refl hw

    · -- Case B: R = (a*b) + acR, where acR ∈ (a*c).right
      have hacR' : acR ∈ (a.mul c).right := hacR
      rw [mem_mul_right] at hacR'
      rcases hacR' with hLR | hRL

      · -- Subcase B1: acR from (aL ∈ a.left, cR ∈ c.right)
        rcases hLR with ⟨aL, haL, cR, hcR, rfl⟩
        have ha : birthday aL < birthday a := Game.birthday_lt_left haL
        have hc : birthday cR < birthday c := Game.birthday_lt_right hcR
        let yR : Game := b.add cR
        have hyR : yR ∈ (b.add c).right := by
          rw [mem_add_right]
          exact Or.inr ⟨cR, hcR, rfl⟩
        refine ⟨Game.mulOpt4 aL (b.add c) a yR, ?_, ?_⟩
        · rw [mem_mul_right]
          exact Or.inl ⟨aL, haL, yR, hyR, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aL (b.add c) a (b.add cR)).eq
                ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cR))).add
                  (((aL.mul b).add (aL.mul cR)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aL) (Y := b.add c) (X := a) (yOpt := b.add cR)
                (A := (aL.mul b).add (aL.mul c))
                (B := (a.mul b).add (a.mul cR))
                (C := (aL.mul b).add (aL.mul cR))
                (IHa aL ha)
                (IHc cR hc)
                (IHac aL cR ha hc)
          have h_alg :
              ((((aL.mul b).add (aL.mul c)).add ((a.mul b).add (a.mul cR))).add
                ((aL.mul b).add (aL.mul cR)).neg).eq
              ((a.mul b).add (((aL.mul c).add (a.mul cR)).add (aL.mul cR).neg)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel
          have hw :
              (Game.mulOpt4 aL (b.add c) a (b.add cR)).eq
                ((a.mul b).add (((aL.mul c).add (a.mul cR)).add (aL.mul cR).neg)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩
          exact Game.eq_refl hw
      · -- Subcase B2: acR from (aR ∈ a.right, cL ∈ c.left)
        rcases hRL with ⟨aR, haR, cL, hcL, rfl⟩
        have ha : birthday aR < birthday a := Game.birthday_lt_right haR
        have hc : birthday cL < birthday c := Game.birthday_lt_left hcL
        let yL : Game := b.add cL
        have hyL : yL ∈ (b.add c).left := by
          rw [mem_add_left]
          exact Or.inr ⟨cL, hcL, rfl⟩
        refine ⟨Game.mulOpt4 aR (b.add c) a yL, ?_, ?_⟩
        · rw [mem_mul_right]
          exact Or.inr ⟨aR, haR, yL, hyL, by rfl⟩
        · have hrewrite :
              (Game.mulOpt4 aR (b.add c) a (b.add cL)).eq
                ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cL))).add
                  (((aR.mul b).add (aR.mul cL)).neg)) := by
            simpa [Game.mulOpt4] using
              Game.mulOpt4_congr
                (xOpt := aR) (Y := b.add c) (X := a) (yOpt := b.add cL)
                (A := (aR.mul b).add (aR.mul c))
                (B := (a.mul b).add (a.mul cL))
                (C := (aR.mul b).add (aR.mul cL))
                (IHa aR ha)
                (IHc cL hc)
                (IHac aR cL ha hc)

          have h_alg :
              ((((aR.mul b).add (aR.mul c)).add ((a.mul b).add (a.mul cL))).add
                ((aR.mul b).add (aR.mul cL)).neg).eq
              ((a.mul b).add (((aR.mul c).add (a.mul cL)).add (aR.mul cL).neg)) := by
                refine Game.eq_of_q_eq (u := _) (v := _) ?_
                · simp
                  abel

          have hw :
              (Game.mulOpt4 aR (b.add c) a (b.add cL)).eq
                ((a.mul b).add (((aR.mul c).add (a.mul cL)).add (aR.mul cL).neg)) :=
            Game.eq_trans ⟨hrewrite, h_alg⟩

          exact Game.eq_refl hw


theorem Game.mul_distrib {a b c : Game} :
    (a.mul (b.add c)).eq ((a.mul b).add (a.mul c)) := by
  let tri : TriGame := {a := a, b := b, c:= c}
  apply Game.mul_distrib_tri tri


theorem Game.mul_distrib_right {a b c : Game} :
    ((a.add b).mul c).eq ((a.mul c).add (b.mul c)) := by
  -- (a+b)*c = c*(a+b) = c*a + c*b = a*c + b*c
  have h1 : ((a.add b).mul c).eq (c.mul (a.add b)) := by
    simpa using (Game.mul_comm (a := (a.add b)) (b := c))
  have h2 : (c.mul (a.add b)).eq ((c.mul a).add (c.mul b)) := by
    simpa using (Game.mul_distrib (a := c) (b := a) (c := b))
  have h3 : ((c.mul a).add (c.mul b)).eq ((a.mul c).add (b.mul c)) := by
    refine Game.add_equal ?_
    constructor
    · exact Game.mul_comm
    · exact Game.mul_comm
  exact Game.eq_trans ⟨Game.eq_trans ⟨h1, h2⟩, h3⟩
