import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel
import Surreal.game
import Surreal.surreal
import Surreal.addition


/-- ## Definition of a ⊗ b
left elements are al of the form (al ⊗ b) ⊕ (a ⊗ bl) ⊕ (al ⊗ bl).neg
right elements are all of the form (al ⊗ br) ⊕ (a ⊗ br) ⊕ (al ⊗ br).neg
-/

def flatten {α : Type} : List (List α) → List α
  | [] => []
  | x :: xs => x ++ flatten xs

@[simp] theorem mem_flatten_iff {α : Type} {x : α} {xss : List (List α)} :
    x ∈ flatten xss ↔ ∃ xs ∈ xss, x ∈ xs := by
  induction xss with
  | nil =>
      simp [flatten]
  | cons xs xss ih =>
      simp [flatten, List.mem_append, ih]

private lemma birthday_add_lt_left₁ {x y xl : Game} (hxl : xl ∈ x.left) :
    xl.birthday + y.birthday < x.birthday + y.birthday := by
  exact add_lt_add_right (Game.birthday_lt_left hxl) _

private lemma birthday_add_lt_right₁ {x y xr : Game} (hxr : xr ∈ x.right) :
    xr.birthday + y.birthday < x.birthday + y.birthday := by
  exact add_lt_add_right (Game.birthday_lt_right hxr) _

private lemma birthday_add_lt_left₂ {x y yl : Game} (hyl : yl ∈ y.left) :
    x.birthday + yl.birthday < x.birthday + y.birthday := by
  exact add_lt_add_left (Game.birthday_lt_left hyl) _

private lemma birthday_add_lt_right₂ {x y yr : Game} (hyr : yr ∈ y.right) :
    x.birthday + yr.birthday < x.birthday + y.birthday := by
  exact add_lt_add_left (Game.birthday_lt_right hyr) _

private lemma birthday_add_lt_left_left {x y xl yl : Game}
    (hxl : xl ∈ x.left) (hyl : yl ∈ y.left) :
    xl.birthday + yl.birthday < x.birthday + y.birthday := by
  exact add_lt_add (Game.birthday_lt_left hxl) (Game.birthday_lt_left hyl)

private lemma birthday_add_lt_left_right {x y xl yr : Game}
    (hxl : xl ∈ x.left) (hyr : yr ∈ y.right) :
    xl.birthday + yr.birthday < x.birthday + y.birthday := by
  exact add_lt_add (Game.birthday_lt_left hxl) (Game.birthday_lt_right hyr)

private lemma birthday_add_lt_right_left {x y xr yl : Game}
    (hxr : xr ∈ x.right) (hyl : yl ∈ y.left) :
    xr.birthday + yl.birthday < x.birthday + y.birthday := by
  exact add_lt_add (Game.birthday_lt_right hxr) (Game.birthday_lt_left hyl)

private lemma birthday_add_lt_right_right {x y xr yr : Game}
    (hxr : xr ∈ x.right) (hyr : yr ∈ y.right) :
    xr.birthday + yr.birthday < x.birthday + y.birthday := by
  exact add_lt_add (Game.birthday_lt_right hxr) (Game.birthday_lt_right hyr)

def Game.mul : Game → Game → Game
  | x, y =>
    match _hx : x, _hy : y with
    | mk XL XR, mk YL YR =>
      let L :=
        flatten (XL.attach.map fun lx =>
          let xl := lx.val
          let _hxl := lx.property
          YL.attach.map fun ly =>
            let yl := ly.val
            let _hyl := ly.property
            ((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg) ++
        flatten (XR.attach.map fun rx =>
          let xr := rx.val
          let _hxr := rx.property
          YR.attach.map fun ry =>
            let yr := ry.val
            let _hyr := ry.property
            ((xr.mul y).add (x.mul yr)).add (xr.mul yr).neg)
      let R :=
        flatten (XL.attach.map fun lx =>
          let xl := lx.val
          let _hxl := lx.property
          YR.attach.map fun ry =>
            let yr := ry.val
            let _hyr := ry.property
            ((xl.mul y).add (x.mul yr)).add (xl.mul yr).neg) ++
        flatten (XR.attach.map fun rx =>
          let xr := rx.val
          let _hxr := rx.property
          YL.attach.map fun ly =>
            let yl := ly.val
            let _hyl := ly.property
            ((xr.mul y).add (x.mul yl)).add (xr.mul yl).neg)
      Game.mk L R
  termination_by x y => Game.birthday x + Game.birthday y
  decreasing_by
    · simpa [_hy] using
        birthday_add_lt_left₁ (x := Game.mk XL XR) (y := y)
          (xl := xl) (by simpa [Game.left] using _hxl)
    · simpa [_hx] using
        birthday_add_lt_left₂ (x := x) (y := Game.mk YL YR)
          (yl := yl) (by simpa [Game.left] using _hyl)
    · exact birthday_add_lt_left_left (x := Game.mk XL XR) (y := Game.mk YL YR)
        (xl := xl) (yl := yl) (by simpa [Game.left] using _hxl) (by simpa [Game.left] using _hyl)
    · simpa [_hy] using
        birthday_add_lt_right₁ (x := Game.mk XL XR) (y := y)
          (xr := xr) (by simpa [Game.right] using _hxr)
    · simpa [_hx] using
        birthday_add_lt_right₂ (x := x) (y := Game.mk YL YR)
          (yr := yr) (by simpa [Game.right] using _hyr)
    · exact birthday_add_lt_right_right (x := Game.mk XL XR) (y := Game.mk YL YR)
        (xr := xr) (yr := yr) (by simpa [Game.right] using _hxr) (by simpa [Game.right] using _hyr)
    · simpa [_hy] using
        birthday_add_lt_left₁ (x := Game.mk XL XR) (y := y)
          (xl := xl) (by simpa [Game.left] using _hxl)
    · simpa [_hx] using
        birthday_add_lt_right₂ (x := x) (y := Game.mk YL YR)
          (yr := yr) (by simpa [Game.right] using _hyr)
    · exact birthday_add_lt_left_right (x := Game.mk XL XR) (y := Game.mk YL YR)
        (xl := xl) (yr := yr) (by simpa [Game.left] using _hxl) (by simpa [Game.right] using _hyr)
    · simpa [_hy] using
        birthday_add_lt_right₁ (x := Game.mk XL XR) (y := y)
          (xr := xr) (by simpa [Game.right] using _hxr)
    · simpa [_hx] using
        birthday_add_lt_left₂ (x := x) (y := Game.mk YL YR)
          (yl := yl) (by simpa [Game.left] using _hyl)
    · exact birthday_add_lt_right_left (x := Game.mk XL XR) (y := Game.mk YL YR)
          (xr := xr) (yl := yl) (by simpa [Game.right] using _hxr) (by simpa [Game.left] using _hyl)

open Game

local notation:70 x " ⊗ " y => mul x y
local notation:70 x " ⊕ " y => add x y

/-- ## Description of elements in x ⊗ y -/

private theorem mem_flatten_map_map_iff {α β γ : Type} (f : α → β → γ) (z : γ)
    (A : List α) (B : List β) :
    z ∈ flatten (A.map (fun a => B.map (fun b => f a b))) ↔
      ∃ a ∈ A, ∃ b ∈ B, z = f a b := by
  rw [mem_flatten_iff]
  constructor
  · rintro ⟨xs, hxs, hz⟩
    rcases List.mem_map.mp hxs with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hz with ⟨b, hb, hfb⟩
    exact ⟨a, ha, b, hb, hfb.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨B.map (fun b => f a b), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨a, ha, rfl⟩
    · exact List.mem_map.mpr ⟨b, hb, rfl⟩

def Game.mulOpt4 (xOpt Y X yOpt : Game) : Game :=
  (((xOpt.mul Y).add (X.mul yOpt)).add (xOpt.mul yOpt).neg)

lemma mem_mul_left {x y z : Game} : z ∈ (x.mul y).left ↔
      (∃ xl ∈ x.left, ∃ yl ∈ y.left, z = Game.mulOpt4 xl y x yl) ∨
      (∃ xr ∈ x.right, ∃ yr ∈ y.right, z = Game.mulOpt4 xr y x yr) := by
  cases x with
  | mk XL XR =>
    cases y with
    | mk YL YR =>
      simp only [Game.mul, Game.left, List.mem_append]
      rw [mem_flatten_map_map_iff, mem_flatten_map_map_iff]
      constructor
      · rintro (h | h)
        · rcases h with ⟨xl, -, yl, -, hz⟩
          exact Or.inl ⟨xl.1, xl.2, yl.1, yl.2, by simpa [Game.mulOpt4] using hz⟩
        · rcases h with ⟨xr, -, yr, -, hz⟩
          exact Or.inr ⟨xr.1, xr.2, yr.1, yr.2, by simpa [Game.mulOpt4] using hz⟩
      · rintro (h | h)
        · rcases h with ⟨xl, hxl, yl, hyl, hz⟩
          exact Or.inl
            ⟨⟨xl, hxl⟩, by simp, ⟨yl, hyl⟩, by simp, by simpa [Game.mulOpt4] using hz⟩
        · rcases h with ⟨xr, hxr, yr, hyr, hz⟩
          exact Or.inr
            ⟨⟨xr, hxr⟩, by simp, ⟨yr, hyr⟩, by simp, by simpa [Game.mulOpt4] using hz⟩

lemma mem_mul_right {x y z : Game} : z ∈ (x.mul y).right ↔
      (∃ xl ∈ x.left, ∃ yr ∈ y.right, z = Game.mulOpt4 xl y x yr) ∨
      (∃ xr ∈ x.right, ∃ yl ∈ y.left, z = Game.mulOpt4 xr y x yl) := by
  cases x with
  | mk XL XR =>
    cases y with
    | mk YL YR =>
      simp only [Game.mul, Game.right, List.mem_append]
      rw [mem_flatten_map_map_iff, mem_flatten_map_map_iff]
      constructor
      · rintro (h | h)
        · rcases h with ⟨xl, -, yr, -, hz⟩
          exact Or.inl ⟨xl.1, xl.2, yr.1, yr.2, by simpa [Game.mulOpt4] using hz⟩
        · rcases h with ⟨xr, -, yl, -, hz⟩
          exact Or.inr ⟨xr.1, xr.2, yl.1, yl.2, by simpa [Game.mulOpt4] using hz⟩
      · rintro (h | h)
        · rcases h with ⟨xl, hxl, yr, hyr, hz⟩
          exact Or.inl
            ⟨⟨xl, hxl⟩, by simp, ⟨yr, hyr⟩, by simp, by simpa [Game.mulOpt4] using hz⟩
        · rcases h with ⟨xr, hxr, yl, hyl, hz⟩
          exact Or.inr
            ⟨⟨xr, hxr⟩, by simp, ⟨yl, hyl⟩, by simp, by simpa [Game.mulOpt4] using hz⟩

lemma mem_mul_left_ll {a b aL bL : Game}
    (haL : aL ∈ a.left) (hbL : bL ∈ b.left) :
    Game.mulOpt4 aL b a bL ∈ (a ⊗ b).left := by
  rw [mem_mul_left]
  exact Or.inl ⟨aL, haL, bL, hbL, rfl⟩

lemma mem_mul_left_rr {a b aR bR : Game}
    (haR : aR ∈ a.right) (hbR : bR ∈ b.right) :
    Game.mulOpt4 aR b a bR ∈ (a ⊗ b).left := by
  rw [mem_mul_left]
  exact Or.inr ⟨aR, haR, bR, hbR, rfl⟩

lemma mem_mul_right_lr {a b aL bR : Game}
    (haL : aL ∈ a.left) (hbR : bR ∈ b.right) :
    Game.mulOpt4 aL b a bR ∈ (a ⊗ b).right := by
  rw [mem_mul_right]
  exact Or.inl ⟨aL, haL, bR, hbR, rfl⟩

lemma mem_mul_right_rl {a b aR bL : Game}
    (haR : aR ∈ a.right) (hbL : bL ∈ b.left) :
    Game.mulOpt4 aR b a bL ∈ (a ⊗ b).right := by
  rw [mem_mul_right]
  exact Or.inr ⟨aR, haR, bL, hbL, rfl⟩


/-- ## a ⊗ 0 = 0 ⊗ a = 0 -/

lemma flatten_replicate_nil {α} (n : Nat) : flatten (List.replicate n ([] : List α)) = [] := by
  induction n with
  | zero =>
    simp [List.replicate, flatten]
  | succ n ih =>
    simp [List.replicate, flatten, ih]

lemma Game.mul_zero_eq (a : Game) : (a ⊗ zero) = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    simp [flatten_replicate_nil]

lemma Game.zero_mul_eq (a : Game) : (zero ⊗ a) = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    rfl

theorem Game.mul_zero (a : Game) : (a ⊗ zero) ∼ zero := by
  exact Game.eq_of_eq (Game.mul_zero_eq a)

theorem Game.zero_mul (a : Game) : (zero ⊗ a) ∼ zero := by
  exact Game.eq_of_eq (Game.zero_mul_eq a)


/-- ## Muliplication is commutative -/

private lemma Game.mulOpt4_comm (x y xl yl : Game)
    (hxy : (x ⊗ yl) ∼ (yl ⊗ x)) (hxl : (xl ⊗ y) ∼ (y ⊗ xl)) (hxlyl : (xl ⊗ yl) ∼ (yl ⊗ xl)) :
    eq (Game.mulOpt4 xl y x yl) (Game.mulOpt4 yl x y xl) := by
  refine Game.add_equal ?_
  constructor
  · exact Game.eq_trans ⟨Game.add_comm, Game.add_equal ⟨hxy, hxl⟩⟩
  · exact (Game.neg_congr).mp (Game.eq_symm hxlyl)

private lemma mem_mul_left_of_left_left {a b aL bL : Game}
    (haL : aL ∈ a.left) (hbL : bL ∈ b.left) : Game.mulOpt4 aL b a bL ∈ (a ⊗ b).left := by
  rw [Game.mulOpt4, mem_mul_left]
  exact Or.inl ⟨aL, haL, bL, hbL, rfl⟩

private lemma mem_mul_left_of_right_right {a b aR bR : Game}
    (haR : aR ∈ a.right) (hbR : bR ∈ b.right) : Game.mulOpt4 aR b a bR ∈ (a ⊗ b).left := by
  rw [Game.mulOpt4, mem_mul_left]
  exact Or.inr ⟨aR, haR, bR, hbR, rfl⟩

private lemma mem_mul_right_of_left_right {a b aL bR : Game}
    (haL : aL ∈ a.left) (hbR : bR ∈ b.right) : Game.mulOpt4 aL b a bR ∈ (a ⊗ b).right := by
  rw [Game.mulOpt4, mem_mul_right]
  exact Or.inl ⟨aL, haL, bR, hbR, rfl⟩

private lemma mem_mul_right_of_right_left {a b aR bL : Game}
    (haR : aR ∈ a.right) (hbL : bL ∈ b.left) : Game.mulOpt4 aR b a bL ∈ (a ⊗ b).right := by
  rw [Game.mulOpt4, mem_mul_right]
  exact Or.inr ⟨aR, haR, bL, hbL, rfl⟩

private lemma left_option_mul_comm {a b g : Game}
    (ih_aL : ∀ aL ∈ a.left, (aL ⊗ b) ∼ (b ⊗ aL))
    (ih_bL : ∀ bL ∈ b.left, (a ⊗ bL) ∼ (bL ⊗ a))
    (ih_aR : ∀ aR ∈ a.right, (aR ⊗ b) ∼ (b ⊗ aR))
    (ih_bR : ∀ bR ∈ b.right, (a ⊗ bR) ∼ (bR ⊗ a))
    (ih_LL : ∀ aL ∈ a.left, ∀ bL ∈ b.left, (aL ⊗ bL) ∼ (bL ⊗ aL))
    (ih_RR : ∀ aR ∈ a.right, ∀ bR ∈ b.right, (aR ⊗ bR) ∼ (bR ⊗ aR))
    (hg : g ∈ (a ⊗ b).left) : ∃ g' ∈ (b ⊗ a).left, eq g g' := by
  rw [mem_mul_left] at hg
  rcases hg with ⟨aL, haL, bL, hbL, rfl⟩ | ⟨aR, haR, bR, hbR, rfl⟩
  · refine ⟨_, mem_mul_left_of_left_left (a := b) (b := a) hbL haL, ?_⟩
    exact Game.mulOpt4_comm a b aL bL (ih_bL _ hbL) (ih_aL _ haL) (ih_LL _ haL _ hbL)
  · refine ⟨_, mem_mul_left_of_right_right (a := b) (b := a) hbR haR, ?_⟩
    exact Game.mulOpt4_comm a b aR bR (ih_bR _ hbR) (ih_aR _ haR) (ih_RR _ haR _ hbR)

private lemma left_option_mul_comm_symm {a b g : Game}
    (ih_aL : ∀ aL ∈ a.left, (aL ⊗ b) ∼ (b ⊗ aL))
    (ih_bL : ∀ bL ∈ b.left, (a ⊗ bL) ∼ (bL ⊗ a))
    (ih_aR : ∀ aR ∈ a.right, (aR ⊗ b) ∼ (b ⊗ aR))
    (ih_bR : ∀ bR ∈ b.right, (a ⊗ bR) ∼ (bR ⊗ a))
    (ih_LL : ∀ aL ∈ a.left, ∀ bL ∈ b.left, (aL ⊗ bL) ∼ (bL ⊗ aL))
    (ih_RR : ∀ aR ∈ a.right, ∀ bR ∈ b.right, (aR ⊗ bR) ∼ (bR ⊗ aR))
    (hg : g ∈ (b ⊗ a).left) : ∃ g' ∈ (a ⊗ b).left, g ∼ g' := by
  rw [mem_mul_left] at hg
  rcases hg with ⟨bL, hbL, aL, haL, rfl⟩ | ⟨bR, hbR, aR, haR, rfl⟩
  · refine ⟨_, mem_mul_left_of_left_left haL hbL, ?_⟩
    exact Game.eq_symm <|
      Game.mulOpt4_comm a b aL bL (ih_bL _ hbL) (ih_aL _ haL) (ih_LL _ haL _ hbL)
  · refine ⟨_, mem_mul_left_of_right_right haR hbR, ?_⟩
    exact Game.eq_symm <|
      Game.mulOpt4_comm a b aR bR (ih_bR _ hbR) (ih_aR _ haR) (ih_RR _ haR _ hbR)

private lemma right_option_mul_comm {a b g : Game}
    (ih_aL : ∀ aL ∈ a.left, (aL ⊗ b) ∼ (b ⊗ aL))
    (ih_bL : ∀ bL ∈ b.left, (a ⊗ bL) ∼ (bL ⊗ a))
    (ih_aR : ∀ aR ∈ a.right, (aR ⊗ b) ∼ (b ⊗ aR))
    (ih_bR : ∀ bR ∈ b.right, (a ⊗ bR) ∼ (bR ⊗ a))
    (ih_LR : ∀ aL ∈ a.left, ∀ bR ∈ b.right, (aL ⊗ bR) ∼ (bR ⊗ aL))
    (ih_RL : ∀ aR ∈ a.right, ∀ bL ∈ b.left, (aR ⊗ bL) ∼ (bL ⊗ aR))
    (hg : g ∈ (a ⊗ b).right) : ∃ g' ∈ (b ⊗ a).right, g ∼ g' := by
  rw [mem_mul_right] at hg
  rcases hg with ⟨aL, haL, bR, hbR, rfl⟩ | ⟨aR, haR, bL, hbL, rfl⟩
  · refine ⟨_, mem_mul_right_of_right_left (a := b) (b := a) hbR haL, ?_⟩
    exact Game.mulOpt4_comm a b aL bR (ih_bR _ hbR) (ih_aL _ haL) (ih_LR _ haL _ hbR)
  · refine ⟨_, mem_mul_right_of_left_right (a := b) (b := a) hbL haR, ?_⟩
    exact Game.mulOpt4_comm a b aR bL (ih_bL _ hbL) (ih_aR _ haR) (ih_RL _ haR _ hbL)

private lemma right_option_mul_comm_symm {a b g : Game}
    (ih_aL : ∀ aL ∈ a.left, (aL ⊗ b) ∼ (b ⊗ aL))
    (ih_bL : ∀ bL ∈ b.left, (a ⊗ bL) ∼ (bL ⊗ a))
    (ih_aR : ∀ aR ∈ a.right, (aR ⊗ b) ∼ (b ⊗ aR))
    (ih_bR : ∀ bR ∈ b.right, (a ⊗ bR) ∼ (bR ⊗ a))
    (ih_LR : ∀ aL ∈ a.left, ∀ bR ∈ b.right, (aL ⊗ bR) ∼ (bR ⊗ aL))
    (ih_RL : ∀ aR ∈ a.right, ∀ bL ∈ b.left, (aR ⊗ bL) ∼ (bL ⊗ aR))
    (hg : g ∈ (b ⊗ a).right) : ∃ g' ∈ (a ⊗ b).right, g ∼ g' := by
  rw [mem_mul_right] at hg
  rcases hg with ⟨bL, hbL, aR, haR, rfl⟩ | ⟨bR, hbR, aL, haL, rfl⟩
  · refine ⟨_, mem_mul_right_of_right_left haR hbL, ?_⟩
    exact Game.eq_symm <|
      Game.mulOpt4_comm a b aR bL (ih_bL _ hbL) (ih_aR _ haR) (ih_RL _ haR _ hbL)
  · refine ⟨_, mem_mul_right_of_left_right haL hbR, ?_⟩
    exact Game.eq_symm <|
      Game.mulOpt4_comm a b aL bR (ih_bR _ hbR) (ih_aL _ haL) (ih_LR _ haL _ hbR)

lemma Game.bigame_mul_comm (x : BiGame) : eq (x.a ⊗ x.b) (x.b ⊗ x.a) := by
  refine wf_B.induction (C := fun x : BiGame => (x.a ⊗ x.b) ∼ (x.b ⊗ x.a)) x ?_
  rintro ⟨a, b⟩ IH
  have ih_aL : ∀ aL ∈ a.left, (aL ⊗ b) ∼ (b ⊗ aL) := by
    intro aL haL
    exact IH ⟨aL, b⟩ (Game.B_of_left_mem_fst haL)
  have ih_bL : ∀ bL ∈ b.left, (a ⊗ bL) ∼ (bL ⊗ a) := by
    intro bL hbL
    exact IH ⟨a, bL⟩ (Game.B_of_left_mem_snd hbL)
  have ih_aR : ∀ aR ∈ a.right, (aR ⊗ b) ∼ (b ⊗ aR) := by
    intro aR haR
    exact IH ⟨aR, b⟩ (Game.B_of_right_mem_fst haR)
  have ih_bR : ∀ bR ∈ b.right, (a ⊗ bR) ∼ (bR ⊗ a) := by
    intro bR hbR
    exact IH ⟨a, bR⟩ (Game.B_of_right_mem_snd hbR)
  have ih_LL : ∀ aL ∈ a.left, ∀ bL ∈ b.left, (aL ⊗ bL) ∼ (bL ⊗ aL) := by
    intro aL haL bL hbL
    exact IH ⟨aL, bL⟩ (Game.B_of_left_left haL hbL)
  have ih_RR : ∀ aR ∈ a.right, ∀ bR ∈ b.right, (aR ⊗ bR) ∼ (bR ⊗ aR) := by
    intro aR haR bR hbR
    exact IH ⟨aR, bR⟩ (Game.B_of_right_right haR hbR)
  have ih_LR : ∀ aL ∈ a.left, ∀ bR ∈ b.right, (aL ⊗ bR) ∼ (bR ⊗ aL) := by
    intro aL haL bR hbR
    exact IH ⟨aL, bR⟩ (Game.B_of_left_right haL hbR)
  have ih_RL : ∀ aR ∈ a.right, ∀ bL ∈ b.left, (aR ⊗ bL) ∼ (bL ⊗ aR) := by
    intro aR haR bL hbL
    exact IH ⟨aR, bL⟩ (Game.B_of_right_left haR hbL)
  refine Game.eq_of_equiv_options ?_ ?_ ?_ ?_
  · intro g hg
    exact left_option_mul_comm ih_aL ih_bL ih_aR ih_bR ih_LL ih_RR hg
  · intro g hg
    exact left_option_mul_comm_symm ih_aL ih_bL ih_aR ih_bR ih_LL ih_RR hg
  · intro g hg
    exact right_option_mul_comm ih_aL ih_bL ih_aR ih_bR ih_LR ih_RL hg
  · intro g hg
    exact right_option_mul_comm_symm ih_aL ih_bL ih_aR ih_bR ih_LR ih_RL hg

theorem Game.mul_comm {a b : Game} : (a ⊗ b) ∼ (b ⊗ a) := by
  let bi : BiGame := {a := a, b := b}
  apply Game.bigame_mul_comm bi


/-- ## a ⊗ 1 = 1 ⊗ a = a -/

private lemma flatten_map_singleton {α β} (l : List α) (f : α → β) :
  flatten (l.map (fun x => [f x])) = l.map f := by
  induction l with
  | nil => simp [flatten]
  | cons h t ih => simp [flatten, ih]

private lemma map_id_iff {α : Type} (f : α → α) (l : List α) :
    l.map f = l ↔ ∀ x ∈ l, f x = x := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp [ih]

theorem Game.mul_one_eq {a : Game} : (a ⊗ one) = a := by
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
      simp [Game.mul_zero_eq, Game.add_zero', Game.neg_zero]
      apply IH
      exact birthday_lt_left lx_
    · rw [map_id_iff,← zero, ← one, ← hx]
      intro rx rx_
      simp [Game.mul_zero_eq, Game.add_zero', Game.neg_zero]
      apply IH
      exact birthday_lt_right rx_

theorem Game.mul_one {a : Game} : (a ⊗ one) ∼ a := by
    unfold eq
    rw [Game.mul_one_eq]
    exact ⟨Game.le_congr, Game.le_congr⟩

theorem Game.one_mul {a : Game} : (one ⊗ a) ∼ a := by
  exact Game.eq_trans ⟨Game.mul_comm, Game.mul_one⟩
