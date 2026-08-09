import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.Game
import Surreal.Surreal

open scoped Game

/-! ## Definition of x ⊕ y
x ⊕ y is defined as {xl ⊕ y, x ⊕ yl | xr ⊕ y, x ⊕ yr}
for all xl ∈ x.left, xr ∈ x.right, yl ∈ y.left, yr ∈ y.right.
-/

def Game.add : Game → Game → Game
  | x, y =>
    match _hx : x, _hy : y with
    | mk XL XR, mk YL YR =>
      let L := (XL.map (fun xl => xl.add y)) ++ (YL.map (fun yl => x.add yl))
      let R := (XR.map (fun xr => xr.add y)) ++ (YR.map (fun yr => x.add yr))
      mk L R
  termination_by x y => x.birthday + y.birthday
  decreasing_by
    · have hxl : xl.birthday < (Game.mk XL XR).birthday := by
        exact Game.birthday_lt_left (by assumption)
      simpa [_hx, _hy] using add_lt_add_right hxl y.birthday
    · have hyl : yl.birthday < (Game.mk YL YR).birthday :=
        by exact Game.birthday_lt_left (by assumption)
      simpa [_hx, _hy] using add_lt_add_left hyl x.birthday
    · have hxr : xr.birthday < (Game.mk XL XR).birthday := by
        exact Game.birthday_lt_right (by assumption)
      simpa [_hx, _hy] using add_lt_add_right hxr y.birthday
    · have hyr : yr.birthday < (Game.mk YL YR).birthday := by
        exact Game.birthday_lt_right (by assumption)
      simpa [_hx, _hy] using add_lt_add_left hyr x.birthday

local notation:70 x " ⊕ " y => Game.add x y

/-! ## Descriptions of left and right options of x ⊕ y -/

lemma add_left (a b : Game) :
    (a ⊕ b).left = a.left.map (fun al => al ⊕ b) ++ b.left.map (fun bl => a ⊕ bl) := by
  cases a; cases b; simp [Game.add, Game.left]

lemma add_right (a b : Game) :
    (a ⊕ b).right = a.right.map (fun ar => ar ⊕ b) ++ b.right.map (fun br => a ⊕ br) := by
  cases a; cases b; simp [Game.add, Game.right]

lemma mem_add_left_iff {x y l : Game} :
l ∈ (x ⊕ y).left ↔ (∃ xl ∈ x.left, (xl ⊕ y) = l) ∨ (∃ yl ∈ y.left, (x ⊕ yl) = l) := by
  rw [add_left]
  simp [eq_comm]

lemma mem_add_right_iff {x y r : Game} :
r ∈ (x ⊕ y).right ↔ (∃ xr ∈ x.right, (xr ⊕ y) = r) ∨ (∃ yr ∈ y.right, (x ⊕ yr) = r) := by
  rw [add_right]
  simp [eq_comm]

lemma mem_add_left₁ {x y xl : Game} (hxl : xl ∈ x.left) :
    (xl ⊕ y) ∈ (x ⊕ y).left := by
  rw [mem_add_left_iff]
  exact Or.inl ⟨xl, hxl, rfl⟩

lemma mem_add_left₂ {x y yl : Game} (hyl : yl ∈ y.left) :
    (x ⊕ yl) ∈ (x ⊕ y).left := by
  rw [mem_add_left_iff]
  exact Or.inr ⟨yl, hyl, rfl⟩

lemma mem_add_right₁ {x y xr : Game} (hxr : xr ∈ x.right) :
    (xr ⊕ y) ∈ (x ⊕ y).right := by
  rw [mem_add_right_iff]
  exact Or.inl ⟨xr, hxr, rfl⟩

lemma mem_add_right₂ {x y yr : Game} (hyr : yr ∈ y.right) :
    (x ⊕ yr) ∈ (x ⊕ y).right := by
  rw [mem_add_right_iff]
  exact Or.inr ⟨yr, hyr, rfl⟩


/-! ## Addition by zero -/

theorem Game.add_zero' {a : Game} : (a ⊕ zero) = a := by
  induction a using wf_R.induction with
  | h x IH =>
      cases x with
      | mk XL XR =>
          unfold Game.add
          simp [zero]
          constructor
          · simpa only [Game.zero, List.map_id] using
              (List.map_congr_left (l := XL)
                (f := fun xl => xl ⊕ Game.zero) (g := id)
                (fun xl hxl => IH xl (Game.birthday_lt_left hxl)))
          · simpa only [Game.zero, List.map_id] using
              (List.map_congr_left (l := XR)
                (f := fun xr => xr ⊕ Game.zero) (g := id)
                (fun xr hxr => IH xr (Game.birthday_lt_right hxr)))

theorem Game.zero_add' {a : Game} : (zero ⊕ a) = a := by
  induction a using wf_R.induction with
  | h x IH =>
      cases x with
      | mk XL XR =>
          unfold Game.add
          simp [zero]
          constructor
          · simpa only [Game.zero, List.map_id] using
              (List.map_congr_left (l := XL)
                (f := fun xl => Game.zero ⊕ xl) (g := id)
                (fun xl hxl => IH xl (Game.birthday_lt_left hxl)))
          · simpa only [Game.zero, List.map_id] using
              (List.map_congr_left (l := XR)
                (f := fun xr => Game.zero ⊕ xr) (g := id)
                (fun xr hxr => IH xr (Game.birthday_lt_right hxr)))

theorem Game.add_zero {a : Game} : (a ⊕ zero) ∼ a := by
  exact Game.eq_of_eq Game.add_zero'

theorem Game.zero_add {a : Game} : (zero ⊕ a) ∼ a := by
  exact Game.eq_of_eq Game.zero_add'


/-! ## Commutativity of ⊕ -/

private abbrev AddCommIH (x y : Game) : Prop :=
  ∀ z : Game.BiGame, Game.B z ⟨x, y⟩ → Game.eq (z.a ⊕ z.b) (z.b ⊕ z.a)

private lemma add_comm_ih_swap {x y : Game} (IH : AddCommIH x y) : AddCommIH y x := by
  rintro ⟨a, b⟩ h
  exact Game.eq_symm <| IH ⟨b, a⟩ (by simpa [Game.B, Nat.add_comm] using h)

private lemma left_option_add_comm {x y l : Game}
    (IH : AddCommIH x y)
    (hl : l ∈ (x ⊕ y).left) : ∃ l' ∈ (y ⊕ x).left, Game.eq l l' := by
  rcases (mem_add_left_iff (x := x) (y := y) (l := l)).1 hl with
    ⟨xl, hxl, rfl⟩ | ⟨yl, hyl, rfl⟩
  · exact ⟨y ⊕ xl, mem_add_left₂ (x := y) (y := x) hxl,
      IH ⟨xl, y⟩ (Game.B_of_left_mem_fst hxl)⟩
  · exact ⟨yl ⊕ x, mem_add_left₁ (x := y) (y := x) hyl,
      IH ⟨x, yl⟩ (Game.B_of_left_mem_snd hyl)⟩

private lemma right_option_add_comm {x y r : Game}
    (IH : AddCommIH x y)
    (hr : r ∈ (x ⊕ y).right) : ∃ r' ∈ (y ⊕ x).right, Game.eq r r' := by
  rcases (mem_add_right_iff (x := x) (y := y) (r := r)).1 hr with
    ⟨xr, hxr, rfl⟩ | ⟨yr, hyr, rfl⟩
  · exact ⟨y ⊕ xr, mem_add_right₂ (x := y) (y := x) hxr,
      IH ⟨xr, y⟩ (Game.B_of_right_mem_fst hxr)⟩
  · exact ⟨yr ⊕ x, mem_add_right₁ (x := y) (y := x) hyr,
      IH ⟨x, yr⟩ (Game.B_of_right_mem_snd hyr)⟩

theorem Game.add_comm {a b : Game} : Game.eq (a ⊕ b) (b ⊕ a) := by
  refine wf_B.induction
    (C := fun z : BiGame => Game.eq (z.a ⊕ z.b) (z.b ⊕ z.a)) ⟨a, b⟩ ?_
  rintro ⟨x, y⟩ IH
  exact Game.eq_of_equiv_options
    (fun _ hl => left_option_add_comm IH hl)
    (fun _ hl => left_option_add_comm (x := y) (y := x) (add_comm_ih_swap IH) hl)
    (fun _ hr => right_option_add_comm IH hr)
    (fun _ hr => right_option_add_comm (x := y) (y := x) (add_comm_ih_swap IH) hr)

/-! ##  a ≤ b → (a ⊕ c) ≤ (b ⊕ c)  ↔   (a ⊕ c) ≤  (b ⊕ c) → a ≤ b
These two statements have to be proved hand-in-hand
-/

private lemma not_self_le_left {x l : Game} (hl : l ∈ x.left) : ¬ x ≼ l :=
  Game.not_ge_left_of_le Game.le_congr hl

private lemma not_right_le_self {x r : Game} (hr : r ∈ x.right) : ¬ r ≼ x :=
  Game.not_le_right_of_le Game.le_congr hr

private theorem Game.add_right_iff (x : TriGame) :
    ((x.a ⊕ x.c) ≼ (x.b ⊕ x.c)) ↔ x.a ≼ x.b := by
  refine wf_T.induction
    (C := fun t : TriGame => ((t.a ⊕ t.c) ≼ (t.b ⊕ t.c)) ↔ t.a ≼ t.b) x ?_
  intro t IH
  rcases t with ⟨a, b, c⟩
  constructor
  · intro hsum
    rw [Game.le]
    constructor
    · intro al hal h_b_le_al
      exact(not_self_le_left (x := a ⊕ c) (l := al ⊕ c)
          (mem_add_left₁ (x := a) (y := c) hal))
        (Game.le_trans ⟨hsum, (IH ⟨b, al, c⟩
            (T_of_a_left_mem (a := a) (b := b) (c := c) hal)).2 h_b_le_al⟩)
    · intro br hbr h_br_le_a
      exact
        (not_right_le_self (x := b ⊕ c) (r := br ⊕ c)
          (mem_add_right₁ (x := b) (y := c) hbr))
        (Game.le_trans ⟨(IH ⟨br, a, c⟩
            (T_of_b_right_mem (a := a) (b := b) (c := c) hbr)).2 h_br_le_a, hsum⟩)
  · intro hab
    rw [Game.le]
    constructor
    · intro l hl
      rcases (mem_add_left_iff (x := a) (y := c) (l := l)).1 hl with
        ⟨al, hal, rfl⟩ | ⟨cl, hcl, rfl⟩
      · intro hcontra
        exact
          (Game.not_ge_left_of_le hab hal)
          ((IH ⟨b, al, c⟩ (T_of_a_left_mem (a := a) (b := b) (c := c) hal)).1 hcontra)
      · intro hcontra
        exact
          (not_self_le_left (x := b ⊕ c) (l := b ⊕ cl)
            (mem_add_left₂ (x := b) (y := c) hcl))
          (Game.le_trans ⟨hcontra, (IH ⟨a, b, cl⟩
              (T_of_c_left_mem (a := a) (b := b) (c := c) hcl)).2 hab⟩)
    · intro r hr
      rcases (mem_add_right_iff (x := b) (y := c) (r := r)).1 hr with
        ⟨br, hbr, rfl⟩ | ⟨cr, hcr, rfl⟩
      · intro hcontra
        exact
          (Game.not_le_right_of_le hab hbr)
          ((IH ⟨br, a, c⟩ (T_of_b_right_mem (a := a) (b := b) (c := c) hbr)).1 hcontra)
      · intro hcontra
        exact
          (not_right_le_self (x := a ⊕ c) (r := a ⊕ cr)
            (mem_add_right₂ (x := a) (y := c) hcr))
          (Game.le_trans
            ⟨(IH ⟨a, b, cr⟩ (T_of_c_right_mem (a := a) (b := b) (c := c) hcr)).2 hab, hcontra⟩)

lemma Game.big_aux (x : TriGame) :
  (x.a ≼ x.b → (x.a ⊕ x.c) ≼ (x.b ⊕ x.c)) ∧ (((x.a ⊕ x.c) ≼ (x.b ⊕ x.c)) → x.a ≼ x.b) := by
  exact ⟨(Game.add_right_iff x).2, (Game.add_right_iff x).1⟩

theorem Game.add_le_add_right {a b c : Game} (hab : a ≼ b) : (a ⊕ c) ≼ (b ⊕ c) := by
  exact (Game.add_right_iff ⟨a, b, c⟩).2 hab

theorem Game.add_right_cancel {a b c : Game} (h : (a ⊕ c) ≼ (b ⊕ c)) : a ≼ b := by
  exact (Game.add_right_iff ⟨a, b, c⟩).1 h


/-! ##  Some other inequalities-/

theorem Game.add_le_add {a b c d : Game} : (a ≼ c ∧ b ≼ d) → (a ⊕ b) ≼ (c ⊕ d) := by
  intro ⟨h_ac, h_bd⟩
  have h1 : (a ⊕ b) ≼ (c ⊕ b) :=
    (Game.big_aux ⟨a, c, b⟩).1 h_ac
  let t : TriGame := {a := b, b := d, c := c}
  have t1 : (b ⊕ c) ≼ (d ⊕ c) := (Game.big_aux t).1 h_bd
  have t2 : (c ⊕ b) ≼ (d ⊕ c) := by
    have cb_eq : (c ⊕ b).eq (b ⊕ c) := Game.add_comm
    unfold eq at cb_eq
    apply Game.le_trans ⟨cb_eq.1, t1⟩
  have t3 : (c ⊕ b) ≼ (c ⊕ d) := by
    have dc_eq : (d ⊕ c).eq (c ⊕ d) := Game.add_comm
    unfold eq at dc_eq
    apply Game.le_trans ⟨t2, dc_eq.1⟩
  exact Game.le_trans ⟨h1, t3⟩

theorem Game.add_reduce {a b c d : Game} : ((c ⊕ d) ≼ (a ⊕ b) ∧ (b ≼ d)) → (c ≼ a) := by
  intro h
  rcases h with ⟨h_main, h_bd⟩
  have h_mono : (b ⊕ c) ≼ (d ⊕ c) := (Game.big_aux ⟨b, d, c⟩).1 h_bd
  have comm_cb : (c ⊕ b) ≼ (b ⊕ c) := (Game.add_comm).1
  have comm_dc : (d ⊕ c) ≼ (c ⊕ d) := (Game.add_comm).1
  have step1 : (c ⊕ b) ≼ (d ⊕ c) := Game.le_trans ⟨comm_cb, h_mono⟩
  have step2 : (c ⊕ b) ≼ (c ⊕ d) := Game.le_trans ⟨step1, comm_dc⟩
  have step3 : (c ⊕ b) ≼ (a ⊕ b) := Game.le_trans ⟨step2, h_main⟩
  exact (Game.big_aux ⟨c, a, b⟩).2 step3

theorem Game.add_equal {a b c d : Game} : (a.eq c) ∧ (b.eq d) → (a ⊕ b).eq (c ⊕ d) := by
  intro ⟨h1, h2⟩
  unfold eq at h1 h2
  unfold eq
  constructor
  · exact Game.add_le_add ⟨h1.1, h2.1⟩
  · exact Game.add_le_add ⟨h1.2, h2.2⟩

theorem Game.add_lt_le {a b c d : Game} : (a ≺ c) ∧ (b ≼ d) → (a ⊕ b) ≺ (c ⊕ d) := by
  intro h
  unfold lt at h
  constructor
  · exact Game.add_le_add  ⟨h.1.1, h.2⟩
  · intro h_contra
    have h_bad : c ≼ a := Game.add_reduce ⟨h_contra, h.2⟩
    exact h.1.2 h_bad

theorem Game.add_le_lt {a b c d : Game} : (a ≼ c) ∧ (b ≺ d) → (a ⊕ b) ≺ (c ⊕ d) := by
  rintro ⟨hac, hbd⟩
  exact Game.lt_of_le_of_lt (Game.add_comm (a := a) (b := b)).1
    (Game.lt_of_lt_of_le
      (Game.add_lt_le ⟨hbd, hac⟩)
      (Game.add_comm (a := d) (b := c)).1)


theorem Game.add_le_right_right {u v : Game} (t : Game) : u ≼ v → (u ⊕ t) ≼ (v ⊕ t) := by
  intro huv
  exact Game.add_le_add_right huv

theorem Game.add_le_left_right {u v : Game} (t : Game) : u ≼ v → (t ⊕ u) ≼ (v ⊕ t) := by
  intro huv
  have comm_tu : (t ⊕ u) ≼ (u ⊕ t) := (Game.add_comm).1
  exact Game.le_trans ⟨comm_tu, (Game.add_le_add_right huv)⟩

theorem Game.add_le_right_left {u v : Game} (t : Game) : u ≼ v → (u ⊕ t) ≼ (t ⊕ v) := by
  intro huv
  have comm_tv : (v ⊕ t) ≼ (t ⊕ v) := (Game.add_comm).1
  exact Game.le_trans ⟨(Game.add_le_add_right huv), comm_tv⟩

theorem Game.add_le_left_left {u v : Game} (t : Game) : u ≼ v → (t ⊕ u) ≼ (t ⊕ v) := by
  intro huv
  have comm_tu : (t ⊕ u) ≼ (u ⊕ t) := (Game.add_comm).1
  exact Game.le_trans ⟨comm_tu, (Game.add_le_right_left t huv)⟩


theorem Game.add_lt_left_left {u v : Game} (t : Game) : u ≺ v → (t ⊕ u) ≺ (t ⊕ v) := by
  intro huv
  exact Game.add_le_lt ⟨Game.le_congr, huv⟩

theorem Game.add_lt_right_right {u v : Game} (t : Game) : u ≺ v → (u ⊕ t) ≺ (v ⊕ t) := by
  intro huv
  exact Game.add_lt_le ⟨huv, Game.le_congr⟩

theorem Game.add_lt_left_right {u v : Game} (t : Game) : u ≺ v → (t ⊕ u) ≺ (v ⊕ t) := by
  intro huv
  exact Game.lt_of_le_of_lt
    (Game.add_comm (a := t) (b := u)).1
    (Game.add_lt_right_right t huv)

theorem Game.add_lt_right_left {u v : Game} (t : Game) : u ≺ v → (u ⊕ t) ≺ (t ⊕ v) := by
  intro huv
  exact Game.lt_of_lt_of_le
    (Game.add_lt_right_right t huv)
    (Game.add_comm (a := v) (b := t)).1

/-! ##  Associativity of ⊕ -/

private lemma append_map3_congr {α β} {l1 l2 l3 : List α} {f1 g1 f2 g2 f3 g3 : α → β}
    (h1 : l1.map f1 = l1.map g1) (h2 : l2.map f2 = l2.map g2) (h3 : l3.map f3 = l3.map g3) :
    l1.map f1 ++ (l2.map f2 ++ l3.map f3) = l1.map g1 ++ (l2.map g2 ++ l3.map g3) := by
  exact congrArg₂ List.append h1 (congrArg₂ List.append h2 h3)

theorem Game.add_assoc {a b c : Game} : ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) := by
  induction a using wf_R.induction generalizing b c with
  | h a IHa =>
    induction b using wf_R.induction generalizing c with
    | h b IHb =>
      induction c using wf_R.induction with
      | h c IHc =>
        refine Game.ext ?_ ?_
        · simpa [add_left, List.map_append, List.map_map, List.append_assoc, Function.comp] using
            (append_map3_congr
              (by
                apply List.map_congr_left
                intro al hal
                simpa using IHa al (birthday_lt_left hal) (b := b) (c := c))
              (by
                apply List.map_congr_left
                intro bl hbl
                simpa using IHb bl (birthday_lt_left hbl) (c := c))
              (by
                apply List.map_congr_left
                intro cl hcl
                simpa using IHc cl (birthday_lt_left hcl)))
        · simpa [add_right, List.map_append, List.map_map, List.append_assoc, Function.comp] using
            (append_map3_congr
              (by
                apply List.map_congr_left
                intro ar har
                simpa using IHa ar (birthday_lt_right har) (b := b) (c := c))
              (by
                apply List.map_congr_left
                intro br hbr
                simpa using IHb br (birthday_lt_right hbr) (c := c))
              (by
                apply List.map_congr_left
                intro cr hcr
                simpa using IHc cr (birthday_lt_right hcr)))


/-! ## Definition of negative  -/

def Game.neg : Game → Game
  | g =>
    let L := g.right.attach.map (fun ⟨r, _hr⟩ => Game.neg r)
    let R := g.left.attach.map (fun ⟨l, _hl⟩ => Game.neg l)
    Game.mk L R
  termination_by g => g.birthday
  decreasing_by
    · exact birthday_lt_right _hr
    · exact birthday_lt_left _hl

/-! ## Description of negative elements -/

lemma neg_left_def (g : Game) :
    (Game.neg g).left = g.right.map Game.neg := by
  rw [Game.neg]
  exact List.attach_map_val

lemma neg_right_def (g : Game) :
    (Game.neg g).right = g.left.map Game.neg := by
  rw [Game.neg]
  exact List.attach_map_val

/-! ## -0 = 0 -/

theorem Game.neg_zero : zero.neg = zero := by
  rw [Game.neg]
  simp [zero]
  unfold Game.right Game.left
  simp

/-! ##  a ≤ b ↔  -b ≤ -a -/

lemma mem_neg_left_iff {x l : Game} :
    l ∈ (Game.neg x).left ↔ ∃ r ∈ x.right, l = Game.neg r := by
  rw [neg_left_def]
  simp [eq_comm]

lemma mem_neg_right_iff {x r : Game} :
    r ∈ (Game.neg x).right ↔ ∃ l ∈ x.left, r = Game.neg l := by
  rw [neg_right_def]
  simp [eq_comm]

lemma mem_neg_left_of_right {x r : Game} (hr : r ∈ x.right) :
    Game.neg r ∈ (Game.neg x).left := by
  exact mem_neg_left_iff.mpr ⟨r, hr, rfl⟩

lemma mem_neg_right_of_left {x l : Game} (hl : l ∈ x.left) :
    Game.neg l ∈ (Game.neg x).right := by
  exact mem_neg_right_iff.mpr ⟨l, hl, rfl⟩

theorem bigame_neg_le_neg (x : Game.BiGame) :
    x.a ≼ x.b ↔ (Game.neg x.b) ≼ (Game.neg x.a) := by
  refine Game.wf_B.induction
    (C := fun x : Game.BiGame =>
     x.a ≼ x.b ↔ (Game.neg x.b) ≼ (Game.neg x.a)) x ?_
  rintro ⟨a, b⟩ IH
  have ih_left {aL : Game} (haL : aL ∈ a.left) :
      b ≼ aL ↔ (Game.neg aL) ≼ (Game.neg b) := by
    simpa using IH ⟨b, aL⟩ (Game.B_of_left_mem_swap (a := a) (b := b) haL)
  have ih_right {bR : Game} (hbR : bR ∈ b.right) :
      bR ≼ a ↔ (Game.neg a) ≼ (Game.neg bR) := by
    simpa using IH ⟨bR, a⟩ (Game.B_of_right_mem_swap (a := a) (b := b) hbR)
  constructor
  · intro h
    rw [Game.le] at h ⊢
    refine ⟨?_, ?_⟩
    · rintro l hl h'
      rcases mem_neg_left_iff.mp hl with ⟨bR, hbR, rfl⟩
      exact h.2 bR hbR ((ih_right hbR).2 h')
    · rintro r hr h'
      rcases mem_neg_right_iff.mp hr with ⟨aL, haL, rfl⟩
      exact h.1 aL haL ((ih_left haL).2 h')
  · intro h
    rw [Game.le] at h ⊢
    refine ⟨?_, ?_⟩
    · intro aL haL h'
      exact h.2 _ (mem_neg_right_iff.mpr ⟨aL, haL, rfl⟩) ((ih_left haL).1 h')
    · intro bR hbR h'
      exact h.1 _ (mem_neg_left_iff.mpr ⟨bR, hbR, rfl⟩) ((ih_right hbR).1 h')


/-! ## a ≤, =, < b  ↔  -b ≤, =, < -a -/

theorem Game.neg_le_neg {a b : Game} : le a b ↔ le (neg b) (neg a) := by
  let bi : BiGame := {a := a, b := b}
  apply bigame_neg_le_neg bi

theorem Game.neg_congr {a b : Game} : a.eq b ↔ (neg b).eq (neg a) := by
  unfold eq
  rw [Game.neg_le_neg]
  nth_rw 2 [Game.neg_le_neg]

theorem Game.neg_congr_left {a b : Game} (h : a ∼ b) : Game.neg a ∼ Game.neg b := by
  exact Game.eq_symm <| (Game.neg_congr).mp h

theorem Game.neg_lt_neg {a b : Game} : lt a b ↔ lt (neg b) (neg a) := by
  unfold lt
  rw [Game.neg_le_neg]
  nth_rw 2 [Game.neg_le_neg]

/-! ## a + (-a) = 0 -/

private lemma add_neg_mem_right_of_left {x xl : Game} (hxl : xl ∈ x.left) :
    (xl ⊕ (Game.neg xl)) ∈ (xl ⊕ (Game.neg x)).right := by
  rw [mem_add_right_iff]
  exact Or.inr ⟨Game.neg xl, mem_neg_right_iff.mpr ⟨xl, hxl, rfl⟩, rfl⟩

private lemma add_neg_mem_right_of_right {x xr : Game} (hxr : xr ∈ x.right) :
    (xr ⊕ (Game.neg xr)) ∈ (x ⊕ (Game.neg xr)).right := by
  rw [mem_add_right_iff]
  exact Or.inl ⟨xr, hxr, rfl⟩

private lemma add_neg_mem_left_of_right {x xr : Game} (hxr : xr ∈ x.right) :
    (xr ⊕ (Game.neg xr)) ∈ (xr ⊕ (Game.neg x)).left := by
  rw [mem_add_left_iff]
  exact Or.inr ⟨Game.neg xr, mem_neg_left_iff.mpr ⟨xr, hxr, rfl⟩, rfl⟩

private lemma add_neg_mem_left_of_left {x xl : Game} (hxl : xl ∈ x.left) :
    (xl ⊕ (Game.neg xl)) ∈ (x ⊕ (Game.neg xl)).left := by
  rw [mem_add_left_iff]
  exact Or.inl ⟨xl, hxl, rfl⟩

theorem Game.add_neg (x : Game) : (x ⊕ (Game.neg x)).eq zero := by
  refine wf_R.induction (C := fun x : Game => (x ⊕ (Game.neg x)).eq zero) x ?_
  intro x IH
  unfold Game.eq
  constructor
  · unfold Game.le
    refine ⟨?_, by simp [zero, Game.right]⟩
    intro l hl hz
    unfold Game.le at hz
    have hl' := (mem_add_left_iff (x := x) (y := Game.neg x) (l := l)).1 hl
    rcases hl' with ⟨xl, hxl, rfl⟩ | ⟨n, hn, rfl⟩
    · exact hz.2 _ (add_neg_mem_right_of_left hxl) (IH xl (birthday_lt_left hxl)).1
    · rcases mem_neg_left_iff.mp hn with ⟨xr, hxr, rfl⟩
      exact hz.2 _ (add_neg_mem_right_of_right hxr) (IH xr (birthday_lt_right hxr)).1
  · unfold Game.le
    refine ⟨by simp [zero, Game.left], ?_⟩
    intro r hr hz
    unfold Game.le at hz
    have hr' := (mem_add_right_iff (x := x) (y := Game.neg x) (r := r)).1 hr
    rcases hr' with ⟨xr, hxr, rfl⟩ | ⟨n, hn, rfl⟩
    · exact hz.1 _ (add_neg_mem_left_of_right hxr) (IH xr (birthday_lt_right hxr)).2
    · rcases mem_neg_right_iff.mp hn with ⟨xl, hxl, rfl⟩
      exact hz.1 _ (add_neg_mem_left_of_left hxl) (IH xl (birthday_lt_left hxl)).2

theorem Game.neg_add (x : Game) : ((Game.neg x) ⊕ x).eq Game.zero := by
  apply Game.eq_trans
  constructor
  · exact Game.add_comm
  · exact Game.add_neg x


/-! ## Addition Results for surreal numbers -/

open Surreal

/-! ##  Sum of surreal numbers is surreal-/

private lemma add_left_lt_right {a b : Surreal} {L R : Game}
  (hL : L ∈ (a.val ⊕ b.val).left) (hR : R ∈ (a.val ⊕ b.val).right) : L ≺ R := by
  rw [mem_add_left_iff] at hL
  rw [mem_add_right_iff] at hR
  rcases hL with ⟨al, hal, rfl⟩ | ⟨bl, hbl, rfl⟩
  · rcases hR with ⟨ar, har, rfl⟩ | ⟨br, hbr, rfl⟩
    · exact Game.add_lt_le
        ⟨Surreal.left_lt_right (x := a) hal har, Game.le_congr⟩
    · exact Game.add_lt_le
        ⟨Surreal.left_lt (x := a) hal, (Surreal.lt_right (x := b) hbr).1⟩
  · rcases hR with ⟨ar, har, rfl⟩ | ⟨br, hbr, rfl⟩
    · exact Game.add_lt_le
        ⟨Surreal.lt_right (x := a) har, (Surreal.left_lt (x := b) hbl).1⟩
    · exact Game.add_le_lt
        ⟨Game.le_congr, Surreal.left_lt_right (x := b) hbl hbr⟩

private lemma add_left_option_isSurreal {a b : Surreal}
    (IH : ∀ y : BiSurreal, U y ⟨a, b⟩ → IsSurreal (y.a.val ⊕ y.b.val))
    {L : Game} (hL : L ∈ (a.val ⊕ b.val).left) : IsSurreal L := by
  rw [mem_add_left_iff] at hL
  rcases hL with ⟨al, hal, rfl⟩ | ⟨bl, hbl, rfl⟩
  · exact IH ⟨leftOption a al hal, b⟩ (U_left₁ (a := a) (b := b) hal)
  · exact IH ⟨a, leftOption b bl hbl⟩ (U_left₂ (a := a) (b := b) hbl)

private lemma add_right_option_isSurreal {a b : Surreal}
    (IH : ∀ y : BiSurreal, U y ⟨a, b⟩ → IsSurreal (y.a.val ⊕ y.b.val))
    {R : Game} (hR : R ∈ (a.val ⊕ b.val).right) : IsSurreal R := by
  rw [mem_add_right_iff] at hR
  rcases hR with ⟨ar, har, rfl⟩ | ⟨br, hbr, rfl⟩
  · exact IH ⟨rightOption a ar har, b⟩ (U_right₁ (a := a) (b := b) har)
  · exact IH ⟨a, rightOption b br hbr⟩ (U_right₂ (a := a) (b := b) hbr)

theorem add_isSurreal1 (x : BiSurreal) : IsSurreal (x.a.val ⊕ x.b.val) := by
  apply wf_U.induction x
  intro x IH
  rcases x with ⟨a, b⟩
  unfold IsSurreal
  constructor
  · intro L hL R hR
    exact (add_left_lt_right (a := a) (b := b) hL hR).2
  · constructor
    · intro L hL
      exact add_left_option_isSurreal (a := a) (b := b) IH hL
    · intro R hR
      exact add_right_option_isSurreal (a := a) (b := b) IH hR

theorem Surreal.add_isSurreal {a b : Surreal} :
    IsSurreal (a.val ⊕ b.val) := by
  exact add_isSurreal1 ⟨a, b⟩

def Surreal.add (a b : Surreal) : Surreal := ⟨a.val ⊕ b.val, add_isSurreal⟩

/-! ##  a is surreal ↔ -a is surreal -/

private lemma not_neg_le_neg {x xl xr : Game} (sx : IsSurreal x)
    (hxl : xl ∈ x.left) (hxr : xr ∈ x.right) :
    ¬ (Game.neg xl) ≼ (Game.neg xr) := by
  unfold IsSurreal at sx
  intro h
  exact sx.1 xl hxl xr hxr ((Game.neg_le_neg (a := xr) (b := xl)).2 h)

theorem Surreal.neg_isSurreal (a : Surreal) : IsSurreal (Game.neg a.val) := by
  refine (Game.wf_R.induction
    (C := fun x => IsSurreal x → IsSurreal (Game.neg x)) a.val ?_) a.property
  intro x IH sx
  unfold IsSurreal
  refine ⟨?_, ?_, ?_⟩
  · intro l hl r hr
    rcases mem_neg_left_iff.mp hl with ⟨xr, hxr, rfl⟩
    rcases mem_neg_right_iff.mp hr with ⟨xl, hxl, rfl⟩
    exact not_neg_le_neg sx hxl hxr
  · intro l hl
    rcases mem_neg_left_iff.mp hl with ⟨xr, hxr, rfl⟩
    exact IH xr (Game.birthday_lt_of_isOption (Or.inr hxr))
      (IsSurreal.isSurreal_option sx (Or.inr hxr))
  · intro r hr
    rcases mem_neg_right_iff.mp hr with ⟨xl, hxl, rfl⟩
    exact IH xl (Game.birthday_lt_of_isOption (Or.inl hxl))
      (IsSurreal.isSurreal_option sx (Or.inl hxl))

theorem Surreal.add_neg (a : Surreal) : (a.val ⊕ (Game.neg a.val)).eq Game.zero := by
  exact Game.add_neg a.val

theorem Surreal.neg_add (a : Surreal) : ((Game.neg a) ⊕ a).eq Game.zero := by
  apply Game.eq_trans
  constructor
  · exact Game.add_comm
  · exact Surreal.add_neg a
