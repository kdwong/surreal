import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal
import Surreal.addition

-------------------------------------------
---------- Definition of a*b --------------
-------------------------------------------
def Game.mul : Game → Game → Game
  | x, y =>
  match hx : x, hy : y with
  | mk XL XR, mk YL YR =>
  let L :=
    List.zipWith (fun ⟨xl, _hxl⟩ ⟨yl, _hyl⟩ =>
      ((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg) XL.attach YL.attach ++
    List.zipWith (fun ⟨xr, _hxr⟩ ⟨yr, _hyr⟩ =>
      ((xr.mul y).add (x.mul yr)).add (xr.mul yr).neg) XR.attach YR.attach
  let R :=
    List.zipWith (fun ⟨xl, _hxl⟩ ⟨yr, _hyr⟩ =>
      ((xl.mul y).add (x.mul yr)).add (xl.mul yr).neg) XL.attach YR.attach ++
    List.zipWith (fun ⟨xr, _hxr⟩ ⟨yl, _hyl⟩ =>
      ((xr.mul y).add (x.mul yl)).add (xr.mul yl).neg) XR.attach YL.attach
  Game.mk L R
  termination_by x y => Game.birthday x + Game.birthday y
  decreasing_by
  -- =================================================
  -- First zipwith
  -- =================================================
  -- 1. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [hy] using hmeasure

  -- 2. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [hx] using hmeasure

  -- 3. xl * yl
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : xl.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyl_lt
    assumption

  -- =================================================
  -- Second zipwith
  -- =================================================

  -- 4. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [hy] using hmeasure

  -- 5. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [hx] using hmeasure

  -- 6. xr * yr
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : xr.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyr_lt
    assumption

  -- =================================================
  -- Third zipwith
  -- =================================================

  -- 7. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [hy] using hmeasure

  -- 8. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [hx] using hmeasure

  -- 9. xl * yr
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (mk XL XR) xl (by simpa [Game.left] using _hxl)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (mk YL YR) yr (by simpa [Game.right] using _hyr)
    have hmeasure : xl.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyr_lt
    assumption

  -- =================================================
  -- Fourth Zipwith
  -- =================================================

  -- 10. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [hy] using hmeasure

  -- 11. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [hx] using hmeasure

  -- 12. xr * yl
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (mk XL XR) xr (by simpa [Game.right] using _hxr)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (mk YL YR) yl (by simpa [Game.left] using _hyl)
    have hmeasure : xr.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyl_lt
    assumption
