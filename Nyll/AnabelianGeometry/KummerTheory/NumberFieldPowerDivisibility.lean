/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.IntegerCharacters
import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPowerSeparation

/-!
# A uniform divisibility bound for powers of a number-field element

For a fixed non-torsion element a, one positive integer M controls all
relations a^e = d^n in the original number field: n divides eM. A fixed
S-unit group contains both a and every possible d in these relations.
-/

noncomputable section

namespace AnabelianGeometry.KummerTheory

variable {K : Type*} [Field K] [NumberField K]

/-- Powers of one non-torsion number-field element have uniformly bounded
denominators. The witnesses to all power relations are allowed to vary. -/
theorem exists_power_divisibility_bound (a : Kˣ) (ha : ¬ IsOfFinOrder a) :
    ∃ M : ℕ+, ∀ (e : ℤ) (n : ℕ+) (d : Kˣ),
      a ^ e = d ^ (n : ℕ) → (n : ℤ) ∣ e * (M : ℤ) := by
  obtain ⟨T, haT⟩ := exists_sUnitGroup_mem a
  let S : Subgroup Kˣ := SUnitGroup (K := K) T
  have : Group.FG S := GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp (SUnitGroup.moduleFinite (K := K) T))
  let aS : S := ⟨a, haT⟩
  have haS : ¬ IsOfFinOrder aS := by
    intro h
    exact ha (S.subtype.isOfFinOrder h)
  obtain ⟨f, hf⟩ := exists_integer_character_ne_one aS haS
  let z : ℤ := Multiplicative.toAdd (f aS)
  have hz : z ≠ 0 := by
    intro h
    exact hf (Multiplicative.toAdd.injective h)
  refine ⟨⟨z.natAbs, Int.natAbs_pos.mpr hz⟩, ?_⟩
  intro e n d h
  have hdS : d ∈ S :=
    mem_sUnitGroup_of_pow_mem T n d (h ▸ S.zpow_mem haT e)
  let dS : S := ⟨d, hdS⟩
  have hS : aS ^ e = dS ^ (n : ℕ) := Subtype.ext h
  have hd : (n : ℤ) ∣ e * z := integer_character_dvd_of_zpow_eq_pow f aS dS e n hS
  change (n : ℤ) ∣ e * (z.natAbs : ℤ)
  rcases le_total 0 z with hpos | hneg
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hpos] using hd
  · have hd' := dvd_neg.mpr hd
    simpa only [Int.natCast_natAbs, abs_of_nonpos hneg, mul_neg] using hd'

end AnabelianGeometry.KummerTheory
