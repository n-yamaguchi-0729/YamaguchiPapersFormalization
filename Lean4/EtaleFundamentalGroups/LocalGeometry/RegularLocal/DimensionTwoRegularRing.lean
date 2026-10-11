/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RegularLocalRing.Defs
import EtaleFundamentalGroups.LocalGeometry.HeightOne.RegularLocalDimensionTwoDVR

/-!
# Two-dimensional regular local domains are regular rings

Mathlib defines a regular ring through regularity at every prime and does not
yet contain the general theorem that a regular local ring is a regular ring.
In the two-dimensional domain case needed here, the missing localization
statement follows directly from the prime-height trichotomy: the generic
point is a field, every nonmaximal nonzero prime has height one and hence a
DVR localization, and localization at the maximal ideal is the original
regular local ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A two-dimensional regular local domain is regular at every prime. -/
theorem isRegularRing_of_isRegularLocalRing_dimension_two
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p hp
  by_cases hpBot : p = ⊥
  · subst p
    let : Field (Localization.AtPrime (⊥ : Ideal R)) :=
      IsField.toField (by
        simp [isField_iff_maximalIdeal_eq,
          ← Localization.AtPrime.map_eq_maximalIdeal])
    infer_instance
  by_cases hpMax : p = IsLocalRing.maximalIdeal R
  · subst p
    let e : R ≃ₐ[R]
        Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
      IsLocalization.atUnits R
        (IsLocalRing.maximalIdeal R).primeCompl
        (fun x ↦ by simpa using! fun a ↦ a)
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  · have hpLe : p ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime p
    have hpLt : p < IsLocalRing.maximalIdeal R :=
      lt_of_le_of_ne hpLe hpMax
    have hMaxHeight :
        (IsLocalRing.maximalIdeal R).height = (2 : ℕ∞) := by
      have hMaxHeightCast :
          (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) =
            ((2 : ℕ∞) : WithBot ℕ∞) := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
      exact WithBot.coe_eq_coe.mp hMaxHeightCast
    have hpHeightLt : p.height < (2 : ℕ∞) := by
      rw [← hMaxHeight]
      exact Ideal.height_strict_mono_of_isPrime_of_isPrime hpLt
    have hpHeightLe : p.height ≤ (1 : ℕ∞) := by
      rw [← ENat.lt_add_one_iff ENat.one_ne_top,
        one_add_one_eq_two]
      exact hpHeightLt
    have hpHeightPos : (1 : ℕ∞) ≤ p.height :=
      Order.one_le_iff_ne_zero.mpr
        (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpBot)
    have hpHeight : p.height = 1 :=
      le_antisymm hpHeightLe hpHeightPos
    let : IsDiscreteValuationRing (Localization.AtPrime p) :=
      isDiscreteValuationRing_localizationAtPrime_of_isRegularLocalRing_dimension_two
        hdim p hpHeight
    infer_instance

end EtaleFundamentalGroups

end
