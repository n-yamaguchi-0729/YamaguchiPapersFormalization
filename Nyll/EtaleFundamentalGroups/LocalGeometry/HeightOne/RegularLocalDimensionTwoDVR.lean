/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Height-one localizations of two-dimensional regular local domains

A two-dimensional regular local domain is integrally closed.  Localizing at
a height-one prime preserves integral closedness and Noetherianity, and the
localized ring has Krull dimension one.  Thus it is a non-field normal
Noetherian local domain with a unique nonzero prime, hence a discrete
valuation ring.

This argument deliberately does not pass through an `IsRegularRing` instance
on the original local ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- The localization of a two-dimensional regular local domain at a
height-one prime is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_isRegularLocalRing_dimension_two
    {D : Type u} [CommRing D] [IsDomain D] [IsRegularLocalRing D]
    (hdim : ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞))
    (q : Ideal D) [q.IsPrime] (hqHeight : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  let V := Localization.AtPrime q
  have hintegrallyClosedD : IsIntegrallyClosed D :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  let : IsIntegrallyClosed D := hintegrallyClosedD
  let : IsNoetherianRing V :=
    IsLocalization.isNoetherianRing q.primeCompl V
      (inferInstance : IsNoetherianRing D)
  have hintegrallyClosedV : IsIntegrallyClosed V :=
    isIntegrallyClosed_of_isLocalization V q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed V := hintegrallyClosedV
  have hqNe : q ≠ ⊥ := by
    intro hq
    have hqZero : q.height = 0 :=
      Ideal.height_eq_zero_iff_eq_bot.mpr hq
    rw [hqHeight] at hqZero
    norm_num at hqZero
  have hnotField : ¬ IsField V :=
    IsLocalization.AtPrime.not_isField D hqNe V
  have hdimV : ringKrullDim V = ((1 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim V = (q.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height q V
      _ = ((1 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hqHeight
  have hkrullDimLE : Ring.KrullDimLE 1 V := by
    rw [Ring.krullDimLE_iff, hdimV]
    exact le_rfl
  have hmaximalOfNonzeroPrime :
      ∀ (Q : Ideal V), Q ≠ ⊥ → Q.IsPrime → Q.IsMaximal :=
    (Ring.krullDimLE_one_iff_of_isPrime_bot.mp hkrullDimLE)
  have huniqueNonzeroPrime :
      ∃! Q : Ideal V, Q ≠ ⊥ ∧ Q.IsPrime := by
    refine ⟨maximalIdeal V, ?_, ?_⟩
    · exact ⟨isField_iff_maximalIdeal_eq.not.mp hnotField, inferInstance⟩
    · intro Q hQ
      exact IsLocalRing.eq_maximalIdeal
        (hmaximalOfNonzeroPrime Q hQ.1 hQ.2)
  have hnormalUnique :
      IsIntegrallyClosed V ∧
        ∃! Q : Ideal V, Q ≠ ⊥ ∧ Q.IsPrime :=
    ⟨hintegrallyClosedV, huniqueNonzeroPrime⟩
  exact ((IsDiscreteValuationRing.TFAE V hnotField).out 1 4).mpr
    hnormalUnique

end EtaleFundamentalGroups

end
