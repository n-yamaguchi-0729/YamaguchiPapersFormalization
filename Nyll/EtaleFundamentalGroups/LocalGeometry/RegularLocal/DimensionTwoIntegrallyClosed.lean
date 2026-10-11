/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightTwo.RegularPair
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularPair.IntegrallyClosed

/-!
# Normality of two-dimensional regular local domains

Mathlib's current definition of a regular ring directly asks for regularity
of every prime localization; it does not yet provide the converse theorem
that a regular local ring is regular.  In dimension two, the explicit
regular-pair construction supplies the normality statement needed by the
generic-component normalization argument without that missing general
localization theorem.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing

universe u

/-- A two-dimensional regular local domain is integrally closed.

The regular pair is produced from a basis of the cotangent space and is not
part of the theorem's input. -/
theorem isIntegrallyClosed_of_isRegularLocalRing_dimension_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞)) :
    IsIntegrallyClosed A := by
  have hfin :
      Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hdim] at hreg
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hreg)
  obtain ⟨x, y, hregular, hspan⟩ :=
    EtaleFundamentalGroups.exists_regular_pair_of_finrank_cotangentSpace_eq_two_unconstrained
      hfin hdim
  exact
    isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
      A x y hregular hspan

/-- Every height-two localization of a regular domain is integrally closed. -/
theorem isIntegrallyClosed_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2) :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  apply isIntegrallyClosed_of_isRegularLocalRing_dimension_two
  calc
    ringKrullDim (Localization.AtPrime P) = (P.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height
        P (Localization.AtPrime P)
    _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
      congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP

end EtaleFundamentalGroups.SpecialLocalPurity

end
