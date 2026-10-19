/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Away.TensorBaseChange

/-!
# Transport of a literal Away map along an algebra equivalence

The chosen Tag factor and the root-refined normalization factor are related
by an algebra equivalence.  This file records the formal transport needed to
keep the literal Away map while changing between those two carriers.

No etaleness of either unlocalized carrier is used.  The proof regards an
algebra equivalence as the right edge of a pushout and applies the literal
Away base-change theorem.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uC uD₀ uD₁

/-- A literal etale Away map is invariant under an equivalence of its target
as an algebra over the base. -/
theorem localization_awayMap_etale_of_algEquiv
    {A : Type uA} {D₀ : Type uD₀} {D₁ : Type uD₁}
    [CommRing A] [CommRing D₀] [CommRing D₁]
    [Algebra A D₀] [Algebra A D₁]
    (E : D₀ ≃ₐ[A] D₁) (f : A)
    (hAway :
      (Localization.awayMap (algebraMap A D₀) f).Etale) :
    (Localization.awayMap (algebraMap A D₁) f).Etale := by
  let dAlgebra : Algebra D₀ D₁ := E.toRingHom.toAlgebra
  let : IsScalarTower A D₀ D₁ :=
    IsScalarTower.of_algebraMap_eq'
      E.toAlgHom.comp_algebraMap.symm
  let : Algebra.IsPushout A D₀ A D₁ :=
    Algebra.IsPushout.of_bijective_right D₀ D₁ E.bijective
  simpa only [Algebra.algebraMap_self_apply] using
    (localization_awayMap_etale_of_isPushout
      (A := A) (B := D₀) (C := A) (D := D₁) f hAway)

/-- An equivalence of the source transports a literal etale Away map to
its composite over the original scalar ring. -/
theorem localization_awayMap_etale_of_source_algEquiv
    {A : Type uA} {C : Type uC} {D : Type uD₀}
    [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
    (E : A ≃ₐ[A] C) (f : A)
    (hAway :
      (Localization.awayMap (algebraMap C D) (algebraMap A C f)).Etale) :
    (Localization.awayMap (algebraMap A D) f).Etale := by
  let : Algebra C A := E.symm.toRingHom.toAlgebra
  let : IsScalarTower C A D := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap C D x = algebraMap A D (E.symm x)
    have hE : algebraMap A C (E.symm x) = E (E.symm x) := by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
        (E.commutes (E.symm x)).symm
    calc
      algebraMap C D x =
          algebraMap C D (algebraMap A C (E.symm x)) :=
        congrArg (algebraMap C D) (hE.trans (E.apply_symm_apply x)).symm
      _ = algebraMap A D (E.symm x) :=
        (IsScalarTower.algebraMap_apply A C D (E.symm x)).symm
  let : Algebra.IsPushout C D A D :=
    Algebra.IsPushout.of_bijective_left A D E.symm.bijective
  have hBack := localization_awayMap_etale_of_isPushout
    (A := C) (B := D) (C := A) (D := D) (algebraMap A C f) hAway
  have hf : algebraMap C A (algebraMap A C f) = f := by
    change E.symm (algebraMap A C f) = f
    have hE : E f = algebraMap A C f := by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using E.commutes f
    rw [← hE, E.symm_apply_apply]
  rw [hf] at hBack
  exact hBack

/-- A target equivalence over an intermediate algebra transports the literal
Away map over the original base, provided both target actions are the actual
scalar-tower composites. -/
theorem localization_awayMap_etale_of_tower_algEquiv
    {A : Type uA} {C : Type uC}
    {D₀ : Type uD₀} {D₁ : Type uD₁}
    [CommRing A] [CommRing C] [CommRing D₀] [CommRing D₁]
    [Algebra A C]
    [Algebra C D₀] [Algebra C D₁]
    [Algebra A D₀] [Algebra A D₁]
    [IsScalarTower A C D₀] [IsScalarTower A C D₁]
    (E : D₀ ≃ₐ[C] D₁) (f : A)
    (hAway :
      (Localization.awayMap (algebraMap A D₀) f).Etale) :
    (Localization.awayMap (algebraMap A D₁) f).Etale := by
  let Ebase : D₀ ≃ₐ[A] D₁ := E.restrictScalars A
  exact localization_awayMap_etale_of_algEquiv Ebase f hAway

end EtaleFundamentalGroups

end
