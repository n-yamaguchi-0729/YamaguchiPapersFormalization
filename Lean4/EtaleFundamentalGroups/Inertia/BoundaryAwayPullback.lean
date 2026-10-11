/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeNormalCrossingsComplementCover
import SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual pullback squares for the boundary-away chart

The complement chart and the principal localization identify the same open
subscheme as the inverse image of the original complement. Their canonical
maps form pullback squares. This identifies the source of a base-changed
relative normalization with the actual finite-etale pullback cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- Pulling back an ideal's support complement is the actual complement square. -/
theorem isPullback_comapSupportComplementTo
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    IsPullback (comapSupportComplementTo I f) (I.comap f).supportComplement.ι
      I.supportComplement.ι f := by
  apply IsOpenImmersion.isPullback
  · exact (comapSupportComplementTo_comp_ι I f).symm
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
      supportComplement_comap]

/-- The principal local boundary complement is the pullback of the global
support complement under the canonical localized-stalk map. -/
theorem isPullback_localizationAwayToSupportComplement
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (a : Localization.AtPrime P)
    (ha : (I.stalkIdeal x).map
      (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)) = Ideal.span {a}) :
    IsPullback (localizationAwayToSupportComplement I x P a ha)
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P) (Localization.Away a))))
      I.supportComplement.ι (Scheme.localizationAtPrimeTo X x P) := by
  apply IsOpenImmersion.isPullback
  · exact (localizationAwayToSupportComplement_comp_ι I x P a ha).symm
  · rw [Scheme.Opens.opensRange_ι,
      Scheme.Hom.opensRange_localizationAway (R := .of (Localization.AtPrime P)) a]
    exact localizationAtPrimeTo_preimage_supportComplement_eq_basicOpen I x P a ha

/-- The composite boundary-away chart has the original support complement
as its base-change square, including its canonical map into that complement. -/
theorem isPullback_boundaryAwayToSupportComplement
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : Spec (Y.presheaf.stalk y)) :
    let : P.asIdeal.IsPrime := P.isPrime
    ∀ {r : ℕ} (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary : ((I.comap f).stalkIdeal y).map
      (algebraMap (Y.presheaf.stalk y) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {EtaleFundamentalGroups.boundaryProduct t r}),
    IsPullback (boundaryAwayToSupportComplement I f y P t hboundary)
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P.asIdeal)
        (Localization.Away (EtaleFundamentalGroups.boundaryProduct t r)))))
      I.supportComplement.ι (Scheme.localizationAtPrimeTo Y y P.asIdeal ≫ f) := by
  intro hP r t hboundary
  exact (isPullback_localizationAwayToSupportComplement (I.comap f) y P.asIdeal
    (EtaleFundamentalGroups.boundaryProduct t r) hboundary).paste_horiz
      (isPullback_comapSupportComplementTo I f)

end AlgebraicGeometry.Scheme.IdealSheafData
