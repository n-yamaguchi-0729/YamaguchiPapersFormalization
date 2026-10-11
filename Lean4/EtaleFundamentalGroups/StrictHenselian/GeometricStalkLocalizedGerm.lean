/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic


/-!
# Localized neighborhood rings mapping to the geometric étale stalk

On an actual pointed étale neighborhood, take the prime ideal given by the
kernel of evaluation in the geometric field. Every section outside this ideal
has an invertible germ. The universal property of localization therefore
constructs a map from the actual local ring of sections at this prime to the
geometric stalk. This map is local, as follows from the criterion for a fraction
to be a unit in a localization at a prime.

This supplies the local-stage maps needed to transfer local algebra from
affine étale neighborhoods. No local-stage map or comparison is postulated.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (W : S.Etale)
  (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)

/-- The actual prime of the neighborhood's ring of sections selected by its
given geometric point. -/
def geometricNeighborhoodPrime : PrimeSpectrum Γ(W.left, ⊤) :=
  ⟨RingHom.ker (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom,
    RingHom.ker_isPrime _⟩

/-- A denominator outside the selected prime has an invertible germ. -/
theorem geometricStalkGerm_isUnit_of_mem_primeCompl
    (a : (geometricNeighborhoodPrime s W t).asIdeal.primeCompl) :
    IsUnit (geometricStalkGerm s W t a) := by
  apply geometricStalk_isUnit_of_evaluation_ne_zero s
  have ha := a.property
  change (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom (a : Γ(W.left, ⊤)) ≠ 0 at ha
  intro hzero
  apply ha
  exact (ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s W t) a).symm.trans hzero

/-- The actual local ring of sections at the chosen point maps to the geometric
stalk by localization of the germ map. -/
def geometricStalkLocalizedGerm :
    Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal →+* geometricStalk s :=
  IsLocalization.lift (S := Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal)
    (g := (geometricStalkGerm s W t).hom)
    (geometricStalkGerm_isUnit_of_mem_primeCompl s W t)

/-- The map from the local ring extends the original section germ map. -/
theorem geometricStalkLocalizedGerm_comp :
    (geometricStalkLocalizedGerm s W t).comp
      (algebraMap Γ(W.left, ⊤)
        (Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal)) =
      (geometricStalkGerm s W t).hom :=
  IsLocalization.lift_comp (geometricStalkGerm_isUnit_of_mem_primeCompl s W t)

/-- On an ordinary section the localized germ is its original germ. -/
theorem geometricStalkLocalizedGerm_apply (a : Γ(W.left, ⊤)) :
    geometricStalkLocalizedGerm s W t
      (algebraMap Γ(W.left, ⊤)
        (Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal) a) =
      geometricStalkGerm s W t a :=
  RingHom.congr_fun (geometricStalkLocalizedGerm_comp s W t) a

/-- The localized germ map is local: a fraction with unit germ has a numerator
outside the prime selected by the geometric point. -/
instance geometricStalkLocalizedGerm_isLocalHom :
    IsLocalHom (geometricStalkLocalizedGerm s W t) where
  map_nonunit z hz := by
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq
      (geometricNeighborhoodPrime s W t).asIdeal.primeCompl z
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul,
      geometricStalkLocalizedGerm_apply] at hz
    have haunit : IsUnit (geometricStalkGerm s W t a) := isUnit_of_mul_isUnit_left hz
    apply (IsLocalization.AtPrime.isUnit_mk'_iff
      (Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal)
      (geometricNeighborhoodPrime s W t).asIdeal a b).mpr
    change (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom a ≠ 0
    intro ha
    apply (haunit.map (geometricStalkEvaluation s).hom).ne_zero
    exact (ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s W t) a).trans ha

end EtaleFundamentalGroups.StrictHenselian
