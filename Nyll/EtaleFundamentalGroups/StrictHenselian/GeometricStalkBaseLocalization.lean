/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# The ordinary local ring mapping to the actual geometric stalk

For any geometric point of an affine scheme, the structure map factors
through the localization at its actual kernel prime. This factorization
is local, and for a domain base it is injective. No comparison with a
separately postulated strict henselization is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] (φ : R →+* Ω)

/-- The actual prime of the affine base selected by the geometric point. -/
def geometricBasePrime : PrimeSpectrum R :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩

private theorem geometricBaseDenominatorUnit
    (r : (geometricBasePrime φ).asIdeal.primeCompl) :
    IsUnit (geometricStalkStructureMap φ r) := by
  apply geometricStalk_isUnit_of_evaluation_ne_zero
    (Spec.map (CommRingCat.ofHom φ))
  rw [geometricStalkStructureMap_evaluation_apply]
  exact r.property

/-- The actual structure map extended from the affine base to its ordinary local ring. -/
def geometricStalkBaseLocalizationMap :
    Localization.AtPrime (geometricBasePrime φ).asIdeal →+*
      geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
  IsLocalization.lift (S := Localization.AtPrime (geometricBasePrime φ).asIdeal)
    (g := geometricStalkStructureMap φ) (geometricBaseDenominatorUnit φ)

/-- Localization of the base retains its actual structure map on original elements. -/
theorem geometricStalkBaseLocalizationMap_comp :
    (geometricStalkBaseLocalizationMap φ).comp
      (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal)) =
        geometricStalkStructureMap φ :=
  IsLocalization.lift_comp (geometricBaseDenominatorUnit φ)

/-- Pointwise compatibility of the localized base map with the actual structure map. -/
theorem geometricStalkBaseLocalizationMap_apply (r : R) :
    geometricStalkBaseLocalizationMap φ
      (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal) r) =
        geometricStalkStructureMap φ r :=
  RingHom.congr_fun (geometricStalkBaseLocalizationMap_comp φ) r

/-- The map from the ordinary local ring to the geometric stalk is local.
This follows from the localization correspondence on ideals. -/
instance geometricStalkBaseLocalizationMap_isLocalHom :
    IsLocalHom (geometricStalkBaseLocalizationMap φ) := by
  apply ((IsLocalRing.local_hom_TFAE (geometricStalkBaseLocalizationMap φ)).out 5 1).mp
  apply (IsLocalization.orderEmbedding (geometricBasePrime φ).asIdeal.primeCompl
    (Localization.AtPrime (geometricBasePrime φ).asIdeal)).injective
  change ((maximalIdeal (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).comap
      (geometricStalkBaseLocalizationMap φ)).comap
      (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal)) =
    (maximalIdeal (Localization.AtPrime (geometricBasePrime φ).asIdeal)).under R
  rw [Ideal.comap_comap, geometricStalkBaseLocalizationMap_comp,
    IsLocalization.AtPrime.under_maximalIdeal
      (Localization.AtPrime (geometricBasePrime φ).asIdeal)
      (geometricBasePrime φ).asIdeal]
  ext r
  change (¬ IsUnit (geometricStalkStructureMap φ r)) ↔ φ r = 0
  rw [geometricStalk_isUnit_iff, geometricStalkStructureMap_evaluation_apply]
  exact not_ne_iff

/-- For a domain base, the actual ordinary local ring embeds in the geometric stalk. -/
theorem geometricStalkBaseLocalizationMap_injective [IsDomain R] :
    Function.Injective (geometricStalkBaseLocalizationMap φ) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (geometricBasePrime φ).asIdeal.primeCompl
    (geometricStalkBaseLocalizationMap φ)).mpr
  intro x y
  constructor
  · exact congrArg (geometricStalkBaseLocalizationMap φ)
  · intro h
    rw [geometricStalkBaseLocalizationMap_apply,
      geometricStalkBaseLocalizationMap_apply] at h
    exact congrArg (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal))
      (geometricStalkStructureMap_injective_of_isDomain φ h)

/-- The prime selected on an actual neighborhood lies over the actual kernel
prime on the affine base. -/
theorem geometricNeighborhoodPrime_comap_structure
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal.comap
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom) =
        (geometricBasePrime φ).asIdeal := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let β := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  ext r
  change (v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) (β r) = 0 ↔
    φ r = 0
  have h₁ :
      geometricStalkEvaluation s (geometricStalkGerm s V v (β r)) =
        (v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) (β r) :=
    ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s V v) (β r)
  have h₂ : geometricStalkGerm s V v (β r) = geometricStalkStructureMap φ r :=
    RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r
  rw [← h₁, h₂, geometricStalkStructureMap_evaluation_apply]

/-- The actual map between ordinary local rings selected by a pointed
étale neighborhood, constructed by Mathlib's localization functor. -/
def geometricNeighborhoodBaseLocalizationMap
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    Localization.AtPrime (geometricBasePrime φ).asIdeal →+*
      Localization.AtPrime
        (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal :=
  Localization.localRingHom (geometricBasePrime φ).asIdeal
    (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom)
    (geometricNeighborhoodPrime_comap_structure φ V v).symm

/-- The actual neighborhood-localization map is local. -/
instance geometricNeighborhoodBaseLocalizationMap_isLocalHom
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    IsLocalHom (geometricNeighborhoodBaseLocalizationMap φ V v) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- On base elements the localized neighborhood map is the original section map. -/
theorem geometricNeighborhoodBaseLocalizationMap_apply
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
    (r : R) :
    geometricNeighborhoodBaseLocalizationMap φ V v
      (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal) r) =
    algebraMap Γ(V.left, ⊤)
      (Localization.AtPrime
        (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal)
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop) r) :=
  Localization.localRingHom_to_map _ _ _ _ r

/-- Mapping a localized neighborhood into the geometric stalk commutes with
the actual map from the ordinary local ring of the base. -/
theorem geometricNeighborhoodBaseLocalizationMap_germ
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    (geometricStalkLocalizedGerm (Spec.map (CommRingCat.ofHom φ)) V v).comp
      (geometricNeighborhoodBaseLocalizationMap φ V v) =
        geometricStalkBaseLocalizationMap φ := by
  apply IsLocalization.ringHom_ext (geometricBasePrime φ).asIdeal.primeCompl
  ext r
  change geometricStalkLocalizedGerm (Spec.map (CommRingCat.ofHom φ)) V v
      (geometricNeighborhoodBaseLocalizationMap φ V v
        (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal) r)) =
    geometricStalkBaseLocalizationMap φ
      (algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal) r)
  rw [geometricNeighborhoodBaseLocalizationMap_apply, geometricStalkLocalizedGerm_apply,
    geometricStalkBaseLocalizationMap_apply]
  exact RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r

end EtaleFundamentalGroups.StrictHenselian
