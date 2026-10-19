/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVRAtPrime
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# The actual geometric étale stalk of a DVR is a DVR

These are the local-base corollaries of the ordinary-local-ring result.
The factorization and maximal-ideal proofs are shared with arbitrary
affine bases rather than repeated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

private def geometricBaseLocalizationEquivOfLocal :
    R ≃ₐ[R] Localization.AtPrime (geometricBasePrime φ).asIdeal :=
  IsLocalization.atUnits R (geometricBasePrime φ).asIdeal.primeCompl
    (S := Localization.AtPrime (geometricBasePrime φ).asIdeal) (by
      intro r hr
      change IsUnit r
      have hrφ : φ r ≠ 0 := hr
      exact IsLocalHom.map_nonunit (f := φ) r (isUnit_iff_ne_zero.mpr hrφ))

/-- Every nonzero germ is a unit times a power of the image of any chosen
base uniformizer, by the shared ordinary-local-ring factorization. -/
theorem geometricStalk_exists_unit_mul_uniformizer_pow
    (π : R) (hπ : Irreducible π)
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : (geometricStalk (Spec.map (CommRingCat.ofHom φ)))ˣ),
      (u : geometricStalk (Spec.map (CommRingCat.ofHom φ))) *
        geometricStalkStructureMap φ π ^ n = a := by
  let P := Localization.AtPrime (geometricBasePrime φ).asIdeal
  have : IsDiscreteValuationRing P :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (geometricBaseLocalizationEquivOfLocal φ)
  have hπP : Irreducible (algebraMap R P π) :=
    (MulEquiv.irreducible_iff (geometricBaseLocalizationEquivOfLocal φ)).mpr hπ
  obtain ⟨n, u, hu⟩ :=
    geometricStalk_exists_unit_mul_baseLocal_uniformizer_pow φ
      (algebraMap R P π) hπP a ha
  refine ⟨n, u, ?_⟩
  simpa only [P, geometricStalkBaseLocalizationMap_apply] using hu

/-- A base uniformizer generates the maximal ideal of the actual geometric
étale stalk. -/
theorem geometricStalk_maximalIdeal_eq_span_uniformizer (π : R) (hπ : Irreducible π) :
    maximalIdeal (geometricStalk (Spec.map (CommRingCat.ofHom φ))) =
      Ideal.span {geometricStalkStructureMap φ π} := by
  let P := Localization.AtPrime (geometricBasePrime φ).asIdeal
  have : IsDiscreteValuationRing P :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (geometricBaseLocalizationEquivOfLocal φ)
  have hπP : Irreducible (algebraMap R P π) :=
    (MulEquiv.irreducible_iff (geometricBaseLocalizationEquivOfLocal φ)).mpr hπ
  simpa only [P, geometricStalkBaseLocalizationMap_apply] using
    geometricStalk_maximalIdeal_eq_span_baseLocal_uniformizer φ
      (algebraMap R P π) hπP

/-- The actual geometric étale stalk over a closed geometric point of a DVR
is itself a DVR, by the actual ordinary-local-ring criterion. -/
instance geometricStalk_isDiscreteValuationRing :
    IsDiscreteValuationRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  have : IsDiscreteValuationRing (Localization.AtPrime (geometricBasePrime φ).asIdeal) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (geometricBaseLocalizationEquivOfLocal φ)
  exact geometricStalk_isDiscreteValuationRing_of_baseLocalization φ

end EtaleFundamentalGroups.StrictHenselian
