/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkBaseLocalization
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalEtaleDVR
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.Ring

/-!
# DVR geometric stalks from the ordinary local ring

The affine base need not be local. If its ordinary local ring at the
chosen point is a DVR, pointed affine neighborhoods have local rings
unramified over that actual DVR. Their unit-power factorizations pass to
the actual geometric stalk through the compatible localized germ maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
  [IsDiscreteValuationRing (Localization.AtPrime (geometricBasePrime φ).asIdeal)]

omit [IsIntegrallyClosed R] in
/-- A uniformizer of the actual ordinary local ring yields unit-power
factorizations in the actual geometric stalk. -/
theorem geometricStalk_exists_unit_mul_baseLocal_uniformizer_pow
    (π : Localization.AtPrime (geometricBasePrime φ).asIdeal) (hπ : Irreducible π)
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : (geometricStalk (Spec.map (CommRingCat.ofHom φ)))ˣ),
      (u : geometricStalk (Spec.map (CommRingCat.ofHom φ))) *
        geometricStalkBaseLocalizationMap φ π ^ n = a := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let P := Localization.AtPrime (geometricBasePrime φ).asIdeal
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, j, hVaffine, hj⟩ := geometricStalk_exists_affine_refinement s W t
  let : IsAffine V.left := hVaffine
  let y : Γ(V.left, ⊤) := j.left.appTop z
  have hy : geometricStalkGerm s V v y = a := by
    have h := (Scheme.pointSmallEtale s).toPresheafFiber_w
      j v (etaleSections (Spec (CommRingCat.of R)))
    have hjStrict : (Scheme.pointSmallEtale s).fiber.map j v = t := hj
    rw [hjStrict] at h
    exact (ConcreteCategory.congr_hom h z).trans hz
  let β : R →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  let : Algebra R Γ(V.left, ⊤) := β.toAlgebra
  have hβ : β.Etale := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
          inferInstance)
    · exact HasRingHomProperty.appTop (P := @Etale)
        (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) inferInstance
  let : Algebra.Etale R Γ(V.left, ⊤) := hβ
  let B := Localization.AtPrime (geometricNeighborhoodPrime s V v).asIdeal
  let ψ : P →+* B := geometricNeighborhoodBaseLocalizationMap φ V v
  let : Algebra P B := ψ.toAlgebra
  have : IsScalarTower R P B :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (geometricNeighborhoodBaseLocalizationMap_apply φ V v r).symm
  have : IsLocalHom (algebraMap P B) :=
    geometricNeighborhoodBaseLocalizationMap_isLocalHom φ V v
  have : Algebra.EssFiniteType P B := Algebra.EssFiniteType.of_comp R P B
  have : Algebra.FormallyUnramified R B :=
    Algebra.FormallyUnramified.comp R Γ(V.left, ⊤) B
  have : Algebra.FormallyUnramified P B :=
    Algebra.FormallyUnramified.of_restrictScalars R P B
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing P B
  let θ : B →+* geometricStalk s := geometricStalkLocalizedGerm s V v
  have hθ : θ.comp (algebraMap P B) = geometricStalkBaseLocalizationMap φ :=
    geometricNeighborhoodBaseLocalizationMap_germ φ V v
  have hyB : algebraMap Γ(V.left, ⊤) B y ≠ 0 := by
    intro hzero
    apply ha
    rw [← hy, ← geometricStalkLocalizedGerm_apply]
    change θ (algebraMap Γ(V.left, ⊤) B y) = 0
    rw [hzero, map_zero]
  obtain ⟨n, u, hu⟩ := exists_unit_mul_pow_of_principal_maximalIdeal (algebraMap P B π)
    (localUnramifiedOverDVR_maximalIdeal P B π hπ) (algebraMap Γ(V.left, ⊤) B y) hyB
  refine ⟨n, Units.map θ.toMonoidHom u, ?_⟩
  change θ (u : B) * geometricStalkBaseLocalizationMap φ π ^ n = a
  have h := congrArg θ hu
  have hπMap : θ (algebraMap P B π) = geometricStalkBaseLocalizationMap φ π :=
    DFunLike.congr_fun hθ π
  rw [map_mul, map_pow, hπMap] at h
  change θ (u : B) * geometricStalkBaseLocalizationMap φ π ^ n =
    geometricStalkLocalizedGerm s V v (algebraMap Γ(V.left, ⊤) B y) at h
  rw [geometricStalkLocalizedGerm_apply, hy] at h
  exact h

omit [IsIntegrallyClosed R] in
/-- The ordinary local uniformizer generates the maximal ideal of the
actual geometric stalk. -/
theorem geometricStalk_maximalIdeal_eq_span_baseLocal_uniformizer
    (π : Localization.AtPrime (geometricBasePrime φ).asIdeal) (hπ : Irreducible π) :
    maximalIdeal (geometricStalk (Spec.map (CommRingCat.ofHom φ))) =
      Ideal.span {geometricStalkBaseLocalizationMap φ π} := by
  classical
  apply le_antisymm
  · intro a ha
    by_cases ha0 : a = 0
    · rw [ha0]
      exact Ideal.zero_mem _
    obtain ⟨n, u, hu⟩ :=
      geometricStalk_exists_unit_mul_baseLocal_uniformizer_pow φ π hπ a ha0
    cases n with
    | zero =>
      have hau : IsUnit a := by
        rw [← hu, pow_zero, mul_one]
        exact u.isUnit
      exact False.elim (ha hau)
    | succ n =>
      apply Ideal.mem_span_singleton.mpr
      refine ⟨(u : geometricStalk (Spec.map (CommRingCat.ofHom φ))) *
        geometricStalkBaseLocalizationMap φ π ^ n, ?_⟩
      rw [← hu, pow_succ]
      ring
  · apply Ideal.span_le.mpr
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    change ¬ IsUnit (geometricStalkBaseLocalizationMap φ π)
    intro hunit
    exact hπ.not_isUnit
      (IsLocalHom.map_nonunit (f := geometricStalkBaseLocalizationMap φ) π hunit)

/-- If the actual ordinary local ring at a point is a DVR, its actual
geometric stalk is a DVR. -/
theorem geometricStalk_isDiscreteValuationRing_of_baseLocalization :
    IsDiscreteValuationRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let P := Localization.AtPrime (geometricBasePrime φ).asIdeal
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P
  have hne : geometricStalkBaseLocalizationMap φ π ≠ 0 := by
    intro hzero
    apply hπ.ne_zero
    apply geometricStalkBaseLocalizationMap_injective φ
    rw [hzero, map_zero]
  have hmax := geometricStalk_maximalIdeal_eq_span_baseLocal_uniformizer φ π hπ
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨geometricStalkBaseLocalizationMap φ π,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmax, ?_⟩
  intro a ha
  obtain ⟨n, u, hu⟩ :=
    geometricStalk_exists_unit_mul_baseLocal_uniformizer_pow φ π hπ a ha
  refine ⟨n, u, ?_⟩
  rw [mul_comm]
  exact hu

end EtaleFundamentalGroups.StrictHenselian
