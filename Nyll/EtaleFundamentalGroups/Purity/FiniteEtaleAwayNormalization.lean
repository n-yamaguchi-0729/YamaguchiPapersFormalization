/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.RegularBoundaryPurity
import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleAwayNormalizationAction
import Nyll.SchemeTheory.Etale.AffineBaseChangeProperties
import Mathlib.RingTheory.RingHom.Etale

/-!
# Purity for the actual normalization of a cover of a principal open

Off the principal boundary, normalization recovers the given finite etale
cover. At boundary primes of height one, the hypothesis is a property of the
actual scheme base change. The canonical function-field comparison turns
these into the local hypotheses of purity, with regularity required only
along the boundary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups

universe u

private theorem isEtaleAt_of_awayMap_etale
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (d : R) (h : (Localization.awayMap (algebraMap R B) d).Etale)
    (P : PrimeSpectrum B) (hdP : algebraMap R B d ∉ P.asIdeal) :
    Algebra.IsEtaleAt R P.asIdeal := by
  have hcomp : ((Localization.awayMap (algebraMap R B) d).comp
      (algebraMap R (Localization.Away d))).Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway d)) h
  have heq : (Localization.awayMap (algebraMap R B) d).comp
      (algebraMap R (Localization.Away d)) =
        algebraMap R (Localization.Away (algebraMap R B d)) := by
    ext r
    change IsLocalization.Away.map _ _ (algebraMap R B) d
      (algebraMap R (Localization.Away d) r) = _
    rw [IsLocalization.Away.map, IsLocalization.map_eq,
      IsScalarTower.algebraMap_apply R B (Localization.Away (algebraMap R B d))]
  rw [heq] at hcomp
  let : Algebra.Etale R (Localization.Away (algebraMap R B d)) :=
    RingHom.etale_algebraMap.mp hcomp
  exact Algebra.basicOpen_subset_etaleLocus_iff.mpr
    (inferInstance : Algebra.FormallyEtale R (Localization.Away (algebraMap R B d))) hdP

/-- A connected finite etale cover of a principal open has etale relative
normalization if the base is regular along the boundary and its actual
normalization is etale over every boundary prime of height one. -/
theorem finiteEtaleAway_normalization_etale_of_regular_boundary
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    (d : R) (hd : d ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away d)))) [IsConnected Y]
    (hregular : ∀ p : PrimeSpectrum R, d ∈ p.asIdeal →
      IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (hheightOne : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → d ∈ p →
      Etale (pullback.snd
        ((show Y.left ⟶ Spec (.of (Localization.Away d)) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d)))).fromNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    Etale ((show Y.left ⟶ Spec (.of (Localization.Away d)) from Y.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d)))).fromNormalization := by
  let S := Localization.Away d
  let : IsDomain S := IsLocalization.Away.isDomain S hd
  let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S
    (Submonoid.powers d)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd))
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ Spec (.of S) from Y.hom)
  let f : Y.left ⟶ Spec (.of R) :=
    (show Y.left ⟶ Spec (.of S) from Y.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  let K := (Spec (.of S)).functionField
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R K := localizationAwaySpecFunctionFieldAlgebra d hd
  let : Algebra R L := finiteEtaleAwayFunctionFieldAlgebra d hd Y
  have hAlg := finiteEtaleAwayFunctionFieldAlgebra_eq_affineMorphism d hd Y
  have hcompare : ∃ e : f.normalization ≅ Spec (.of (integralClosure R L)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) =
        f.fromNormalization := by
    change (letI : Algebra R L := finiteEtaleAwayFunctionFieldAlgebra d hd Y
      ∃ e : f.normalization ≅ Spec (.of (integralClosure R L)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) =
          f.fromNormalization)
    rw [hAlg]
    exact ⟨affineMorphismFunctionFieldNormalizationIso R f,
      affineMorphismFunctionFieldNormalizationIso_hom_base R f⟩
  obtain ⟨e, he⟩ := hcompare
  let : IsFractionRing R K := localizationAwaySpecFunctionField_isFractionRing d hd
  let : IsScalarTower R K L := finiteEtaleAway_functionField_isScalarTower d hd Y
  let : FiniteDimensional K L := finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : Algebra.IsSeparable K L := isSeparable_functionField_of_finiteEtale_isConnected Y
  have haway : (Localization.awayMap (algebraMap R (integralClosure R L)) d).Etale :=
    localization_away_integralClosure_functionField_etale_of_finiteEtale d hd Y
  have hEt : Algebra.Etale R (integralClosure R L) := by
    apply SpecialLocalPurity.integralClosure_etale_of_regular_boundary (K := K)
      {p | d ∈ p.asIdeal} hregular
    · intro P hP
      exact isEtaleAt_of_awayMap_etale d haway P hP
    · intro p _ hp P _ _
      by_cases hdp : d ∈ p
      · let b := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
        let g := Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))
        have hN : Etale (pullback.snd f.fromNormalization b) := hheightOne p hp hdp
        let l := pullback.map f.fromNormalization b g b e.hom (𝟙 _) (𝟙 _)
          ((Category.comp_id _).trans he.symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
        have hl : l ≫ pullback.snd g b = pullback.snd f.fromNormalization b :=
          (pullback.lift_snd _ _ _).trans (Category.comp_id _)
        have hG : Etale (pullback.snd g b) := by
          let : Etale (pullback.snd f.fromNormalization b) := hN
          have ht : Etale (inv l ≫ pullback.snd f.fromNormalization b) := inferInstance
          rw [← hl, IsIso.inv_hom_id_assoc] at ht
          exact ht
        apply SchemeTheory.isEtaleAt_of_spec_baseChange_atPrime R (integralClosure R L)
          ⟨p, inferInstance⟩ hG ⟨P, inferInstance⟩
        apply PrimeSpectrum.ext
        exact (Ideal.over_def P p).symm
      · apply isEtaleAt_of_awayMap_etale d haway ⟨P, inferInstance⟩
        intro hdP
        apply hdp
        have hdUnder : d ∈ P.under R := hdP
        rw [← Ideal.over_def P p] at hdUnder
        exact hdUnder
  have hSpec : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hEt)
  have hcomp : Etale (e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) := inferInstance
  rw [he] at hcomp
  exact hcomp

end EtaleFundamentalGroups
