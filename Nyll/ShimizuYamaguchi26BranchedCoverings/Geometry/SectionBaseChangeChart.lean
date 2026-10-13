/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.Tactic.FinCases

/-!
# Coefficient extension on the actual projective coordinate charts

The projective coefficient morphism restricts on both coordinate charts to
polynomial coefficient extension. The proof uses the homogeneous-localization
maps of `ProjectiveSpace.BaseChange` (whose FLT attribution is retained there),
the actual chart isomorphism, and the functoriality of `Proj.map`. The swap of
homogeneous coordinates commutes with coefficient extension.

These identities connect pullbacks of the original section ideals to their
actual polynomial equations over the new coefficient ring, as required in
Shimizu and Yamaguchi, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem standardChartEquiv_map
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (awayMapX R S 1 (1 : Fin 2)).comp (standardChartEquiv R).toRingHom =
      (standardChartEquiv S).toRingHom.comp (Polynomial.mapRingHom (algebraMap R S)) := by
  apply Polynomial.ringHom_ext
  · intro r
    change awayMapX R S 1 (1 : Fin 2) (standardChartEquiv R (Polynomial.C r)) =
      standardChartEquiv S (Polynomial.map (algebraMap R S) (Polynomial.C r))
    rw [Polynomial.map_C, ← Polynomial.algebraMap_eq, (standardChartEquiv R).commutes,
      ← Polynomial.algebraMap_eq, (standardChartEquiv S).commutes]
    exact DFunLike.congr_fun (awayMapX_algebraMap R S 1 (1 : Fin 2)) r
  · change awayMapX R S 1 (1 : Fin 2) (standardChartEquiv R Polynomial.X) =
      standardChartEquiv S (Polynomial.map (algebraMap R S) Polynomial.X)
    rw [standardChartEquiv_X, Polynomial.map_X, standardChartEquiv_X,
      awayMapX_ratio]

private theorem standardChartEquiv_symm_map
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (standardChartEquiv S).symm.toRingHom.comp (awayMapX R S 1 (1 : Fin 2)) =
      (Polynomial.mapRingHom (algebraMap R S)).comp (standardChartEquiv R).symm.toRingHom := by
  apply RingHom.ext
  intro x
  apply (standardChartEquiv S).injective
  change standardChartEquiv S ((standardChartEquiv S).symm (awayMapX R S 1 1 x)) =
    standardChartEquiv S (Polynomial.map (algebraMap R S) ((standardChartEquiv R).symm x))
  rw [AlgEquiv.apply_symm_apply]
  have h : awayMapX R S 1 (1 : Fin 2)
      (standardChartEquiv R ((standardChartEquiv R).symm x)) =
      standardChartEquiv S
        (Polynomial.map (algebraMap R S) ((standardChartEquiv R).symm x)) :=
    DFunLike.congr_fun (standardChartEquiv_map R S) ((standardChartEquiv R).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

/-- Polynomial coefficient extension is the restriction of the actual projective
coefficient map to the standard chart. -/
theorem standardChartEmbedding_comp_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    standardChartEmbedding S ≫ ProjSpace.map R S 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R S))) ≫
        standardChartEmbedding R := by
  have haway :
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) S)
          (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one S 1 1) one_pos ≫
        ProjSpace.map R S 1 =
      Spec.map (CommRingCat.ofHom (awayMapX R S 1 (1 : Fin 2))) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) R)
          (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1) one_pos := by
    have htransport : ∀ {y : MvPolynomial (Fin 2) S}
        (h : ProjSpace.mvMapGraded R S 1 (MvPolynomial.X (1 : Fin 2)) = y)
        (hy : y ∈ MvPolynomial.homogeneousSubmodule (Fin 2) S 1),
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) S) y hy one_pos ≫
            ProjSpace.map R S 1 =
          Spec.map (CommRingCat.ofHom
              (h ▸ HomogeneousLocalization.Away.map (ProjSpace.mvMapGraded R S 1)
                (MvPolynomial.X (1 : Fin 2)))) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) R)
              (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1) one_pos := by
      intro y h hy
      subst h
      exact Proj.awayι_comp_map (ProjSpace.mvMapGraded R S 1)
        (ProjSpace.irrelevant_le_map_mvMapGraded R S 1) one_pos
        (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1)
    exact htransport (ProjSpace.mvMapGraded_X R S 1 (1 : Fin 2))
      (ProjSpace.X_mem_one S 1 1)
  change (Spec.map (CommRingCat.ofHom (standardChartEquiv S).symm.toRingHom) ≫ _) ≫ _ =
    _ ≫ (Spec.map (CommRingCat.ofHom (standardChartEquiv R).symm.toRingHom) ≫ _)
  rw [Category.assoc, haway, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, standardChartEquiv_symm_map]

private theorem coordinateSwapSubstitution_map
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (bezoutCoordinateSubstitution (0 : S) 1 0 1).comp (ProjSpace.mvMapGraded R S 1) =
      (ProjSpace.mvMapGraded R S 1).comp (bezoutCoordinateSubstitution (0 : R) 1 0 1) := by
  apply GradedRingHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change bezoutCoordinateSubstitution (0 : S) 1 0 1
        (MvPolynomial.map (algebraMap R S) (MvPolynomial.C r)) =
      MvPolynomial.map (algebraMap R S)
        (bezoutCoordinateSubstitution (0 : R) 1 0 1 (MvPolynomial.C r))
    rw [MvPolynomial.map_C, bezoutCoordinateSubstitution_C,
      bezoutCoordinateSubstitution_C, MvPolynomial.map_C]
  · intro j
    fin_cases j
    · change bezoutCoordinateSubstitution (0 : S) 1 0 1
          (ProjSpace.mvMapGraded R S 1 (MvPolynomial.X (0 : Fin 2))) =
        ProjSpace.mvMapGraded R S 1
          (bezoutCoordinateSubstitution (0 : R) 1 0 1 (MvPolynomial.X (0 : Fin 2)))
      rw [ProjSpace.mvMapGraded_X, bezoutCoordinateSubstitution_X_zero,
        bezoutCoordinateSubstitution_X_zero]
      simp only [map_zero, map_one, zero_mul, one_mul, zero_add, ProjSpace.mvMapGraded_X]
    · change bezoutCoordinateSubstitution (0 : S) 1 0 1
          (ProjSpace.mvMapGraded R S 1 (MvPolynomial.X (1 : Fin 2))) =
        ProjSpace.mvMapGraded R S 1
          (bezoutCoordinateSubstitution (0 : R) 1 0 1 (MvPolynomial.X (1 : Fin 2)))
      rw [ProjSpace.mvMapGraded_X, bezoutCoordinateSubstitution_X_one,
        bezoutCoordinateSubstitution_X_one]
      simp only [linearSectionEquation, map_zero, map_one, zero_mul, one_mul,
        sub_zero, ProjSpace.mvMapGraded_X]

/-- Swapping the two actual homogeneous coordinates commutes with extension
of the coefficient ring. -/
theorem projectiveCoordinateSwap_comp_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (projectiveCoordinateSwap S).hom ≫ ProjSpace.map R S 1 =
      ProjSpace.map R S 1 ≫ (projectiveCoordinateSwap R).hom := by
  change Proj.map (bezoutCoordinateSubstitution (0 : S) 1 0 1) _ ≫
      Proj.map (ProjSpace.mvMapGraded R S 1) _ =
    Proj.map (ProjSpace.mvMapGraded R S 1) _ ≫
      Proj.map (bezoutCoordinateSubstitution (0 : R) 1 0 1) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [coordinateSwapSubstitution_map]

/-- On the infinity chart, the actual projective coefficient map is the
spectrum of polynomial coefficient extension. -/
theorem infinityChartEmbedding_comp_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    infinityChartEmbedding S ≫ ProjSpace.map R S 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R S))) ≫
        infinityChartEmbedding R := by
  rw [infinityChartEmbedding, Category.assoc, projectiveCoordinateSwap_comp_baseChange,
    ← Category.assoc, standardChartEmbedding_comp_baseChange, Category.assoc,
    infinityChartEmbedding]

end ShimizuYamaguchi26BranchedCoverings
