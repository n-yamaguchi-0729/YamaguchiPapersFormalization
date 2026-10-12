/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The zero section of the projective line

Evaluation at zero gives a morphism from `Spec R` to the standard affine
chart of the projective line. The kernel of this evaluation is generated
by the affine coordinate, so its affine image is its zero locus.
The irrelevant-ideal condition puts every projective zero of `T₀` inside
the chart `T₁ ≠ 0`. Thus the image of the actual scheme morphism is exactly
the homogeneous zero locus of `T₀`, over any commutative ring.

This section and its image are used to construct the primitive integral
sections in Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero section, constructed by polynomial evaluation in the standard chart. -/
def zeroSection (R : Type u) [CommRing R] :
    Spec (CommRingCat.of R) ⟶ ProjectiveLine R :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫ standardChartEmbedding R

private theorem standardChartEmbedding_X_zero_mem_iff
    (R : Type u) [CommRing R] (q : PrimeSpectrum (Polynomial R)) :
    MvPolynomial.X (0 : Fin 2) ∈ (standardChartEmbedding R q).asHomogeneousIdeal ↔
      Polynomial.X ∈ q.asIdeal := by
  classical
  apply not_iff_not.mp
  have hpre : standardChartEmbedding R ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X (0 : Fin 2)) = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
    simpa only [linearSectionEquation, map_one, map_zero, one_mul, zero_mul, sub_zero] using
      (standardChartEmbedding_preimage_linearSection (0 : R) 1)
  change q ∈ standardChartEmbedding R ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X (0 : Fin 2)) ↔ q ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)
  rw [hpre]
  exact Iff.rfl

private theorem mem_range_affineZeroSection_iff
    (R : Type u) [CommRing R] (q : PrimeSpectrum (Polynomial R)) :
    q ∈ Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ↔
      Polynomial.X ∈ q.asIdeal := by
  change q ∈ Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) ↔ _
  rw [range_comap_of_surjective R (Polynomial.evalRingHom (0 : R))
      (Polynomial.eval_surjective (0 : R)),
    Polynomial.ker_evalRingHom, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  simp only [Polynomial.C_0, sub_zero]
  exact Iff.rfl

/-- The image of the zero section is exactly its homogeneous linear zero locus. -/
theorem range_zeroSection (R : Type u) [CommRing R] :
    Set.range (zeroSection R) =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        {linearSectionEquation (0 : R) 1} := by
  ext x
  refine Iff.trans ?_ ((ProjectiveSpectrum.mem_zeroLocus
    (MvPolynomial.homogeneousSubmodule (Fin 2) R) x
    {linearSectionEquation (0 : R) 1}).trans Set.singleton_subset_iff).symm
  have hequation : linearSectionEquation (0 : R) 1 = MvPolynomial.X (0 : Fin 2) := by
    simp only [linearSectionEquation, map_one, map_zero, one_mul, zero_mul, sub_zero]
  rw [hequation]
  constructor
  · rintro ⟨q, rfl⟩
    change MvPolynomial.X (0 : Fin 2) ∈
      (standardChartEmbedding R
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) q)).asHomogeneousIdeal
    apply (standardChartEmbedding_X_zero_mem_iff R _).mpr
    exact (mem_range_affineZeroSection_iff R _).mp ⟨q, rfl⟩
  · intro hxzero
    have hxchart : x ∈ infinityComplement R := by
      change MvPolynomial.X (1 : Fin 2) ∉ x.asHomogeneousIdeal
      exact fun hxone => projectiveLine_not_both_coordinates_mem x hxzero hxone
    have hxrange : x ∈ (standardChartEmbedding R).opensRange := by
      rw [standardChartEmbedding_opensRange]
      exact hxchart
    obtain ⟨q, hq⟩ := Scheme.Hom.mem_opensRange.mp hxrange
    have hqzero : Polynomial.X ∈ q.asIdeal :=
      (standardChartEmbedding_X_zero_mem_iff R q).mp (hq.symm ▸ hxzero)
    obtain ⟨z, hz⟩ := (mem_range_affineZeroSection_iff R q).mpr hqzero
    refine ⟨z, ?_⟩
    change standardChartEmbedding R
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) z) = x
    rw [hz]
    exact hq

end ShimizuYamaguchi26BranchedCoverings
