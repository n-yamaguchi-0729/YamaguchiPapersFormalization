/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ClosedImmersionLift
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The actual integral section in the infinity chart

When the first primitive coordinate is a unit in a reduced coefficient ring,
its inverse times the second coordinate gives a concrete affine coordinate.
Evaluation at this value, followed by the infinity chart of the integral
projective line, has image contained in the original integral section.
The reduced-source factorization theorem for closed immersions and the
terminal property of `Spec ℤ` identify these actual scheme morphisms.

This supplies the coordinate description of the original section needed
for the local ideal calculation in Lemma 2.3 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The corresponding stalk-ideal and intersection-length comparisons remain
separate statements.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The concrete infinity-chart coordinate when the first coordinate is a unit. -/
def integralSectionChartCoordinate (R : Type) [CommRing R] (u v : ℤ)
    (hu : IsUnit (u : R)) : R :=
  (↑(hu.unit⁻¹) : R) * (v : R)

/-- Restricting the actual integral section to a reduced coefficient ring
agrees with evaluation at its concrete infinity-chart coordinate. -/
theorem integralSection_eq_infinityChart
    (R : Type) [CommRing R] [_root_.IsReduced R]
    (u v a b : ℤ) (hab : a * u + b * v = 1) (hu : IsUnit (u : R)) :
    Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) ≫ integralSection u v a b hab =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap ℤ R)
        (integralSectionChartCoordinate R u v hu))) ≫ infinityChartEmbedding ℤ := by
  let c : R := integralSectionChartCoordinate R u v hu
  let ev : ℤ[X] →+* R := Polynomial.eval₂RingHom (algebraMap ℤ R) c
  let f : Spec (CommRingCat.of R) ⟶ ProjectiveLine ℤ :=
    Spec.map (CommRingCat.ofHom ev) ≫ infinityChartEmbedding ℤ
  have huc : (u : R) * c = (v : R) := by
    change (u : R) * ((↑(hu.unit⁻¹) : R) * (v : R)) = (v : R)
    rw [← mul_assoc, hu.mul_val_inv, one_mul]
  have heval : ev (Polynomial.C v - Polynomial.C u * Polynomial.X) = 0 := by
    simp only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
      algebraMap_int_eq, Int.coe_castRingHom, huc, sub_self]
  have hrange : Set.range f ⊆ Set.range (integralSection u v a b hab) := by
    rw [range_integralSection]
    rintro y ⟨x, rfl⟩
    apply (ProjectiveSpectrum.mem_zeroLocus
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (f x) {linearSectionEquation u v}).mpr
    apply Set.singleton_subset_iff.mpr
    change linearSectionEquation u v ∈
      (infinityChartEmbedding ℤ (Spec.map (CommRingCat.ofHom ev) x)).asHomogeneousIdeal
    apply (infinityChartEmbedding_linearSection_mem_iff u v
      (Spec.map (CommRingCat.ofHom ev) x)).mpr
    change ev (Polynomial.C v - Polynomial.C u * Polynomial.X) ∈ x.asIdeal
    rw [heval]
    exact Ideal.zero_mem _
  obtain ⟨g, hg⟩ :=
    IsClosedImmersion.exists_lift_of_isReduced_of_range_subset
      (integralSection u v a b hab) f hrange
  have hg_eq : g = Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) :=
    specZIsTerminal.hom_ext _ _
  rw [hg_eq] at hg
  exact hg

end ShimizuYamaguchi26BranchedCoverings
