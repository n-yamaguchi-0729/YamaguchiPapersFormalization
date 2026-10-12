/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Set.Insert
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Homogeneous supports of rational sections

The support is the actual homogeneous zero locus of the primitive equation
`v*T₀-u*T₁` in the integral projective line. Pulling it back along the
coefficient morphism computes the same equation over the new coefficient
ring. This supplies one common geometric definition for Lemmas 2.3 and 2.4
of Shimizu and Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The support of the integral section with the given rational projective point,
as the zero locus of its primitive homogeneous equation. -/
def rationalSectionSupport (a : Projectivization ℚ (ℚ × ℚ)) :
    Set (ProjectiveLine ℤ) :=
  ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    {linearSectionEquation (rationalPointNumerator a) (rationalPointDenominator a)}

/-- The coefficient morphism pulls a rational section support back to the
zero locus of its primitive equation over the new ring. -/
theorem mem_rationalSectionSupport_baseChange_iff (R : Type) [CommRing R]
    (a : Projectivization ℚ (ℚ × ℚ)) (x : ProjectiveLine R) :
    (ProjSpace.map ℤ R 1) x ∈ rationalSectionSupport a ↔
      linearSectionEquation (rationalPointNumerator a : R)
        (rationalPointDenominator a : R) ∈ x.asHomogeneousIdeal := by
  refine (ProjectiveSpectrum.mem_zeroLocus
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) ((ProjSpace.map ℤ R 1) x)
    {linearSectionEquation (rationalPointNumerator a) (rationalPointDenominator a)}).trans ?_
  rw [Set.singleton_subset_iff]
  change MvPolynomial.map (algebraMap ℤ R)
      (linearSectionEquation (rationalPointNumerator a) (rationalPointDenominator a)) ∈
        x.asHomogeneousIdeal ↔ _
  simp only [linearSectionEquation, map_sub, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, algebraMap_int_eq, Int.coe_castRingHom]

end ShimizuYamaguchi26BranchedCoverings
