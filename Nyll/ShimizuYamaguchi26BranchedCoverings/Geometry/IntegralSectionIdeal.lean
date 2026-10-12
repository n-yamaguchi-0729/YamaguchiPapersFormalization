/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Closure
import Mathlib.Topology.Sets.Closeds

/-!
# The ideal sheaf of an integral section

The section constructed from a primitive integer pair has reduced source
`Spec ℤ`. Its scheme-theoretic image therefore has the reduced induced
structure on its closed image. The actual kernel ideal sheaf is consequently
the vanishing ideal of the homogeneous equation's zero locus.

For a rational point, this identifies the section's ideal sheaf with the
vanishing ideal of the Zariski closure of the original rational point, as in
Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
This statement identifies the reduced closed subscheme; identifying its ideal
on a chart with the principal linear-equation ideal additionally uses the
radicality of that concrete polynomial ideal.
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The kernel of the actual integral section is the reduced ideal sheaf of
the zero locus of its primitive homogeneous equation. -/
theorem integralSection_ker_eq_vanishingIdeal
    (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (integralSection u v a b hab).ker =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
            {linearSectionEquation u v},
          ProjectiveSpectrum.isClosed_zeroLocus _ _⟩ := by
  have hbot : Scheme.IdealSheafData.vanishingIdeal
      (⊤ : TopologicalSpace.Closeds (Spec (CommRingCat.of ℤ))) = ⊥ := by
    rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  rw [← Scheme.IdealSheafData.map_bot (integralSection u v a b hab),
    ← hbot, Scheme.IdealSheafData.map_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply SetLike.coe_injective
  change closure ((integralSection u v a b hab) '' Set.univ) = _
  rw [Set.image_univ]
  have hrange : Set.range (integralSection u v a b hab) =
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u v} : Set (ProjectiveLine ℤ)) :=
    range_integralSection u v a b hab
  exact (integralSection u v a b hab).isClosedEmbedding.isClosed_range.closure_eq.trans hrange

/-- The actual ideal sheaf of a rational section is the vanishing ideal of
the closure of its original rational point in the integral projective line. -/
theorem rationalSection_ker_eq_vanishingIdeal_closure
    (a : Projectivization ℚ (ℚ × ℚ)) :
    (rationalSection a).ker =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure
          ({rationalSectionGenericPoint a} : Set (ProjectiveLine ℤ))) := by
  unfold rationalSection
  rw [integralSection_ker_eq_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply SetLike.coe_injective
  change rationalSectionSupport a =
    closure ({rationalSectionGenericPoint a} : Set (ProjectiveLine ℤ))
  exact (closure_rationalSectionGenericPoint a).symm

end ShimizuYamaguchi26BranchedCoverings
