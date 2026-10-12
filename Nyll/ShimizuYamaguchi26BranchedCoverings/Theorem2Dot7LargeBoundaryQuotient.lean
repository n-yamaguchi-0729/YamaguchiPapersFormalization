/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.SixSectionBound
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot5QuadraticQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Corollary 2.7: a quotient for at least seven rational sections

Source: Ryoji Shimizu and Naganori Yamaguchi,
On branched coverings of the projective line over the integers,
[arXiv:2608.15057v1](https://arxiv.org/abs/2608.15057v1),
Corollary 2.7, the case of at least seven boundary components.

For a finite set `A` of rational projective points, the open `U_A` is the
finite intersection of the nonvanishing opens of their primitive section
equations. These are the complements of the actual homogeneous supports
`rationalSectionSupport`; `range_rationalSection` identifies those supports
with the images of the integral sections.

If `A` has at least seven members, the existing arithmetic bound supplies
two distinct points whose primitive determinant is divisible by four.
Their determinant is nonzero because the points are distinct. The existing
connected quadratic cover then gives a continuous surjection from the actual
etale fundamental group of `U_A` to the cyclic group of order two.

The statement holds at every geometric point of the constructed open. That
point supplies the nonemptiness needed by the existing open-restriction
argument; no affine comparison, cover, or connectedness is assumed.
This proves the large-boundary part of Corollary 2.7. The cases of at most
two boundary components, and the full equivalence with normal crossings,
are separate assertions.
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Corollary 2.7, large-boundary case: the complement of at least seven
rational sections has a continuous cyclic quotient of order two at every
geometric base point. The open is constructed as the finite intersection
of the complements of the actual section equations. -/
theorem large_boundary_quotient_2_7
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) (hcard : 7 ≤ A.card)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶
      (A.inf fun a => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (rationalPointNumerator a)
          (rationalPointDenominator a))).toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  classical
  let O : Projectivization ℚ (ℚ × ℚ) → (ProjectiveLine ℤ).Opens := fun a =>
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation (rationalPointNumerator a) (rationalPointDenominator a))
  let U : (ProjectiveLine ℤ).Opens := A.inf O
  have hsize : 6 < Fintype.card ↥A := by
    rw [Fintype.card_coe]
    exact lt_of_lt_of_le (by decide : 6 < 7) hcard
  obtain ⟨a, b, hab, hfour⟩ :=
    exists_four_dvd_coordinateDeterminant_of_six_lt_card
      (ι := ↥A) (fun a => rationalPointNumerator a.val)
      (fun a => rationalPointDenominator a.val)
      (fun a => rationalPointCoordinates_isCoprime a.val) hsize
  have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hU : U ≤ integralPairComplement
      (rationalPointNumerator a.val) (rationalPointDenominator a.val)
      (rationalPointNumerator b.val) (rationalPointDenominator b.val) := by
    change A.inf O ≤ O a.val ⊓ O b.val
    exact le_inf (Finset.inf_le a.property) (Finset.inf_le b.property)
  exact exists_surjective_cyclicTwo_of_four_dvd_pairDeterminant
    (rationalPointNumerator a.val) (rationalPointDenominator a.val)
    (rationalPointNumerator b.val) (rationalPointDenominator b.val)
    (rationalPointCoordinates_isCoprime a.val) (rationalPointCoordinates_isCoprime b.val)
    hfour (rationalPoint_coordinateDeterminant_ne_zero a.val b.val hne) U hU ξ

end ShimizuYamaguchi26BranchedCoverings
