/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Operations

/-!
# The local equation of the actual finite p-adic section divisor

The effective Cartier divisor constructed by pulling back the original finite
rational-section divisor to the p-adic integers has, on the infinity chart,
the product of the original primitive coordinate equations as its local
stalk equation. Both the finite-product pullback and stalk-product identities
reuse existing proofs. In particular the pullback-product proof retains its
external FLT attribution in its original AlgebraicCurves module.

This identifies the actual global divisor with the local equations used for
Shimizu and Yamaguchi, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators Polynomial
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual finite rational-section Cartier divisor over the p-adic integers
has the product of its primitive equations as its generator in every stalk of
the infinity chart. -/
theorem rationalSectionPadicDivisor_stalkIdeal_eq
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (q : Spec (CommRingCat.of ℤ_[p][X])) :
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData).stalkIdeal
        (infinityChartEmbedding ℤ_[p] q) =
      Ideal.span {(∏ a ∈ A, infinityChartGermAt ℤ_[p] q
        (Polynomial.C (rationalPointDenominator a : ℤ_[p]) -
          Polynomial.C (rationalPointNumerator a : ℤ_[p]) * Polynomial.X))} := by
  classical
  rw [rationalSectionPadicDivisor_ideal, comap_finset_prod,
    Scheme.IdealSheafData.stalkIdeal_finset_prod]
  calc
    (∏ a ∈ A, ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (infinityChartEmbedding ℤ_[p] q)) =
      ∏ a ∈ A, Ideal.span {(infinityChartGermAt ℤ_[p] q
        (Polynomial.C (rationalPointDenominator a : ℤ_[p]) -
          Polynomial.C (rationalPointNumerator a : ℤ_[p]) * Polynomial.X))} :=
      Finset.prod_congr rfl (fun a _ => rationalSection_baseChange_stalkIdeal_eq ℤ_[p] a q)
    _ = Ideal.span {(∏ a ∈ A, infinityChartGermAt ℤ_[p] q
        (Polynomial.C (rationalPointDenominator a : ℤ_[p]) -
          Polynomial.C (rationalPointNumerator a : ℤ_[p]) * Polynomial.X))} :=
      Ideal.prod_span_singleton A _

end ShimizuYamaguchi26BranchedCoverings
