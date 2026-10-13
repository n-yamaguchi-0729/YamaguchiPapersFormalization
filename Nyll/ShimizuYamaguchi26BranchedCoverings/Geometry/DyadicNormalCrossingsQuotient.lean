/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossingsGlobal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionFamily
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot5QuadraticQuotient
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

/-!
# A quadratic quotient from failure of integral dyadic normal crossings

Failure of strict normal crossings along the dyadic fibre of the actual
finite rational-section divisor produces a pair in the original boundary
with determinant divisible by four. The existing connected quadratic cover
then supplies a quotient on the complement of that same divisor.

This connects the geometric obstruction to the covering construction of
Proposition 2.5 of Shimizu and Yamaguchi, arXiv:2608.15057v1. Comparison with
normal crossings after base change to the p-adic integers remains separate;
the hypothesis here explicitly concerns strict normal crossings over integers.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- Failure of integral strict normal crossings over two gives a continuous
quadratic quotient on the actual finite-divisor complement, at every geometric
base point. The obstructing pair and its connected double cover are constructed. -/
theorem exists_surjective_cyclicTwo_of_not_strictNormalCrossings_over_two
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (hbad : ¬ ∀ x : ProjectiveLine ℤ,
      x ∈ (rationalSectionDivisor A).support →
      ProjSpace.π ℤ 1 x = integerPrimePoint 2 →
      (rationalSectionDivisor A).IsStrictNormalCrossingsAt x)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶
      (∏ a ∈ A, (rationalSection a).ker).supportComplement.toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  obtain ⟨a, ha, b, hb, hab, hval⟩ :=
    (rationalSectionFamily_not_isStrictNormalCrossings_over_two_iff A).mp hbad
  have hfour : (4 : ℤ) ∣ rationalPointDelta a b := by
    have hpower : (2 : ℤ) ^ 2 ∣ rationalPointDelta a b :=
      (padicValInt_dvd_iff 2 _).mpr (Or.inr hval)
    simpa only [show (2 : ℤ) ^ 2 = 4 by norm_num] using hpower
  revert ξ
  rw [rationalSectionFamily_supportComplement]
  intro ξ
  exact exists_surjective_cyclicTwo_of_four_dvd_delta_in_boundary A a b ha hb hab hfour ξ

end ShimizuYamaguchi26BranchedCoverings
