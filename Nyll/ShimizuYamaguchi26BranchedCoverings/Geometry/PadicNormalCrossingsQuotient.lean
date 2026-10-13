/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.DyadicNormalCrossingsQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FullSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionFamily
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Proposition 2.5: a quadratic quotient from failure of dyadic normal crossings

The hypothesis is ordinary normal crossings of the actual base change of
`D_A` to the p-adic integers, as in Section 2 of Shimizu and Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1).

Strict normal crossings imply ordinary normal crossings. Thus failure of the
latter excludes the former, and the all-support p-adic criterion produces
failure along the original integral dyadic fibre. The constructed quadratic
cover then supplies a continuous quotient on the original integral complement.
No converse from ordinary to strict normal crossings is needed here.
-/

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- Proposition 2.5: if the actual rational-section divisor is not normal
crossings after base change to the 2-adic integers, its original integral
complement admits a continuous quotient of order two, at every geometric
base point. -/
theorem exists_surjective_cyclicTwo_of_not_normalCrossings_at_two
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (hbad : ¬ (rationalSectionPadicDivisor 2 A).IsNormalCrossings)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶
      (∏ a ∈ A, (rationalSection a).ker).supportComplement.toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  apply exists_surjective_cyclicTwo_of_not_strictNormalCrossings_over_two A ?_ ξ
  intro hstrict
  have hpadic : (rationalSectionPadicDivisor 2 A).IsStrictNormalCrossings :=
    (rationalSectionPadicDivisor_isStrictNormalCrossings_iff_integer 2 A).mpr hstrict
  exact hbad hpadic.isNormalCrossings

end ShimizuYamaguchi26BranchedCoverings
