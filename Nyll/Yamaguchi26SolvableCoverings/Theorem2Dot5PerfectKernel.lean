/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.Boundary
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot1BoundaryQuotient
import Nyll.Yamaguchi26SolvableCoverings.GroupTheory.PerfectKernel
import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryAbelianizationPullback
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot2BoundaryCondition
import Nyll.ProCGroups.FiniteStepSolvableQuotients.ProsolvableCriterion
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Theorem 2.5: the boundary kernel is topologically perfect

Under condition `(†)`, the complement of the horizontal divisor is connected and
the kernel of the inclusion-induced fundamental-group homomorphism is topologically
perfect. The same homomorphism induces an isomorphism on maximal prosolvable quotients.

The commutator closure is taken inside the kernel with its own subspace topology.
The quotient isomorphism agrees with the inclusion-induced map on all representatives.
The proof applies abelian invariance after the actual finite etale covers corresponding
to open normal subgroups, then checks perfectness in finite quotients.

Source: [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1), Theorem 2.5.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open ProCGroups.FiniteStepSolvableQuotients

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- 定理 2.5：条件 `(†)` の下で、補集合は連結、包含が誘導する
基本群の準同型の核は位相的完全であり、その最大 prosolvable 商への誘導写像は同型である。 -/
theorem perfect_kernel_2_5
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hD : BoundaryCondition D) :
    ConnectedSpace D.1.supportComplement ∧
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement),
        let f : π₁ᵉᵗ(point) →ₜ* π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) :=
          fundamentalGroupHom D.1.supportComplement.ι point
        (commutator f.toMonoidHom.ker).topologicalClosure = ⊤ ∧
          ∃ e : Prosolvable π₁ᵉᵗ(point) ≃ₜ* Prosolvable π₁ᵉᵗ(point ≫ D.1.supportComplement.ι),
            ∀ g : π₁ᵉᵗ(point), e (QuotientGroup.mk g) = QuotientGroup.mk (f g) := by
  obtain ⟨hU, hboundary⟩ := boundary_quotient_1_1 D hD.1
  refine ⟨hU, ?_⟩
  let : ConnectedSpace D.1.supportComplement := hU
  intro Ω _ _ point
  let f : π₁ᵉᵗ(point) →ₜ* π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) :=
    fundamentalGroupHom D.1.supportComplement.ι point
  have hf : Function.Surjective f := (hboundary Ω point).1
  have hAb : OpenNormalAbelianizationInjective f :=
    openNormalAbelianizationInjective_of_finiteDiscreteAbelianMapsKillKernel
      f hf (boundary_openNormalFiniteDiscreteAbelianMapsKillKernel D hhor hD point)
  refine ⟨kernel_topologicallyPerfect_of_openNormalAbelianizationInjective f hf hAb, ?_⟩
  refine ⟨prosolvableResidualQuotientContinuousMulEquiv f hf hAb, ?_⟩
  intro g
  rfl

end Yamaguchi26SolvableCoverings
