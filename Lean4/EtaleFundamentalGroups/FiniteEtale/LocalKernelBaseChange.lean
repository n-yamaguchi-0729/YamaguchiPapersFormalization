/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Foundations.Algebra.Module_free_quotient_range_of_ker_baseChange_residueField_le
import EtaleFundamentalGroups.FiniteEtale.ProjectiveCokernelBaseChange

/-!
# Local H⁰ base change from surjectivity on the closed fibre

For a map between finite free modules over a local ring, surjectivity of
the kernel comparison on the residue field forces both its kernel and
cokernel to split. In particular, its kernel is finite projective and
commutes with arbitrary scalar extension.
-/

noncomputable section

open scoped TensorProduct

namespace TwoChartCech

universe u

/-- Closed-fibre surjectivity for a finite free two-term complex gives a
finite projective kernel and arbitrary kernel base change. -/
theorem finite_projective_ker_and_bijective_baseChange_of_residue_surjective
    {R M N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (d : M →ₗ[R] N)
    (hsurj : Function.Surjective (kerBaseChangeHom d (IsLocalRing.ResidueField R))) :
    Module.Finite R (LinearMap.ker d) ∧ Module.Projective R (LinearMap.ker d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (kerBaseChangeHom d A) := by
  have hResidue : LinearMap.ker (d.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker d).subtype.baseChange (IsLocalRing.ResidueField R)) := by
    intro x hx
    obtain ⟨z, hz⟩ := hsurj ⟨x, hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  have hCoker : Module.Free R (N ⧸ LinearMap.range d) :=
    Module.free_quotient_range_of_ker_baseChange_residueField_le d hResidue
  exact finite_projective_ker_and_bijective_baseChange_of_projective_coker d

end TwoChartCech
