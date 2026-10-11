/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleHomDescent
import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletion

/-!
# Hom descent along maximal-adic completion

This specializes faithfully flat Hom descent to the completion map of a
Noetherian local ring.  It is the full-faithfulness input for module formal
gluing at the closed point.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- Linear maps over a Noetherian local ring are exactly the compatible maps
between their maximal-adic completions. -/
noncomputable def maximalAdicCompletionModuleHomDescentEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    (M →ₗ[R] N) ≃ₗ[R]
      tensorProductDescentCompatibleLinearMaps
        (R := R) (S := AdicCompletion (maximalIdeal R) R)
        (M := M) (N := N) := by
  letI : Module.FaithfullyFlat R
      (AdicCompletion (maximalIdeal R) R) :=
    maximalAdicCompletion_faithfullyFlat R
  exact tensorProductLinearMapDescentEquiv

@[simp]
theorem maximalAdicCompletionModuleHomDescentEquiv_apply
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    ((maximalAdicCompletionModuleHomDescentEquiv R M N) f :
        (AdicCompletion (maximalIdeal R) R ⊗[R] M) →ₗ[
          AdicCompletion (maximalIdeal R) R]
        (AdicCompletion (maximalIdeal R) R ⊗[R] N)) =
      f.baseChange (AdicCompletion (maximalIdeal R) R) :=
  rfl

end EtaleFundamentalGroups

end
