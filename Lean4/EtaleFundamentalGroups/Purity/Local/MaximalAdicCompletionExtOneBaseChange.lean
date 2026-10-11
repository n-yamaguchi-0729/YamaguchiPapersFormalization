/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.FinitePresentationExtOneBaseChange
import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletionExtTorsion
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Ext¹ base change to a maximal-adic completion

Let `R` be a noetherian local ring and let `R̂` be its completion at the
maximal ideal.  For a finitely presented module `Q` killed by a power of the
maximal ideal, the canonical functorial map

`Ext¹_R(Q, N) → Ext¹_R̂(R̂ ⊗ Q, R̂ ⊗ N)`

is an equivalence of `R`-modules.  The proof is the direct composite of the
torsion tensor-unit equivalence with flat finite-presentation base change for
`Ext¹`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian IsLocalRing
open scoped TensorProduct ModuleCat.Algebra

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R] [Small.{u} R]
variable [IsNoetherianRing R] [IsLocalRing R]

-- Re-enable, only in this file, the functorial linear/exact structures used
-- to define the canonical map in `FinitePresentationExtOneBaseChange`.
attribute [local instance]
  moduleCatExtendScalarsLinearOverBase
  moduleCatExtendScalarsPreservesFiniteLimits
  moduleCatExtendScalarsAdditive
  extIsScalarTowerOfAlgebra

/-- The canonical `Ext¹` map to the maximal-adic completion, packaged as an
`R`-linear equivalence when its finitely presented first variable is killed
by a power of the maximal ideal. -/
noncomputable def maximalAdicCompletionExtOneEquivOfLeftTorsionPow
    (n : ℕ) (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q]
    (hQ : Module.IsTorsionBySet R Q
      ((maximalIdeal R) ^ n : Ideal R)) :
    Ext Q N 1 ≃ₗ[R]
      Ext
        ((ModuleCat.extendScalars
          (algebraMap R (AdicCompletion (maximalIdeal R) R))).obj Q)
        ((ModuleCat.extendScalars
          (algebraMap R (AdicCompletion (maximalIdeal R) R))).obj N)
        1 :=
  (adicCompletionExtTensorEquivOfLeftTorsionPow
      (maximalIdeal R) (maximalIdeal R).fg_of_isNoetherianRing n hQ 1).trans
    ((mapExtOne_isBaseChange_of_finitePresentation_of_flat
      (R := R) (S := AdicCompletion (maximalIdeal R) R) Q N).equiv.restrictScalars R)

@[simp]
theorem maximalAdicCompletionExtOneEquivOfLeftTorsionPow_apply
    (n : ℕ) (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q]
    (hQ : Module.IsTorsionBySet R Q
      ((maximalIdeal R) ^ n : Ideal R)) (x : Ext Q N 1) :
    maximalAdicCompletionExtOneEquivOfLeftTorsionPow n Q N hQ x =
      (ModuleCat.extendScalars
        (algebraMap R (AdicCompletion (maximalIdeal R) R))).mapExtLinearMap
          R Q N 1 x := by
  simp [maximalAdicCompletionExtOneEquivOfLeftTorsionPow]

/-- The underlying linear map of the completion equivalence is exactly the
canonical functorial map on `Ext¹`. -/
theorem maximalAdicCompletionExtOneEquivOfLeftTorsionPow_toLinearMap
    (n : ℕ) (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q]
    (hQ : Module.IsTorsionBySet R Q
      ((maximalIdeal R) ^ n : Ideal R)) :
    (maximalAdicCompletionExtOneEquivOfLeftTorsionPow n Q N hQ).toLinearMap =
      (ModuleCat.extendScalars
        (algebraMap R (AdicCompletion (maximalIdeal R) R))).mapExtLinearMap
          R Q N 1 := by
  ext x
  exact maximalAdicCompletionExtOneEquivOfLeftTorsionPow_apply n Q N hQ x

/-- In particular, the canonical map on `Ext¹` is bijective. -/
theorem maximalAdicCompletion_mapExtOne_bijective_of_left_torsionPow
    (n : ℕ) (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q]
    (hQ : Module.IsTorsionBySet R Q
      ((maximalIdeal R) ^ n : Ideal R)) :
    Function.Bijective
      ((ModuleCat.extendScalars
        (algebraMap R (AdicCompletion (maximalIdeal R) R))).mapExtLinearMap
          R Q N 1) := by
  rw [← maximalAdicCompletionExtOneEquivOfLeftTorsionPow_toLinearMap n Q N hQ]
  exact (maximalAdicCompletionExtOneEquivOfLeftTorsionPow n Q N hQ).bijective

end EtaleFundamentalGroups

end
