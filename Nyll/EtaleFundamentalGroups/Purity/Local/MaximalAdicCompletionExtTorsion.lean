/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.AdicCompletionAnnihilatedBaseChange
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic

/-!
# Torsion input for maximal-adic Ext base change

The completion comparison for `Ext¹` starts with a finite module killed by a
power of the adic ideal.  This file records the two elementary facts needed
before the flat base-change argument: the same ideal power annihilates every
`Ext` group with that module in the first variable, and hence the canonical
tensor unit into the adic completion is an equivalence on that `Ext` group.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- An annihilator of the first variable annihilates the corresponding
`Ext` group. -/
theorem ext_isTorsionBySet_of_left
    {Q N : ModuleCat.{v} R} {s : Set R}
    (hQ : Module.IsTorsionBySet R Q s) (i : ℕ) :
    Module.IsTorsionBySet R (Ext Q N i) s := by
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hQ ⊢
  intro r hr
  exact Module.mem_annihilator.mpr fun x ↦ by
    have hzero := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
      (M := N) (N := Q) (hQ hr) i
    have hx := ConcreteCategory.congr_hom hzero x
    simpa [Ext.mk₀_smul] using hx

/-- If the first variable is killed by `I ^ n`, then completion does not
change its `Ext` group at the tensor-unit stage. -/
noncomputable def adicCompletionExtTensorEquivOfLeftTorsionPow
    (I : Ideal R) (hI : I.FG) (n : ℕ)
    {Q N : ModuleCat.{v} R}
    (hQ : Module.IsTorsionBySet R Q (I ^ n : Ideal R)) (i : ℕ) :
    Ext Q N i ≃ₗ[R]
      (AdicCompletion I R ⊗[R] Ext Q N i) :=
  adicCompletionTensorEquivOfIsTorsionBySetPow I hI n
    (ext_isTorsionBySet_of_left hQ i)

@[simp]
theorem adicCompletionExtTensorEquivOfLeftTorsionPow_apply
    (I : Ideal R) (hI : I.FG) (n : ℕ)
    {Q N : ModuleCat.{v} R}
    (hQ : Module.IsTorsionBySet R Q (I ^ n : Ideal R)) (i : ℕ)
    (x : Ext Q N i) :
    adicCompletionExtTensorEquivOfLeftTorsionPow I hI n hQ i x =
      1 ⊗ₜ[R] x :=
  rfl

end EtaleFundamentalGroups

end
