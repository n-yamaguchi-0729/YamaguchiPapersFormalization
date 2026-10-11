/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.AdicCompletionQuotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Base change of modules annihilated by the adic ideal

The first, torsion-level input to formal gluing is that extension of scalars
from a ring to its adic completion does not change a module annihilated by the
adic ideal.  The proof uses the closed-fibre comparison and is valid without
assuming that the original ring is complete.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

open scoped TensorProduct

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (hI : I.FG)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An element of the extended ideal tensors to zero against a module
annihilated by the original ideal. -/
theorem adicCompletion_tmul_eq_zero_of_mem_map
    (hM : Module.IsTorsionBySet R M I)
    {x : AdicCompletion I R}
    (hx : x ∈ I.map (algebraMap R (AdicCompletion I R))) (m : M) :
    x ⊗ₜ[R] m = 0 := by
  rw [Ideal.map, ← Ideal.submodule_span_eq] at hx
  refine Submodule.span_induction
    (p := fun y : AdicCompletion I R ↦ fun _ ↦ y ⊗ₜ[R] m = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨r, hr, rfl⟩
    simpa [Algebra.smul_def, @hM m ⟨r, hr⟩] using
      (TensorProduct.smul_tmul r (1 : AdicCompletion I R) m)
  · simp
  · intro x y _ _ hx hy
    rw [TensorProduct.add_tmul, hx, hy, add_zero]
  · intro a x _ hx
    rw [← TensorProduct.smul_tmul', hx, smul_zero]

/-- If `M` is annihilated by `I`, then the canonical base-change map
`M → Â ⊗[R] M` is bijective. -/
theorem adicCompletion_tensorProduct_mk_bijective_of_isTorsionBySet
    (hI : I.FG)
    (hM : Module.IsTorsionBySet R M I) :
    Function.Bijective
      (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  have hsmul : I • (⊤ : Submodule R M) = ⊥ := by
    apply Submodule.le_annihilator_iff.mp
    rw [Submodule.annihilator_top]
    exact (Module.isTorsionBySet_iff_subset_annihilator R M).mp hM
  constructor
  · intro m n hmn
    have hmapped := congrArg
      (TensorProduct.map
        (adicCompletionClosedFiberAlgHom I hI).toLinearMap
        (LinearMap.id : M →ₗ[R] M)) hmn
    have hquot := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) hmapped
    have hmk : (Submodule.Quotient.mk m : M ⧸ (I • (⊤ : Submodule R M))) =
        Submodule.Quotient.mk n := by
      simpa using hquot
    have hdiff : m - n ∈ I • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq _).mp hmk
    rw [hsmul, Submodule.mem_bot] at hdiff
    exact sub_eq_zero.mp hdiff
  · intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        obtain ⟨mx, rfl⟩ := hx
        obtain ⟨my, rfl⟩ := hy
        refine ⟨mx + my, ?_⟩
        change 1 ⊗ₜ[R] (mx + my) = 1 ⊗ₜ[R] mx + 1 ⊗ₜ[R] my
        rw [TensorProduct.tmul_add]
    | tmul x m =>
        obtain ⟨r, hr⟩ := adicCompletion_exists_sub_mem_map I hI x
        refine ⟨r • m, ?_⟩
        have hzero :
            (x - algebraMap R (AdicCompletion I R) r) ⊗ₜ[R] m = 0 :=
          adicCompletion_tmul_eq_zero_of_mem_map I hM hr m
        have heq :
            x ⊗ₜ[R] m =
              algebraMap R (AdicCompletion I R) r ⊗ₜ[R] m := by
          apply sub_eq_zero.mp
          simpa only [TensorProduct.sub_tmul] using hzero
        calc
          1 ⊗ₜ[R] (r • m) =
              (r • (1 : AdicCompletion I R)) ⊗ₜ[R] m :=
            (TensorProduct.smul_tmul r (1 : AdicCompletion I R) m).symm
          _ = algebraMap R (AdicCompletion I R) r ⊗ₜ[R] m := by
            rw [Algebra.smul_def, mul_one]
          _ = x ⊗ₜ[R] m := heq.symm

/-- The canonical linear equivalence furnished by base change for an
`I`-annihilated module. -/
noncomputable def adicCompletionTensorEquivOfIsTorsionBySet
    (hI : I.FG)
    (hM : Module.IsTorsionBySet R M I) :
    M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
  LinearEquiv.ofBijective
    (TensorProduct.mk R (AdicCompletion I R) M 1)
    (adicCompletion_tensorProduct_mk_bijective_of_isTorsionBySet I hI hM)

@[simp]
theorem adicCompletionTensorEquivOfIsTorsionBySet_apply
    (hI : I.FG)
    (hM : Module.IsTorsionBySet R M I) (m : M) :
    adicCompletionTensorEquivOfIsTorsionBySet I hI hM m = 1 ⊗ₜ[R] m :=
  rfl

/-- An element of the extension of `I ^ n` tensors to zero against a module
annihilated by `I ^ n`, while the completion remains the `I`-adic
completion. -/
theorem adicCompletion_tmul_eq_zero_of_mem_map_pow
    (n : ℕ) (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R))
    {x : AdicCompletion I R}
    (hx : x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R))) (m : M) :
    x ⊗ₜ[R] m = 0 := by
  rw [Ideal.map, ← Ideal.submodule_span_eq] at hx
  refine Submodule.span_induction
    (p := fun y : AdicCompletion I R ↦ fun _ ↦ y ⊗ₜ[R] m = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨r, hr, rfl⟩
    simpa [Algebra.smul_def, @hM m ⟨r, hr⟩] using
      (TensorProduct.smul_tmul r (1 : AdicCompletion I R) m)
  · simp
  · intro x y _ _ hx hy
    rw [TensorProduct.add_tmul, hx, hy, add_zero]
  · intro a x _ hx
    rw [← TensorProduct.smul_tmul', hx, smul_zero]

/-- If `M` is annihilated by `I ^ n`, then the canonical map to its base
change along the `I`-adic completion is bijective. -/
theorem adicCompletion_tensorProduct_mk_bijective_of_isTorsionBySet_pow
    (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    Function.Bijective
      (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  have hsmul : I ^ n • (⊤ : Submodule R M) = ⊥ := by
    apply Submodule.le_annihilator_iff.mp
    rw [Submodule.annihilator_top]
    exact (Module.isTorsionBySet_iff_subset_annihilator R M).mp hM
  constructor
  · intro m m' hmm'
    have hmapped := congrArg
      (TensorProduct.map
        (AdicCompletion.evalₐ I n).toLinearMap
        (LinearMap.id : M →ₗ[R] M)) hmm'
    have hquot := congrArg
      (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)) hmapped
    have hmk :
        (Submodule.Quotient.mk m : M ⧸ (I ^ n • (⊤ : Submodule R M))) =
          Submodule.Quotient.mk m' := by
      simpa using hquot
    have hdiff : m - m' ∈ I ^ n • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq _).mp hmk
    rw [hsmul, Submodule.mem_bot] at hdiff
    exact sub_eq_zero.mp hdiff
  · intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        obtain ⟨mx, rfl⟩ := hx
        obtain ⟨my, rfl⟩ := hy
        refine ⟨mx + my, ?_⟩
        change 1 ⊗ₜ[R] (mx + my) = 1 ⊗ₜ[R] mx + 1 ⊗ₜ[R] my
        rw [TensorProduct.tmul_add]
    | tmul x m =>
        obtain ⟨r, hr⟩ := adicCompletion_exists_sub_mem_map_pow I hI n x
        refine ⟨r • m, ?_⟩
        have hzero :
            (x - algebraMap R (AdicCompletion I R) r) ⊗ₜ[R] m = 0 :=
          adicCompletion_tmul_eq_zero_of_mem_map_pow I n hM hr m
        have heq :
            x ⊗ₜ[R] m =
              algebraMap R (AdicCompletion I R) r ⊗ₜ[R] m := by
          apply sub_eq_zero.mp
          simpa only [TensorProduct.sub_tmul] using hzero
        calc
          1 ⊗ₜ[R] (r • m) =
              (r • (1 : AdicCompletion I R)) ⊗ₜ[R] m :=
            (TensorProduct.smul_tmul r (1 : AdicCompletion I R) m).symm
          _ = algebraMap R (AdicCompletion I R) r ⊗ₜ[R] m := by
            rw [Algebra.smul_def, mul_one]
          _ = x ⊗ₜ[R] m := heq.symm

/-- The canonical linear equivalence for a module annihilated by a power of
the adic ideal. -/
noncomputable def adicCompletionTensorEquivOfIsTorsionBySetPow
    (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
  LinearEquiv.ofBijective
    (TensorProduct.mk R (AdicCompletion I R) M 1)
    (adicCompletion_tensorProduct_mk_bijective_of_isTorsionBySet_pow
      I hI n hM)

@[simp]
theorem adicCompletionTensorEquivOfIsTorsionBySetPow_apply
    (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) (m : M) :
    adicCompletionTensorEquivOfIsTorsionBySetPow I hI n hM m =
      1 ⊗ₜ[R] m :=
  rfl

end EtaleFundamentalGroups

end
