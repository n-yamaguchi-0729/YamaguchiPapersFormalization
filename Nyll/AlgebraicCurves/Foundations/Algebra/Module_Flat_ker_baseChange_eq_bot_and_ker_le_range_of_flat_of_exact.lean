/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Nyll.SchemeTheory.RingTheory.Flat.TensorInjectivity
import Nyll.SchemeTheory.RingTheory.Flat.Kernel

/-!
# Module Flat ker base Change eq bot and ker le range of flat of exact
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.ModuleFlatKerBaseChangeBotKerLe

universe u

open TensorProduct

theorem _root_.Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1))
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (h0 : LinearMap.ker (d 0) = ⊥) (hex : ∀ i, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((d 0).baseChange A) = ⊥ ∧
      ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by
  classical
  let Z : ∀ i, Submodule R (C i) := fun i => LinearMap.ker (d i)
  have hdZ : ∀ i (c : C i), d i c ∈ Z (i + 1) := fun i c => by
    change d (i + 1) (d i c) = 0
    exact LinearMap.congr_fun (hdd i) c
  let g : ∀ i, C i →ₗ[R] ↥(Z (i + 1)) := fun i => LinearMap.codRestrict (Z (i + 1)) (d i) (hdZ i)
  have hg_surj : ∀ i, Function.Surjective (g i) := by
    intro i z
    obtain ⟨c, hc⟩ := hex i z.2
    exact ⟨c, Subtype.ext hc⟩
  have hg_exact : ∀ i, Function.Exact (Z i).subtype (g i) := by
    intro i
    rw [LinearMap.exact_iff, LinearMap.ker_codRestrict, Submodule.range_subtype]
  have hdig : ∀ i, d i = (Z (i + 1)).subtype ∘ₗ g i := fun i =>
    (LinearMap.subtype_comp_codRestrict _ _ _).symm
  have hflat : ∀ k i, n ≤ i + k → Module.Flat R ↥(Z i) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : Subsingleton (C i) := hbd i (by omega)
      infer_instance
    | succ k ih =>
      intro i hi
      have : Module.Flat R ↥(Z (i + 1)) := ih (i + 1) (by omega)
      have := Module.Flat.ker_of_surjective_of_flat (g i) (hg_surj i)
      exact Module.Flat.of_linearEquiv (M := ↥(LinearMap.ker (g i)))
        (LinearEquiv.ofEq (Z i) (LinearMap.ker (g i)) (LinearMap.ker_codRestrict (Z (i + 1)) (d i)
          (hdZ i)).symm)
  have hflat' : ∀ i, Module.Flat R ↥(Z i) := fun i => hflat n i (Nat.le_add_left n i)
  have hinj : ∀ i, Function.Injective ((Z i).subtype.lTensor A) := fun i =>
    haveI := hflat' (i + 1)
    Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat (Z i).subtype (g i)
      (Z i).injective_subtype (hg_exact i) (hg_surj i) A
  have hker : ∀ i, LinearMap.ker ((d i).lTensor A) = LinearMap.range ((Z i).subtype.lTensor A) := by
    intro i
    rw [hdig i, LinearMap.lTensor_comp, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (hinj (i + 1)))]
    exact (LinearMap.exact_iff.mp (lTensor_exact A (hg_exact i) (hg_surj i)))
  have hrange : ∀ i, LinearMap.range ((d i).lTensor A) = LinearMap.range ((Z (i +
    1)).subtype.lTensor A) := by
    intro i
    rw [hdig i, LinearMap.lTensor_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective A (hg_surj i)))]
  constructor
  · rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hx
    have hx' : x ∈ LinearMap.ker ((d 0).lTensor A) := hx
    rw [hker 0] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hZ0 : Z 0 = ⊥ := h0
    have : Subsingleton ↥(Z 0) := by rw [hZ0]; infer_instance
    rw [Subsingleton.elim y 0, map_zero]
  · intro i x hx
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hx
    have hx' : x ∈ LinearMap.ker ((d (i + 1)).lTensor A) := hx
    rw [hker (i + 1), ← hrange i] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]⟩
end AlgebraicCurves.Foundations.Algebra.Proofs.ModuleFlatKerBaseChangeBotKerLe
end ProofImplementation
