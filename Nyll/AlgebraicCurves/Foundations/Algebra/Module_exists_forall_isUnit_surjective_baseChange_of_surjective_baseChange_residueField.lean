/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Module exists forall is Unit surjective base Change of surjective base Change residue
Field
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField

universe u

open TensorProduct

namespace K4FSurjSpread

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

theorem lTensor_surjective_of_subsingleton (f : M →ₗ[R] N) (A : Type u) [AddCommGroup A] [Module R
  A]
    (h : Subsingleton (A ⊗[R] (N ⧸ LinearMap.range f))) : Function.Surjective (f.lTensor A) := by
  have ex := lTensor_exact A (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
  rw [← LinearMap.range_eq_top, ← ex.linearMap_ker_eq, LinearMap.ker_eq_top]
  ext x
  exact Subsingleton.elim _ _

theorem subsingleton_tensor_of_smul_eq_zero (Q : Type u) [AddCommGroup Q] [Module R Q] (g : R)
    (hg : ∀ q : Q, g • q = 0) (A : Type u) [CommRing A] [Algebra R A] (hu : IsUnit (algebraMap R A
      g)) :
    Subsingleton (A ⊗[R] Q) := by
  refine ⟨fun x y => ?_⟩
  suffices h0 : ∀ z : A ⊗[R] Q, z = 0 by rw [h0 x, h0 y]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a q =>
    obtain ⟨v, hv⟩ := hu
    have : a = g • ((v⁻¹ : Aˣ).1 * a) := by
      rw [Algebra.smul_def, ← mul_assoc, ← hv, Units.mul_inv, one_mul]
    rw [this, ← smul_tmul', ← tmul_smul, hg, tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end K4FSurjSpread

open K4FSurjSpread in
theorem
  _root_.Module.exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (𝔭 : PrimeSpectrum R)
    (hf : Function.Surjective (f.baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Function.Surjective (f.baseChange A) := by
  classical
  set Q := N ⧸ LinearMap.range f with hQ
  have hsub : Subsingleton (𝔭.asIdeal.ResidueField ⊗[R] Q) := by
    have ex := lTensor_exact 𝔭.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
      (Submodule.mkQ_surjective _)
    have hsurj : Function.Surjective ((LinearMap.range f).mkQ.lTensor 𝔭.asIdeal.ResidueField) :=
      LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
    have hzero : (LinearMap.range f).mkQ.lTensor 𝔭.asIdeal.ResidueField = 0 := by
      rw [← LinearMap.ker_eq_top, ex.linearMap_ker_eq, LinearMap.range_eq_top]
      have : ⇑(f.baseChange 𝔭.asIdeal.ResidueField) = ⇑(f.lTensor 𝔭.asIdeal.ResidueField) :=
        LinearMap.baseChange_eq_ltensor f
      rw [← this]; exact hf
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := hsurj x; obtain ⟨y', rfl⟩ := hsurj y
    rw [hzero]; rfl
  have hnot : 𝔭 ∉ Module.support R Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite, IsConcreteLE.not_le_iff_exists] at hnot
  obtain ⟨g, hgann, hg𝔭⟩ := hnot
  refine ⟨g, hg𝔭, fun A _ _ hu => ?_⟩
  have hsubA := subsingleton_tensor_of_smul_eq_zero Q g (fun q => Module.mem_annihilator.mp hgann
    q) A hu
  have := lTensor_surjective_of_subsingleton f A hsubA
  have hfun : ⇑(f.baseChange A) = ⇑(f.lTensor A) := LinearMap.baseChange_eq_ltensor f
  rw [hfun]; exact this
end Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
