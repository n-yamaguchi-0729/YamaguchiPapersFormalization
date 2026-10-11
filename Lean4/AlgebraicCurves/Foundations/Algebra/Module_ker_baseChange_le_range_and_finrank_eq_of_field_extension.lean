/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Dimension.Constructions
import SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Module ker base Change le range and finrank eq of field extension
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension

universe u

open TensorProduct

namespace K4EDescendGood

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K']
  [Algebra R K']
  [Algebra K K'] [IsScalarTower R K K']

/-- The scalar-restricted inclusion of the smaller field into its extension. -/
noncomputable def incl : K →ₗ[R] K' := (Algebra.linearMap K K').restrictScalars R

theorem exists_retraction : ∃ r : K' →ₗ[K] K, r ∘ₗ Algebra.linearMap K K' = LinearMap.id := by
  apply LinearMap.exists_leftInverse_of_injective
  exact LinearMap.ker_eq_bot_of_injective (algebraMap K K').injective

variable {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem baseChange_j (φ : X →ₗ[R] Y) (z : K ⊗[R] X) :
    φ.baseChange K' ((incl K K').rTensor X z) = (incl K K').rTensor Y (φ.baseChange K z) := by
  change (φ.lTensor K') ((incl K K').rTensor X z) = (incl K K').rTensor Y ((φ.lTensor K) z)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

theorem baseChange_ρ (r : K' →ₗ[K] K) (φ : X →ₗ[R] Y) (z : K' ⊗[R] X) :
    φ.baseChange K ((r.restrictScalars R).rTensor X z) = (r.restrictScalars R).rTensor Y
      (φ.baseChange K' z) := by
  change (φ.lTensor K) ((r.restrictScalars R).rTensor X z) = (r.restrictScalars R).rTensor Y
    ((φ.lTensor K') z)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

theorem ρ_j (r : K' →ₗ[K] K) (hr : r ∘ₗ Algebra.linearMap K K' = LinearMap.id) (z : K ⊗[R] X) :
    (r.restrictScalars R).rTensor X ((incl K K').rTensor X z) = z := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : r.restrictScalars R ∘ₗ incl K K' = LinearMap.id := by
    ext c
    exact congrArg (fun f : K →ₗ[K] K => f c) hr
  rw [this, LinearMap.rTensor_id, LinearMap.id_apply]

theorem ker_le_range_descend {Z : Type u} [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : LinearMap.ker (g.baseChange K') ≤ LinearMap.range (f.baseChange K')) :
    LinearMap.ker (g.baseChange K) ≤ LinearMap.range (f.baseChange K) := by
  obtain ⟨r, hr⟩ := exists_retraction K K'
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have hj : (incl K K').rTensor Y u ∈ LinearMap.ker (g.baseChange K') := by
    rw [LinearMap.mem_ker, baseChange_j, hu, map_zero]
  obtain ⟨v, hv⟩ := h hj
  refine ⟨(r.restrictScalars R).rTensor X v, ?_⟩
  rw [baseChange_ρ, hv, ρ_j K K' r hr]

theorem cancelBaseChange_baseChange_baseChange (φ : X →ₗ[R] Y) (z : K' ⊗[K] (K ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R K K' K' Y (((φ.baseChange K).baseChange K') z) =
      (φ.baseChange K') (AlgebraTensorModule.cancelBaseChange R K K' K' X z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      simp [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [tmul_add, map_add, h₁, h₂]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
omit [Algebra R K] [Algebra R K'] [IsScalarTower R K K'] in
theorem finrank_baseChange_field (V : Type u) [AddCommGroup V] [Module K V] :
    Module.finrank K' (K' ⊗[K] V) = Module.finrank K V :=
  Module.finrank_baseChange

theorem finrank_ker_descend (φ : X →ₗ[R] Y) :
    Module.finrank K' (LinearMap.ker (φ.baseChange K')) = Module.finrank K (LinearMap.ker
      (φ.baseChange K)) := by
  set eX := AlgebraTensorModule.cancelBaseChange R K K' K' X
  set eY := AlgebraTensorModule.cancelBaseChange R K K' K' Y
  set A := (φ.baseChange K).baseChange K'
  set B := φ.baseChange K'
  have key : B ∘ₗ eX.toLinearMap = eY.toLinearMap ∘ₗ A := by
    apply LinearMap.ext; intro z
    exact (cancelBaseChange_baseChange_baseChange K K' φ z).symm
  have hmap : (LinearMap.ker A).map eX.toLinearMap = LinearMap.ker B := by
    have h1 : LinearMap.ker A = (LinearMap.ker B).comap eX.toLinearMap := by
      rw [← LinearMap.ker_comp, key, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    rw [h1, Submodule.map_comap_eq_of_surjective eX.surjective]
  have e1 : LinearMap.ker A ≃ₗ[K'] LinearMap.ker B := LinearEquiv.ofSubmodules eX _ _ hmap
  have e2 : K' ⊗[K] LinearMap.ker (φ.baseChange K) ≃ₗ[K'] LinearMap.ker A :=
    LinearMap.tensorKerEquiv K' K' (φ.baseChange K)
  rw [← e1.finrank_eq, ← e2.finrank_eq]
  exact finrank_baseChange_field K K' (LinearMap.ker (φ.baseChange K))

end K4EDescendGood

open K4EDescendGood in
theorem _root_.Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1))
    {F : Type u} [AddCommGroup F] [Module R F] (Θ : F →ₗ[R] C 0)
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R K K'] (r : ℕ)
    (h1 : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K') ≤ LinearMap.range ((d i).baseChange
      K'))
    (h2 : LinearMap.ker ((d 0).baseChange K') ≤ LinearMap.range (Θ.baseChange K'))
    (h3 : Module.finrank K' (LinearMap.ker ((d 0).baseChange K')) = r) :
    (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) ∧
    LinearMap.ker ((d 0).baseChange K) ≤ LinearMap.range (Θ.baseChange K) ∧
    Module.finrank K (LinearMap.ker ((d 0).baseChange K)) = r := by
  refine ⟨fun i => ker_le_range_descend K K' (d i) (d (i + 1)) (h1 i),
    ker_le_range_descend K K' Θ (d 0) h2, ?_⟩
  rw [← finrank_ker_descend K K' (d 0), h3]
end Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
