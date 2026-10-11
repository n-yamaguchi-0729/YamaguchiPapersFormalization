/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_H1_of_genusReached.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_of_genusReached
import AlgebraicCurves.Cohomology.Mem_adeleSpace_iff_mem_repartitions
import AlgebraicCurves.Cohomology.Mem_repartitionsOf_iff_coe_mem_adeleBdd

/-!
Finite adelic first cohomology from a two-chart Cech system reaching the genus.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Finite_H1_of_genusReached

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.finite_H1_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra
    K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (H1 D) := by
  obtain ⟨hfin, -⟩ := indexOfSpecialty_eq_of_genusReached h D
  let e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F) :=
    { toFun := fun a => ⟨(a : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mp a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ : ↥(adeleSpace K F) →ₗ[K] H1 D := (repartitionsOf D ⊔ principalRepartitions K F).mkQ ∘ₗ e
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨⟨(β : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr β.2⟩, ?_⟩
    rfl
  have hker : adeleBddPrincipal K F D ≤ LinearMap.ker φ := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left (mem_repartitionsOf_iff_coe_mem_adeleBdd.mpr ha)
    · intro a ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨f, hf⟩ := LinearMap.mem_range.mp ha
      refine Submodule.mem_sup_right (mem_principalRepartitions_iff.mpr ⟨f, ?_⟩)
      funext v
      have hv := congrFun hf v
      rw [diagonalHom_apply] at hv
      exact hv.symm
  have hψ : Function.Surjective ((adeleBddPrincipal K F D).liftQ φ hker) := by
    intro q
    obtain ⟨a, rfl⟩ := hφ q
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  exact Module.Finite.of_surjective _ hψ
end AlgebraicCurves.Cohomology.Proofs.Finite_H1_of_genusReached
end ProofImplementation
