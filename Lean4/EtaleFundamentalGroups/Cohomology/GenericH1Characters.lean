/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import EtaleFundamentalGroups.Inertia.GenericKernelNormalGeneration
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Actual geometric H¹ and unramified generic characters

The generic absolute Galois map identifies the characters of a normal integral
scheme with the characters that kill its actual normalization inertia groups.
The inertia groups are those of the literal integral closures on affine charts.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CategoryTheory
open EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Cohomology

universe u v

variable (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
variable {B : Type v} [CommGroup B] [TopologicalSpace B] [T2Space B]

/-- Actual generic characters descend precisely when they annihilate all
normalization inertia, including the topological closure of their normal span. -/
theorem exists_genericCharacter_iff_kills_inertia
    (χ : Gal(SeparableClosure X.functionField/X.functionField) →ₜ* B) :
    (∃ ψ : π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) →ₜ* B,
      ψ.comp (genericAbsoluteGaloisHom X) = χ) ↔
    ∀ σ ∈ affineNormalizationInertiaGenerators X, χ σ = 1 := by
  let q := genericAbsoluteGaloisHom X
  constructor
  · rintro ⟨ψ, rfl⟩ σ hσ
    have hk : σ ∈ q.toMonoidHom.ker := by
      rw [genericAbsoluteGaloisHom_ker_eq_normalClosure_affineNormalizationInertia]
      exact (Subgroup.normalClosure (affineNormalizationInertiaGenerators X)).le_topologicalClosure
        (Subgroup.subset_normalClosure hσ)
    change ψ (q σ) = 1
    rw [show q σ = 1 from hk, map_one]
  · intro hχ
    have hk : q.toMonoidHom.ker ≤ χ.toMonoidHom.ker := by
      rw [genericAbsoluteGaloisHom_ker_eq_normalClosure_affineNormalizationInertia]
      apply Subgroup.topologicalClosure_minimal
      · exact Subgroup.normalClosure_le_normal hχ
      · exact isClosed_eq χ.continuous continuous_const
    let e := QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom
      (genericAbsoluteGaloisHom_surjective X)
    let φ := (QuotientGroup.lift q.toMonoidHom.ker χ.toMonoidHom hk).comp
      e.symm.toMonoidHom
    have hφ : ∀ σ, φ (q σ) = χ σ := by
      intro σ
      change QuotientGroup.lift q.toMonoidHom.ker χ.toMonoidHom hk
        (e.symm (e (QuotientGroup.mk σ))) = χ σ
      rw [e.symm_apply_apply]
      rfl
    have hq : Topology.IsQuotientMap q :=
      Topology.IsQuotientMap.of_surjective_continuous
        (genericAbsoluteGaloisHom_surjective X) q.continuous
    have hc : Continuous φ := by
      rw [hq.continuous_iff]
      have he : φ ∘ q = χ := funext hφ
      rw [he]
      exact χ.continuous
    refine ⟨{ __ := φ, continuous_toFun := hc }, ?_⟩
    exact ContinuousMonoidHom.ext hφ

omit [T2Space B] in
/-- Two characters of the actual fundamental group agree if their generic
absolute Galois characters agree. -/
theorem genericCharacter_comp_injective :
    Function.Injective (fun ψ :
      π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) →ₜ* B =>
        ψ.comp (genericAbsoluteGaloisHom X)) := by
  intro ψ τ h
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨σ, rfl⟩ := genericAbsoluteGaloisHom_surjective X g
  exact congrArg (fun f => f σ) h

end EtaleFundamentalGroups.Cohomology
