/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction

/-!
# Lifting normalization inertia to finite fields

Transfers the inertia difference condition through normalization restriction and lifts intrinsic
finite-normalization inertia to finite-field inertia.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

section NativeRestriction

attribute [local instance] normalizationCommAlgGaloisAction

/-- Actual equality with the normalization restriction transfers the
literal inertia difference condition to the prescribed field action.
This action comparison does not introduce finite-dimensional module data. -/
theorem mem_inertia_of_normalization_restriction
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) (σ : F ≃ₐ[K] F)
    (τ : (normalizationCommAlgCat A F).carrier ≃ₐ[A] (normalizationCommAlgCat A F).carrier)
    (hσ : (σ.restrictScalars A).mapIntegralClosure = τ)
    (hτ : ∀ b : (normalizationCommAlgCat A F).carrier, τ.toRingHom.toFun b - b ∈ Q) :
    σ ∈ Q.inertia Gal(F/K) := by
  have hring : normalizationGaloisRingHom A K F σ = τ.toRingHom := by
    change ((σ.restrictScalars A).mapIntegralClosure).toRingHom = τ.toRingHom
    exact congrArg
      (fun f : (normalizationCommAlgCat A F).carrier ≃ₐ[A]
        (normalizationCommAlgCat A F).carrier => f.toRingHom) hσ
  intro b
  change (MulSemiringAction.toRingHom Gal(F/K)
    (normalizationCommAlgCat A F).carrier σ).toFun b - b ∈ Q
  rw [← normalizationGaloisRingHom_eq_original A K F σ, hring]
  exact hτ b

end NativeRestriction

attribute [local instance] normalizationInertiaImageAction

/-- An intrinsic finite-normalization inertia automorphism lifts to the
prescribed finite-field ideal inertia. Its restriction is the same actual
coefficient automorphism, not a separately supplied comparison. -/
theorem finiteNormalization_inertia_exists_field_lift
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [IsGalois K F] [FiniteDimensional K F]
    (Q : Ideal (integralClosure A F))
    (τ : integralClosure A F ≃ₐ[A] integralClosure A F)
    (hτ : ∀ b : integralClosure A F, τ.toRingHom b - b ∈ Q) :
    ∃ σ : F ≃ₐ[K] F,
      σ ∈ Q.inertia Gal(F/K) ∧ (σ.restrictScalars A).mapIntegralClosure = τ := by
  obtain ⟨σ, hσ⟩ := integralClosure_restrictScalars_surjective A K F τ
  exact ⟨σ, mem_inertia_of_normalization_restriction A K F Q σ τ hσ hτ, hσ⟩

end EtaleFundamentalGroups.Inertia
