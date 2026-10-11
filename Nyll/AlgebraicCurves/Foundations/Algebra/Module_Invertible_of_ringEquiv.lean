/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.PicardGroup

/-!
# Module Invertible of ring Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Module_Invertible_of_ringEquiv

universe u v

theorem _root_.Module.Invertible.of_ringEquiv
    {R R' : Type u} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    (M : Type v) [AddCommGroup M] [Module R' M] [Module.Invertible R' M]
    [Module R M] (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
    Module.Invertible R M := by
  let : Algebra R' R := σ.symm.toRingHom.toAlgebra
  have : IsScalarTower R' R M := ⟨fun r' r m => by
    rw [Algebra.smul_def, hσ, hσ r m, ← mul_smul]
    congr 1
    simp [RingHom.algebraMap_toAlgebra]⟩
  have : IsLocalization (⊥ : Submonoid R') R :=
    IsLocalization.of_le_isUnit_of_bijective
      (by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp)
      σ.symm.bijective
  have : IsLocalizedModule (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M) :=
    isLocalizedModule_id (S := (⊥ : Submonoid R')) (M := M) (R' := R)
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M)
end AlgebraicCurves.Foundations.Algebra.Proofs.Module_Invertible_of_ringEquiv
end ProofImplementation
