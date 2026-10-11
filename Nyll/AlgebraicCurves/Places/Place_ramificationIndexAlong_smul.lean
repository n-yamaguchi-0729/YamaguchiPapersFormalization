/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ramificationIndexAlong_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Place ramification Index Along smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_smul

noncomputable section

open AlgebraicCurve

namespace FibreSolG

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f :
  F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_iff (σ : F' ≃ₐ[K] F') (w : Place K F') (x : F') :
    x ∈ (σ • w).toValuationSubring ↔ σ.symm x ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w :
  Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem smul_restrictAlong (W : Place K F') :
    (σ • W).restrictAlong α hα = τ • (W.restrictAlong β hβ) := by
  ext f
  rw [mem_restrictAlong_iff, mem_smul_iff, sq_symm α β σ τ h,
    show f ∈ (τ • W.restrictAlong β hβ).toValuationSubring ↔ τ.symm f ∈ (W.restrictAlong β
      hβ).toValuationSubring from by
      rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl,
    mem_restrictAlong_iff]

theorem ramificationIndexAlong_smul (W : Place K F') :
    (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by
  change sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (σ • W).ord (α f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (β f) = n}
  congr 1
  ext n
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ.symm f, by simpa using hf, ?_⟩
    rw [← hn, ← sq_symm α β σ τ h f, ← Place.ord_smul σ W (σ.symm (α f)), AlgEquiv.apply_symm_apply]
  · rintro ⟨g, hg, hn⟩
    refine ⟨τ g, by simpa using hg, ?_⟩
    rw [← hn, h g, Place.ord_smul]

theorem inertiaDegAlong_smul (W : Place K F') (hdeg : (W.restrictAlong β hβ).deg = 1) :
    (σ • W).inertiaDegAlong α hα = W.inertiaDegAlong β hβ := by
  have h1 := deg_restrictAlong_mul_inertiaDegAlong (K := K) α hα (σ • W)
  have h2 := deg_restrictAlong_mul_inertiaDegAlong (K := K) β hβ W
  rw [smul_restrictAlong α β hα hβ σ τ h, Place.deg_smul, hdeg, one_mul, Place.deg_smul] at h1
  rw [hdeg, one_mul] at h2
  rw [h1, h2]

end Generic

end FibreSolG

end

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.ramificationIndexAlong_smul {K F F' : Type*} [Field K] [Field
  F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F)
  (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).ramificationIndexAlong α =
  W.ramificationIndexAlong β :=
  FibreSolG.ramificationIndexAlong_smul α β σ τ h W
end AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_smul
end ProofImplementation
