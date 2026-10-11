/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_hasValue_smul_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Value

/-!
# Place has Value smul iff
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_hasValue_smul_iff

open AlgebraicCurve IsLocalRing

theorem _root_.AlgebraicCurve.Place.hasValue_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K
  F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by
  have one : ∀ (τ : F ≃ₐ[K] F) (w : Place K F) (x : F), w.HasValue x a → (τ • w).HasValue (τ x) a
    := by
    intro τ w x ⟨hx, hres⟩
    let e := Place.smulRingEquiv τ w.toValuationSubring
    have hmem : τ x ∈ (τ • w).toValuationSubring := (e ⟨x, hx⟩).2
    refine ⟨hmem, ?_⟩
    have hex : (⟨τ x, hmem⟩ : (τ • w).toValuationSubring) = e ⟨x, hx⟩ := Subtype.ext rfl
    have key : (Place.smulResidueAlgEquiv τ w) (residue w.toValuationSubring ⟨x, hx⟩)
        = residue (τ • w).toValuationSubring (e ⟨x, hx⟩) := by
      change IsLocalRing.ResidueField.mapEquiv _ (residue _ _) = residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    rw [hex, ← key, hres, AlgEquiv.commutes]
  refine ⟨fun h => ?_, one σ v g⟩
  have := one σ⁻¹ (σ • v) (σ g) h
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this
end AlgebraicCurves.Places.Proofs.Place_hasValue_smul_iff
end ProofImplementation
