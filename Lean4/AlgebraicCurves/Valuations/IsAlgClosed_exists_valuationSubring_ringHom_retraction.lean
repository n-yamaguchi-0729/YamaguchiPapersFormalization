/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Valuations.ValuationSubring_exists_ringHom_extend_of_isAlgClosed

/-!
# Is Alg Closed exists valuation Subring ring Hom retraction
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs.IsAlgClosed_exists_valuationSubring_ringHom_retraction

theorem _root_.IsAlgClosed.exists_valuationSubring_ringHom_retraction
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by
  let f : K →+* K' := algebraMap K K'
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) f.range e.symm.toRingHom
  refine ⟨O, fun c => hRO ⟨c, rfl⟩, ψ, hker, fun c => ?_⟩
  have h1 : ψ (Subring.inclusion hRO ⟨f c, ⟨c, rfl⟩⟩) = e.symm ⟨f c, ⟨c, rfl⟩⟩ := by
    rw [← RingHom.comp_apply, hψ]; rfl
  have h2 : e.symm ⟨f c, ⟨c, rfl⟩⟩ = c := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h2] at h1
  exact h1
end AlgebraicCurves.Valuations.Proofs.IsAlgClosed_exists_valuationSubring_ringHom_retraction
end ProofImplementation
