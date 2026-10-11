/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.exists_isAffineOpen_le_inf_forall_mem_of_finset

/-!
# exists is Affine Open opens le preimage forall mem of forall finset
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    {X : Scheme.{u}}
    (hAF : ∀ G : Finset X, ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W)
    (U O : X.Opens) (F : Finset ↥U) (hFO : ∀ x ∈ F, U.ι.base x ∈ O) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ O ∧ ∀ x ∈ F, x ∈ W := by
  classical
  obtain ⟨W₁, hW₁, hFW₁⟩ := hAF (F.image fun x => U.ι.base x)
  obtain ⟨W₂, hW₂, hle, hFW₂⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset W₁ hW₁ (U ⊓ O)
      (F.image fun x => U.ι.base x) hFW₁ (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨x.2, hFO x hx⟩)
  have hW₂U : W₂ ≤ U := (hle.trans inf_le_right).trans inf_le_left
  refine ⟨U.ι ⁻¹ᵁ W₂, hW₂.preimage_of_isOpenImmersion U.ι
    (by rwa [Scheme.Opens.opensRange_ι]), ?_, ?_⟩
  · exact Scheme.Hom.preimage_mono _ ((hle.trans inf_le_right).trans inf_le_right)
  · intro x hx
    exact hFW₂ _ (Finset.mem_image_of_mem _ hx)
end exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
