/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Scheme Ideal Sheaf Data exists iso subscheme comap of support subset range
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsOpenImmersion ψ]
    (h : (I.support : Set X) ⊆ Set.range ψ) :
    ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ :=
      by
  have hZU : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range ⇑ψ := by
    intro z
    apply h
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  let _ : IsIso (pullback.snd ψ I.subschemeι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  refine ⟨I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
end Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
