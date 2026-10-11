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

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Tactic.Convert

/-!
# is Separated sigma Desc of forall is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isSeparated_sigmaDesc_of_forall_isSeparated

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
    {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsSeparated (f i)) : IsSeparated (Sigma.desc f) := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover X) (sigmaOpenCover X) (Sigma.desc f)
      (Sigma.desc f)) ?_
  rintro ⟨i, j⟩
  have H := pullback_map_diagonal_isPullback (Sigma.ι X i) (Sigma.ι X j) (Sigma.desc f)
  change IsClosedImmersion (pullback.snd (pullback.diagonal (Sigma.desc f))
    (pullback.map (Sigma.ι X i ≫ Sigma.desc f) (Sigma.ι X j ≫ Sigma.desc f) (Sigma.desc f)
      (Sigma.desc f)
      (Sigma.ι X i) (Sigma.ι X j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  by_cases hij : i = j
  · subst hij
    have hfi : Sigma.ι X i ≫ Sigma.desc f = f i := Sigma.ι_comp_desc _ _
    let _ : IsSeparated (Sigma.ι X i ≫ Sigma.desc f) := by rw [hfi]; exact hf i
    have hci : IsClosedImmersion
        (pullback.fst (Sigma.ι X i) (Sigma.ι X i) ≫ pullback.diagonal (Sigma.ι X i ≫ Sigma.desc f))
          :=
      inferInstance
    convert hci using 2
    apply pullback.hom_ext <;> simp [fst_eq_snd_of_mono_eq]
  · let _ : IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) := isEmpty_pullback_sigmaι_of_ne X hij
    infer_instance
end AlgebraicCurves.Geometry.Schemes.Proofs.isSeparated_sigmaDesc_of_forall_isSeparated
end ProofImplementation
