/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheaf isomorphisms detected on a basis

Detects an isomorphism of sheaves from its components on a basis of open sets.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CategoryTheory.Proofs
namespace TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open _root_.CategoryTheory Opposite TopologicalSpace

theorem _root_.TopCat.Sheaf.isIso_of_isIso_app_of_isBasis {C : Type u}
  [_root_.CategoryTheory.Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G :
      TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by
  have := TopCat.Opens.coverDense_inducedFunctor hB
  have : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this
end TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
end AlgebraicCurves.Foundations.CategoryTheory.Proofs
end ProofImplementation
