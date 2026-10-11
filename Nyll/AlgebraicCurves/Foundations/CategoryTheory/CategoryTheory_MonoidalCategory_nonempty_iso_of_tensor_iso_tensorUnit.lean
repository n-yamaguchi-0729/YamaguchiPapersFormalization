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

import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Isomorphisms detected by tensoring with an invertible object

Cancels a tensor factor equipped with a tensor inverse in a braided monoidal category.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CategoryTheory.Proofs
namespace CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit

universe v u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

theorem _root_.CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit {C : Type
  u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C)) (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N') := by
  obtain ⟨i⟩ := h
  obtain ⟨i'⟩ := h'
  exact ⟨(ρ_ N).symm ≪≫ (Iso.refl N ⊗ᵢ i'.symm) ≪≫ (α_ N M' N').symm ≪≫
    ((β_ N M') ⊗ᵢ Iso.refl N') ≪≫ ((e.symm ⊗ᵢ Iso.refl N) ⊗ᵢ Iso.refl N') ≪≫
    (i ⊗ᵢ Iso.refl N') ≪≫ λ_ N'⟩
end CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
end AlgebraicCurves.Foundations.CategoryTheory.Proofs
end ProofImplementation
