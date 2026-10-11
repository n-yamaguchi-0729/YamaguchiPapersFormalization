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

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

/-!
# Scheme Modules is Invertible of forall exists is Frame On
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.LocalFramesInvertible

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn {X :
  AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧
      AlgebraicGeometry.Scheme.Modules.IsFrameOn s U) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, s, hx, hs⟩ := h x
  exact ⟨U, hx, AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hs U le_rfl
    le_rfl⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.LocalFramesInvertible
end ProofImplementation
