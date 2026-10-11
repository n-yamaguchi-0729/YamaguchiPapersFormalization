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

import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_of_forall_exists_isFrameOn

/-!
# Scheme Modules is Invertible glue Of Cocycle
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isInvertible_glueOfCocycle


open _root_.CategoryTheory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


universe u

theorem _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c :
      Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by
  apply AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
  intro x
  have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Scheme.Modules.glueFrame c i, hi, Scheme.Modules.isFrameOn_glueFrame c i⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isInvertible_glueOfCocycle
end ProofImplementation
