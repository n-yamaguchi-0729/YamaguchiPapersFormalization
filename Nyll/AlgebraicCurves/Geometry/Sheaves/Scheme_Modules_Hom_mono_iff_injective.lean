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

import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Ext
import Mathlib.Tactic.TermCongr

/-!
# Monomorphisms of module sheaves

Characterizes monomorphisms of scheme modules by injectivity on sections.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_mono_iff_injective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Mono φ ↔ ∀ U : X.Opens, Function.Injective (φ.app U) := by
  constructor
  · intro hφ U
    let ev : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} := (CategoryTheory.evaluation _ Ab.{u}).obj (op U)
    have : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
      preserves_mono_of_preservesLimit (Scheme.Modules.toPresheaf X) φ
    have : PreservesLimitsOfShape WalkingCospan ev := evaluation_preservesLimitsOfShape _
    have : Mono (ev.map ((Scheme.Modules.toPresheaf X).map φ)) :=
      preserves_mono_of_preservesLimit _ _
    have h : Mono (φ.app U) := this
    exact (AddCommGrpCat.mono_iff_injective (φ.app U)).1 h
  · intro h
    refine ⟨fun g g' w => ?_⟩
    refine Scheme.Modules.hom_ext g g' fun U => ?_
    ext x
    apply h U
    have := congr(($w).app U x)
    simpa [Scheme.Modules.Hom.comp_app] using this
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_mono_iff_injective
end ProofImplementation
