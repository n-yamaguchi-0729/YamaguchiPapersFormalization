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

import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesProjectionMorphism

/-!
# The counit and the projection morphism

Pulling back the projection morphism and composing with the counit gives its adjoint mate.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_pullback_map_projectionMorphism_comp_counit

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.pullback_map_projectionMorphism_comp_counit
    {Z X : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback i).map (Scheme.Modules.projectionMorphism i F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app ((Scheme.Modules.pullback i).obj
            F) =
      Scheme.Modules.projectionMorphismMate i F := by
  have h := Adjunction.homEquiv_counit (adj := Scheme.Modules.pullbackPushforwardAdjunction i)
    (g := Scheme.Modules.projectionMorphism i F)
  rw [Scheme.Modules.projectionMorphism_def, Equiv.symm_apply_apply] at h
  rw [Scheme.Modules.projectionMorphism_def]
  exact h.symm
end Scheme_Modules_pullback_map_projectionMorphism_comp_counit
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
