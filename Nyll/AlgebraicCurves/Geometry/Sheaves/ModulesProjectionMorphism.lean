/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesProjectionMorphism.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal

/-!
# Projection morphisms for module sheaves

The monoidal pullback comparison and adjunction counit define a projection morphism
and its mate under the pullback-pushforward adjunction.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The morphism from the pullback of `i_* 𝟙 ⊗ F` to `i^* F` obtained from the monoidal comparison,
  counit, and left unitor. -/
def projectionMorphismMate (F : X.Modules) :
    (Modules.pullback i).obj ((Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ⟶ (Modules.pullback
        i).obj F :=
  (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
    ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
    (λ_ ((Modules.pullback i).obj F)).hom

/-- The projection morphism `i_* 𝟙 ⊗ F ⟶ i_* i^* F`, adjoint to `projectionMorphismMate i F`. -/
def projectionMorphism (F : X.Modules) :
    (Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F ⟶ (Modules.pushforward i).obj ((Modules.pullback
        i).obj F) :=
  ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F)

theorem projectionMorphism_def (F : X.Modules) :
    projectionMorphism i F = ((pullbackPushforwardAdjunction i).homEquiv _ _)
        (projectionMorphismMate i F) := rfl

theorem projectionMorphismMate_def (F : X.Modules) :
    projectionMorphismMate i F =
      (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules))
          F).inv ≫
        ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
        (λ_ ((Modules.pullback i).obj F)).hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
