/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRigidify.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Monoidal

/-!
# Rigidification of sheaves of modules

Tensor a module with the pullback of the dual of its restriction to a chosen section.
Module isomorphisms induce isomorphisms of these rigidifications.
-/

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}

/-- The isomorphism of dual modules induced contravariantly by an isomorphism of modules. -/
def dualMapIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

/-- The module tensored with the pullback of the dual of its restriction to the section. -/
def rigidify (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) : P.Modules :=
  L ⊗ (Scheme.Modules.pullback q).obj
    (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))

lemma rigidify_def (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) :
    rigidify σ q L = L ⊗ (Scheme.Modules.pullback q).obj
      (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) := rfl

/-- The isomorphism of rigidified modules induced by the given module isomorphism. -/
def rigidifyMapIso (σ : T ⟶ P) (q : P ⟶ T) {L L' : P.Modules} (e : L ≅ L') :
    rigidify σ q L ≅ rigidify σ q L' :=
  e ⊗ᵢ (Scheme.Modules.pullback q).mapIso (dualMapIso ((Scheme.Modules.pullback σ).mapIso e))

end AlgebraicGeometry.Scheme.Modules

end
