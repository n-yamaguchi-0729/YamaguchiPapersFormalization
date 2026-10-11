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

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import SchemeTheory.Modules.PresheafInternalHom
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import SchemeTheory.Modules.PresheafPullbackMonoidal
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Modules Pullback Monoidal V2
-/

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance : (PresheafOfModules.pushforward.{u} (F := Opens.map f.base)
    f.toRingCatSheafHom.hom).IsRightAdjoint :=
  (PresheafOfModules.PullbackMonoidal.adj (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).isRightAdjoint

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
