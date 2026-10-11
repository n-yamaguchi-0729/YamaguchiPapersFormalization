/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Ideal sheaves and their associated modules

Constructs the module morphisms associated to an ideal sheaf and its closed subscheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The canonical map from the structure module to the pushforward structure module. -/
abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

namespace Scheme.IdealSheafData

/-- The ideal module, realized as the kernel of the quotient structure-sheaf map. -/
def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)

/-- The inclusion of the ideal module into the structure module. -/
def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit

/-- The dual of the ideal module. -/
def invModule (I : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.dual I.module

end Scheme.IdealSheafData

/-- The ideal module of the relative effective Cartier divisor. -/
abbrev RelEffCartierDiv.idealModule {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.module

/-- The dual ideal module associated with the relative effective Cartier divisor. -/
abbrev RelEffCartierDiv.lineBundle {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.invModule

end AlgebraicGeometry

end
