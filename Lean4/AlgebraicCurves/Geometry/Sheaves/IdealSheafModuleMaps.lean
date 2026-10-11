/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModuleMaps.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule

/-!
# Maps between ideal modules under inverse image

The subscheme pullback map induces an ideal-module morphism and its adjoint
pullback comparison.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData)

open Opposite

/-- The canonical morphism from the inverse-image subscheme to the original subscheme. -/
abbrev comapSubschemeHom : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
@[reassoc]
lemma comapSubschemeHom_comp :
    I.comapSubschemeHom f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp [comapSubschemeHom]

lemma kernelι_unitToPushforwardUnit_map_eq_zero :
    (kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (I.comap f).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  set s : Γ(X, U.unop) := (kernel.ι I.subschemeι.unitToPushforwardUnit).val.app U m with hs_def
  have hs : I.subschemeι.app U.unop s = 0 := by
    have := congrArg (fun φ ↦ φ.val.app U m) (kernel.condition I.subschemeι.unitToPushforwardUnit)
    exact this
  have hs' : (I.subschemeι.app U.unop).hom s = 0 := hs
  have h0 : ((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s = 0 := by
    change ((I.comapSubschemeHom f).app _).hom ((I.subschemeι.app U.unop).hom s) = 0
    rw [hs', map_zero]
  have key := congrArg (fun φ ↦ φ.hom s)
    (Scheme.Hom.congr_app (I.comapSubschemeHom_comp f).symm U.unop)
  change (((I.comap f).subschemeι ≫ f).app U.unop).hom s = 0
  rw [key]
  change ((I.comap f).subscheme.presheaf.map _).hom
    (((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s) = 0
  rw [h0, map_zero]

/-- The ideal-module map induced by inverse image of the corresponding ideal sheaf. -/
def moduleToPushforwardComapModule :
    (I.module : SheafOfModules X.ringCatSheaf) ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (I.comap f).module := by
  have : (SheafOfModules.pushforward.{u}
      (F := TopologicalSpace.Opens.map f.base)
      (J := _root_.Opens.grothendieckTopology X)
      (K := _root_.Opens.grothendieckTopology X')
      f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫
    (PreservesKernel.iso (SheafOfModules.pushforward f.toRingCatSheafHom)
      (I.comap f).subschemeι.unitToPushforwardUnit).inv

/-- The pullback ideal-module map obtained from the pushforward map by adjunction. -/
def pullbackModuleComparison :
    (Scheme.Modules.pullback f).obj I.module ⟶ (I.comap f).module := by
  have : (SheafOfModules.pushforward.{u}
      (F := TopologicalSpace.Opens.map f.base)
      (J := _root_.Opens.grothendieckTopology X)
      (K := _root_.Opens.grothendieckTopology X')
      f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _).symm
    (I.moduleToPushforwardComapModule f)

end AlgebraicGeometry.Scheme.IdealSheafData

end
