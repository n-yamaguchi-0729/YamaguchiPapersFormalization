/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CategoryTheory.Reassoc
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Picard.Functor

/-!
# Scheme Modules pullback Comp hom app comp pullback Unit Iso hom
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.PullbackUnitComposition

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.hom_ext Scheme.Modules.pullback Scheme.Hom Scheme
  Scheme.Hom.comp_app Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.pullbackUnitIso)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.hom_ext ringCatSheaf Modules.pullback Hom Γ
  Hom.comp_app Modules Opens Modules.pullbackComp Modules.pullbackUnitIso)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (hom_ext pushforward pushforwardComp pullback
  Hom.comp_app Hom pushforward_map_app pullbackPushforwardAdjunction
  conjugateEquiv_pullbackComp_inv pullbackComp pullbackUnitIso)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical morphism from the unit module to the pushforward of the unit module, induced by
the scheme morphism on functions. -/
noncomputable def unitHom : @Quiver.Hom Y.Modules _ (SheafOfModules.unit Y.ringCatSheaf)
    ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitHom_app (U : Y.Opens) (x : Γ(SheafOfModules.unit Y.ringCatSheaf, U)) :
    (unitHom f).app U x = f.app U x := rfl

theorem homEquiv_pullbackUnitIso_hom :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom = unitHom f := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit (φ :=
    f.toRingCatSheafHom)
  exact h

theorem unitHom_comp :
    unitHom (f ≫ g) = unitHom g ≫ (pushforward g).map (unitHom f) ≫
      (pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [unitHom_app, Scheme.Hom.comp_app]
  rfl

theorem homEquiv_comp_map_pullbackUnitIso :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv _ _
        ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom) =
      unitHom g ≫ (pushforward g).map (unitHom f) := by
  rw [Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction g).homEquiv _ _ ((pullbackPushforwardAdjunction
    f).homEquiv _ _
    ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom)) = _
  have h₁ : (pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom) = (pullbackUnitIso
        g).hom ≫ unitHom f := by
    rw [← homEquiv_pullbackUnitIso_hom f]
    exact (pullbackPushforwardAdjunction f).homEquiv_naturality_left _ _
  rw [h₁, ← homEquiv_pullbackUnitIso_hom g]
  exact (pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _
theorem pullbackUnitIso_comp :
    (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso (f ≫
      g)).hom =
      (pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom := by
  let P : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let e := (pullbackComp f g).app P
  apply (Iso.cancel_iso_inv_left e _ _).mp
  refine (e.inv_hom_id_assoc (pullbackUnitIso (f ≫ g)).hom).trans ?_
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_pullbackUnitIso_hom, unitHom_comp]
  have key := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv (SheafOfModules.unit
      Z.ringCatSheaf)
  rw [conjugateEquiv_pullbackComp_inv] at key
  let A : X.Modules := (pullback g ⋙ pullback f).obj P
  let Q : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let h : A ⟶ Q := (pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom
  let R := pushforward f ⋙ pushforward g
  let S := pushforward (f ≫ g)
  let α : R ⟶ S := (pushforwardComp f g).hom
  let η := ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit
  let η' := (pullbackPushforwardAdjunction (f ≫ g)).unit
  have e₂ : η.app P ≫ R.map h = unitHom g ≫ (pushforward g).map (unitHom f) :=
    homEquiv_comp_map_pullbackUnitIso f g
  have hk : η.app P ≫ α.app A = η'.app P ≫ S.map e.inv := key
  change unitHom g ≫ (pushforward g).map (unitHom f) ≫ α.app Q =
    η'.app P ≫ S.map (e.inv ≫ h)
  calc
    _ = (unitHom g ≫ (pushforward g).map (unitHom f)) ≫ α.app Q :=
      (Category.assoc _ _ _).symm
    _ = (η.app P ≫ R.map h) ≫ α.app Q :=
      congrArg (fun k : P ⟶ R.obj Q => k ≫ α.app Q) e₂.symm
    _ = η.app P ≫ (R.map h ≫ α.app Q) := Category.assoc _ _ _
    _ = η.app P ≫ (α.app A ≫ S.map h) :=
      congrArg (fun k : R.obj A ⟶ S.obj Q => η.app P ≫ k) (α.naturality h)
    _ = (η.app P ≫ α.app A) ≫ S.map h := (Category.assoc _ _ _).symm
    _ = (η'.app P ≫ S.map e.inv) ≫ S.map h :=
      congrArg (fun k : P ⟶ S.obj A => k ≫ S.map h) hk
    _ = η'.app P ≫ S.map (e.inv ≫ h) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k : S.obj ((pullback (f ≫ g)).obj P) ⟶ S.obj Q => η'.app P ≫ k)
          (S.map_comp e.inv h).symm)

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom {X Y
  Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom :=
  AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp f g
end AlgebraicCurves.Geometry.Sheaves.Proofs.PullbackUnitComposition
end ProofImplementation
