/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Iso
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.Pullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare
import AlgebraicCurves.Geometry.Schemes.IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced

/-!
# Scheme Modules exists is Invertible pullback curve Change iso of closed Cover
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
open _root_.PresheafOfModules.InternalHom in
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.instMonoidalClosed
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

namespace GTExists

theorem isClosedImmersion_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c
      = c')
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion f] : IsClosedImmersion (curveChange f hf
      t) := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  have hcomm : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  have sq : IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f :=
    IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance

end GTExists

open _root_.AlgebraicGeometry.IsClosedImmersion in
theorem
_root_.AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred :
      IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec
      (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion
      i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫
      curveChange i₂.1 i₂.2 t)
    (L₁ : (Limits.pullback y₁ t).Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (L₂ : (Limits.pullback y₂ t).Modules) (hL₂ : Scheme.Modules.IsInvertible L₂)
    (φ : (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).obj L₁ ≅
      (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).obj L₂) :
    ∃ (L : (Limits.pullback x t).Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (α₁ : (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj L ≅ L₁)
        (α₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj L ≅ L₂),
        (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).map α₁.hom ≫ φ.hom =
          ((Scheme.Modules.pullbackComp (curveChange j₁.1 j₁.2 t) (curveChange i₁.1 i₁.2 t)).app
            L).hom ≫
            ((Scheme.Modules.pullbackCongr hsq).app L).hom ≫
            ((Scheme.Modules.pullbackComp (curveChange j₂.1 j₂.2 t) (curveChange i₂.1 i₂.2 t)).app
              L).inv ≫
            (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).map α₂.hom := by
  have := GTExists.isClosedImmersion_curveChange i₁.1 i₁.2 t
  have := GTExists.isClosedImmersion_curveChange i₂.1 i₂.2 t
  have : IsClosedImmersion j₂.1 := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hZ
    inferInstance
  have := GTExists.isClosedImmersion_curveChange (c := y₂) j₂.1 j₂.2 t
  exact AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_iso_of_milnorSquare
    (curveChange i₁.1 i₁.2 t) (curveChange i₂.1 i₂.2 t) (curveChange j₁.1 j₁.2 t) (curveChange j₂.1
      j₂.2 t) hsq
    (fun U => app_curveChange_injective_and_exists_of_app_eq_of_isReduced
      x hXred y₁ y₂ z i₁ i₂ hjs j₁ j₂ hZ t hsq U)
    L₁ hL₁ L₂ hL₂ φ
end Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
