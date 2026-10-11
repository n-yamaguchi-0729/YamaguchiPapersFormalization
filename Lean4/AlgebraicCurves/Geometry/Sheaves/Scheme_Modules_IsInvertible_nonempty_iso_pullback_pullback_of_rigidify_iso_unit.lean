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

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Iso
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible

/-!
# Scheme Modules Is Invertible nonempty iso pullback pullback of rigidify iso unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


end Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit in
open _root_.CategoryTheory in
open _root_.CategoryTheory.MonoidalCategory in
open _root_.AlgebraicGeometry in
theorem nonempty_iso_pullback_pullback_of_rigidify_iso_unit
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) {L : P.Modules} (hL : Scheme.Modules.IsInvertible L)
    (e : Nonempty (Scheme.Modules.rigidify σ q L ≅ SheafOfModules.unit P.ringCatSheaf)) :
    Nonempty (L ≅ (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback σ).obj L)) := by
  obtain ⟨e⟩ := e
  obtain ⟨d⟩ := (hL.pullback σ).dual.2
  exact ⟨Scheme.Modules.isoOfTensorIsoUnit
    ((Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)))
    L ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback σ).obj L))
    (β_ _ _ ≪≫ e)
    (β_ _ _ ≪≫ (Scheme.Modules.pullbackTensorObjIso q _ _).symm ≪≫ (Scheme.Modules.pullback
      q).mapIso d ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q)⟩
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
attribute [-simp] AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
