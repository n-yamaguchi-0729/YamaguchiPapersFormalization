/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Poincare fibres and rigidification over a field

Pulling back a classified rigidified bundle along a field-valued point recovers the
underlying pulled-back invertible module, using triviality of rigidification over a field.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PoincareRigidify
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.SmoothProperCurve


namespace K6H8

/-- An isomorphism of modules recovered from their pullbacks along an isomorphism. -/
noncomputable def isoOfPullbackIso' {P Q : Scheme.{u}} (φ : Q ⟶ P) [IsIso φ] {A B : P.Modules}
    (i : (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback φ).obj B) : A ≅ B :=
  ((Scheme.Modules.pullbackId P).app A).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm).app A ≪≫
    ((Scheme.Modules.pullbackComp (inv φ) φ).app A).symm ≪≫
    (Scheme.Modules.pullback (inv φ)).mapIso i ≪≫
    (Scheme.Modules.pullbackComp (inv φ) φ).app B ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app B ≪≫
    (Scheme.Modules.pullbackId P).app B

theorem nonempty_rigidify_iso_self' {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k))
    (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨i⟩ := Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
    σ q L hL k (𝟙 _)
  exact ⟨isoOfPullbackIso' (pullback.fst q (𝟙 _)) i⟩

end K6H8

open K6H8 in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    {B : Type u} [CommRing B] (ρ : R →+* B) {k' : Type u} [Field k']
    (t : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t (Spec.map (CommRingCat.ofHom ρ)))
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (N : (pullback cX (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (hN : Scheme.Modules.IsInvertible N)
    (isoA : (hrep.poincare.pullbackAlong a).L ≅
      Scheme.Modules.rigidify (rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε)
        (pullback.snd cX (Spec.map (CommRingCat.ofHom ρ))) N) :
    Nonempty ((hrep.poincare.pullbackAlong (postComp a ψ)).L ≅
      (Scheme.Modules.pullback (baseChangeSnd cX ψ)).obj N) := by
  have e1 : (hrep.poincare.pullbackAlong (postComp a ψ)).L ≅
    (Scheme.Modules.pullback (baseChangeSnd cX ψ)).obj (hrep.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp cX a ψ).symm).app hrep.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hrep.poincare.L).symm
  have hq : baseChangeSnd cX ψ ≫ pullback.snd cX (Spec.map (CommRingCat.ofHom ρ)) =
    pullback.snd cX t ≫ ψ.1 := by
    rw [AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_snd']
  have hσ : rigSection cX t ε ≫ baseChangeSnd cX ψ =
    ψ.1 ≫ rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε :=
    rigSection_baseChangeSnd cX ε ψ
  obtain ⟨e2⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    ψ.1 (baseChangeSnd cX ψ) hσ hq hN
  obtain ⟨e3⟩ := nonempty_rigidify_iso_self' (rigSection cX t ε) (pullback.snd cX t) _
    (hN.pullback (baseChangeSnd cX ψ))
  exact ⟨e1 ≪≫ (Scheme.Modules.pullback _).mapIso isoA ≪≫ e2 ≪≫ e3⟩
end JacobianVarieties.Picard.Proofs.PoincareRigidify
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
