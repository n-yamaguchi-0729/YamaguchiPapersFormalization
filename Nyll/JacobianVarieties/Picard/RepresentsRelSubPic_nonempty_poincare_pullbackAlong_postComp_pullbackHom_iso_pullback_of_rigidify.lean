/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

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

/-! Poincare line bundles under rigidified pullback and postcomposition. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PoincarePullbackHom
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

/-- Descend a pullback isomorphism along an isomorphism of schemes. -/
noncomputable def isoOfPullbackIso' {P Q : Scheme.{u}} (φ : Q ⟶ P) [IsIso φ] {A B : P.Modules}
    (i : (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback φ).obj B) : A ≅ B :=
  ((Scheme.Modules.pullbackId P).app A).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm).app A ≪≫
    ((Scheme.Modules.pullbackComp (inv φ) φ).app A).symm ≪≫
    (Scheme.Modules.pullback (inv φ)).mapIso i ≪≫
    (Scheme.Modules.pullbackComp (inv φ) φ).app B ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app B ≪≫
    (Scheme.Modules.pullbackId P).app B

/-- Rigidifying over a field preserves the underlying invertible module up to isomorphism. -/
theorem nonempty_rigidify_iso_self' {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k)) (L : P.Modules) (hL :
      Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨i⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
    σ q L hL k (𝟙 _)
  exact ⟨isoOfPullbackIso' (pullback.fst q (𝟙 _)) i⟩

end K6H8

end JacobianVarieties.Picard.Proofs.PoincarePullbackHom

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.SmoothProperCurve
namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

universe u

open JacobianVarieties.Picard.Proofs.PoincarePullbackHom.K6H8 in
/-- Poincare line bundles under rigidified pullback and postcomposition. -/
theorem nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    {C₁ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ (baseChange R cX
      k))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k
      ε).1)
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁)
      D₁)
    {B : Type u} [CommRing B] (ρ : R →+* B) (πk : B →+* k) (hAlgk : algebraMap R k = πk.comp ρ)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hya : y.1 ≫ pullback.fst D.toBase (specMap R k) = Spec.map (CommRingCat.ofHom πk) ≫ a.1)
    (N : (pullback cX (Spec.map (CommRingCat.ofHom ρ))).Modules) (hN : Scheme.Modules.IsInvertible
      N)
    (isoA : (hrep.poincare.pullbackAlong a).L ≅
      Scheme.Modules.rigidify (rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd cX
        (Spec.map (CommRingCat.ofHom ρ))) N) :
    let ψ : SchemeHomOver (𝟙 _ ≫ specMap R k) (Spec.map (CommRingCat.ofHom ρ)) :=
      ⟨Spec.map (CommRingCat.ofHom πk), by
        rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]⟩
    Nonempty ((hrep₁.poincare.pullbackAlong
        (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) y)).L ≅
      (Scheme.Modules.pullback
        (curveChange i₁.1 i₁.2 (𝟙 _) ≫ (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj N)
          := by
  intro ψ
  classical
  obtain ⟨e1⟩ := nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
    i₁.1 i₁.2 hε₁ hreps hrep₁ (𝟙 _) y
  have e1' : (hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁
    hreps hrep₁) y)).L ≅
      Scheme.Modules.rigidify (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _))
        ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong
          y).L) := e1
  obtain ⟨e2⟩ := nonempty_rigidify_iso_self' (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _)) _
    ((hreps.poincare.pullbackAlong y).isInvertible.pullback (curveChange i₁.1 i₁.2 (𝟙 _)))
  let ā : SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase := ⟨pullback.fst D.toBase
    (specMap R k), pullback.condition⟩
  have hcomp : baseChangeSnd (baseChange R cX k) y ≫ (BaseChange.κ cX k (D.baseChange
    k).toBase).hom ≫ baseChangeSnd cX ā =
      ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) ≫ baseChangeSnd cX a := by
    rw [← Category.assoc, BaseChange.baseChangeSnd_κ_hom, Category.assoc, Category.assoc,
      baseChangeSnd_comp, baseChangeSnd_comp]
    congr 2
    apply Subtype.ext
    change y.1 ≫ pullback.fst D.toBase (specMap R k) = Spec.map (CommRingCat.ofHom πk) ≫ a.1
    exact hya
  have e3 : (hreps.poincare.pullbackAlong y).L ≅
      (Scheme.Modules.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj
        (hrep.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) y)).mapIso hPk.some ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) y)).mapIso
        ((Scheme.Modules.pullbackComp (BaseChange.κ cX k (D.baseChange k).toBase).hom
          (baseChangeSnd cX ā)).app hrep.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hrep.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app hrep.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app hrep.poincare.L).symm
  have hq : ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) ≫ pullback.snd cX (Spec.map
    (CommRingCat.ofHom ρ)) =
      pullback.snd (baseChange R cX k) (𝟙 _) ≫ Spec.map (CommRingCat.ofHom πk) := by
    rw [Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  have hσ : rigSection (baseChange R cX k) (𝟙 _) (sectionBaseChange k ε) ≫ ((BaseChange.κ cX k (𝟙
    _)).hom ≫ baseChangeSnd cX ψ) =
      Spec.map (CommRingCat.ofHom πk) ≫ rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε := by
    rw [← Category.assoc, BaseChange.rigSection_κ_hom, rigSection_baseChangeSnd]
  obtain ⟨e4⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    (Spec.map (CommRingCat.ofHom πk)) ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ) hσ hq hN
  obtain ⟨e5⟩ := nonempty_rigidify_iso_self' (rigSection (baseChange R cX k) (𝟙 _)
    (sectionBaseChange k ε))
    (pullback.snd (baseChange R cX k) (𝟙 _)) _ (hN.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫
      baseChangeSnd cX ψ))
  have e6 : (hreps.poincare.pullbackAlong y).L ≅
      (Scheme.Modules.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj N :=
    e3 ≪≫ (Scheme.Modules.pullback _).mapIso isoA ≪≫ e4 ≪≫ e5
  exact ⟨e1' ≪≫ e2 ≪≫ (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).mapIso e6 ≪≫
    (Scheme.Modules.pullbackComp _ _).app N⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
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
