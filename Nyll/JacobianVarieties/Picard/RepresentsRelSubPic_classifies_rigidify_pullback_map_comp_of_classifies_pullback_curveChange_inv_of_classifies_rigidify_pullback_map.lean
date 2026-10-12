/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classifies_rigidify_pullback_map_comp_of_classifies_pullback_curveChange_inv_of_classifies_rigidify_pullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-! Compatibility of rigidified pullback classification with composition. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackComposition
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

/-- A classifying endomorphism pulls back the Poincare bundle by the given curve map. -/
theorem CT_theta_pullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (g : C ⟶ C) (hg : g ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h.classify t N hN)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (postComp θ a)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        ((Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj
          (h.poincare.pullbackAlong a).L)) := by
  classical
  let P := h.poincare
  let cW : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)), pullback c s ⟶ pullback c s :=
    fun s => curveChange (c := c) (c' := c) g hg s
  have CUT : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R))
      (M : RigidifiedLineBundle c ε s), FibrewiseAlgEquivZero M →
      FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε)
        ((Scheme.Modules.pullback (cW s)).obj M.L) (M.isInvertible.pullback _)) := by
    intro S s M hM k _ _ x
    obtain ⟨e49⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
      (rigSection c s ε) (pullback.snd c s) ((Scheme.Modules.pullback (cW s)).obj M.L)
      (M.isInvertible.pullback _) k x
    rw [RigidifiedLineBundle.ofInvertible_L]
    refine IsAlgEquivZero.of_iso e49.symm ?_
    let e : Limits.pullback (pullback.snd c s) x ⟶ Limits.pullback (pullback.snd c s) x :=
      pullback.map _ _ _ _ (cW s) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, curveChange_snd]) (by rw [Category.id_comp, Category.comp_id])
    have he : e ≫ fibreAt c s x = fibreAt c s x := by
      simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
    have hfst : e ≫ pullback.fst (pullback.snd c s) x =
        pullback.fst (pullback.snd c s) x ≫ cW s := by
      simp only [e, pullback.lift_fst]
    refine IsAlgEquivZero.of_iso ?_ ((hM k x).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L
      ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  have IDpt : Nonempty ((P.pullbackAlong (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase
    D.toBase)).L ≅ P.L) := by
    have hb : baseChangeSnd c
        (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [BaseChange.baseChangeSnd_fst', Category.id_comp]
      · rw [BaseChange.baseChangeSnd_snd', Category.id_comp]; exact (Category.comp_id _).symm
    exact ⟨(Scheme.Modules.pullbackCongr hb).app _ ≪≫ (Scheme.Modules.pullbackId _).app _⟩
  let N₀ := RigidifiedLineBundle.ofInvertible (ε := ε) ((Scheme.Modules.pullback (cW D.toBase)).obj
    P.L) (P.isInvertible.pullback _)
  have hN₀ : FibrewiseAlgEquivZero N₀ := CUT D.toBase P h.poincare_mem
  have Iθ : Nonempty ((P.pullbackAlong θ).L ≅ N₀.L) := by
    have hid : (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) = h.classify
      D.toBase P h.poincare_mem :=
      h.classify_unique _ _ _ _ IDpt
    have hcl : postComp θ (h.classify D.toBase P h.poincare_mem) = h.classify D.toBase N₀ hN₀ :=
      hθ D.toBase P h.poincare_mem N₀ hN₀ (rigCorrection ε D.toBase ((Scheme.Modules.pullback (cW
        D.toBase)).obj P.L))
        (((P.isInvertible.pullback _).pullback _).dual).1 ⟨Iso.refl _⟩
    have hθeq : postComp θ (h.classify D.toBase P h.poincare_mem) = θ := by
      rw [← hid]; exact Subtype.ext (Category.id_comp _)
    rw [hθeq] at hcl
    rw [hcl]
    exact h.classify_spec D.toBase N₀ hN₀
  have hcWnat : ∀ {S S' : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)} {s' : S' ⟶ Spec
    (CommRingCat.of R)}
      (ψ : SchemeHomOver s' s), baseChangeSnd c ψ ≫ cW s = cW s' ≫ baseChangeSnd c ψ :=
    fun ψ => (curveChange_baseChangeSnd g hg ψ).symm
  obtain ⟨iθ⟩ := Iθ
  obtain ⟨inat⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) a
    (L := (Scheme.Modules.pullback (cW D.toBase)).obj P.L) (P.isInvertible.pullback _)
  have isq : (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((Scheme.Modules.pullback (cW
    D.toBase)).obj P.L) ≅
      (Scheme.Modules.pullback (cW t)).obj (P.pullbackAlong a).L :=
    (Scheme.Modules.pullbackComp _ _).app P.L ≪≫ (Scheme.Modules.pullbackCongr (hcWnat a)).app P.L
      ≪≫
      ((Scheme.Modules.pullbackComp _ _).app P.L).symm
  obtain ⟨icongr⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((P.isInvertible.pullback _).pullback _) ((P.pullbackAlong a).isInvertible.pullback _) isq
  refine ⟨(RigidifiedLineBundle.pullbackAlongPullbackAlongIso' P θ a).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c a)).mapIso iθ ≪≫ inat ≪≫ icongr ≪≫ ?_⟩
  rw [RigidifiedLineBundle.ofInvertible_L]

end JacobianVarieties.Picard.Proofs.PullbackComposition

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.PullbackComposition

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

universe u

/-- Compatibility of rigidified pullback classification with composition. -/
theorem classifies_rigidify_pullback_map_comp_of_curveChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (e : C ≅ C) (he' : e.inv ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) e.inv he' t)).obj
          M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h.classify t N hN)
    (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
    (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of R)))
    (f : C ⟶ C) (hf : f ≫ c = c ≫ β)
    (N : SchemeHomOver (D.toBase ≫ β') D.toBase)
    (hN :
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ :
              SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t f (𝟙 T) β hf.symm
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L)))) :
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ (N.1 ≫ θ.1), by
              rw [Category.assoc, Category.assoc, θ.2, N.2, ← Category.assoc, a.2]⟩ :
                SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t (e.inv ≫ f) (𝟙 T) β
                  (by rw [Category.assoc, hf, ← Category.assoc, he'])
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L))) := by
  intro T t a
  let t' : T ⟶ Spec (CommRingCat.of R) := t ≫ β'
  let x : SchemeHomOver t' D.toBase := ⟨a.1 ≫ N.1,
    by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩
  let Pa := (h.poincare.pullbackAlong a).L
  have hPa : Scheme.Modules.IsInvertible Pa := (h.poincare.pullbackAlong a).isInvertible
  let cc := curveChange (c := c) (c' := c) e.inv he' t'
  let mf := pullback.map c t' c t f (𝟙 T) β hf.symm
    (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp])
  let mg := pullback.map c t' c t (e.inv ≫ f) (𝟙 T) β
    (by rw [Category.assoc, hf, ← Category.assoc, he'])
    (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp])
  let q := pullback.snd c t'
  let σ := rigSection c t' ε
  have hσq : σ ≫ q = 𝟙 _ := by simp only [σ, q, rigSection, pullback.lift_snd]
  have hccq : cc ≫ q = q := curveChange_snd e.inv he' t'
  have hmaps : cc ≫ mf = mg := by
    apply pullback.hom_ext
    · simp only [cc, mf, mg, curveChange, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [cc, mf, mg, curveChange, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp]
  have hpt : (⟨a.1 ≫ (N.1 ≫ θ.1), by
      rw [Category.assoc, Category.assoc, θ.2, N.2, ← Category.assoc, a.2]⟩ :
        SchemeHomOver t' D.toBase) =
      postComp θ x := Subtype.ext (Category.assoc _ _ _).symm
  rw [hpt]
  obtain ⟨i1⟩ := CT_theta_pullback h e.inv he' θ (fun s M hM N' hN' Q hQ hiso => hθ s M hM N' hN' Q
    hQ hiso) t' x
  obtain ⟨i2⟩ := hN t a
  let X := (Scheme.Modules.pullback mf).obj Pa
  have hX : Scheme.Modules.IsInvertible X := hPa.pullback mf
  let Z := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj X)
  have hZ : Scheme.Modules.IsInvertible Z := (hX.pullback σ).dual.1
  refine ⟨i1 ≪≫ Scheme.Modules.rigidifyMapIso σ q
      ((Scheme.Modules.pullback cc).mapIso i2 ≪≫
        Scheme.Modules.pullbackTensorObjIso cc X ((Scheme.Modules.pullback q).obj Z) ≪≫
        whiskerLeftIso _ ((Scheme.Modules.pullbackComp cc q).app Z ≪≫ (Scheme.Modules.pullbackCongr
          hccq).app Z) ≪≫ β_ _ _) ≪≫
    (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso hσq hZ (hX.pullback
      cc)).some ≪≫
    Scheme.Modules.rigidifyMapIso σ q ((Scheme.Modules.pullbackComp cc mf).app Pa ≪≫
      (Scheme.Modules.pullbackCongr hmaps).app Pa)⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation

attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
