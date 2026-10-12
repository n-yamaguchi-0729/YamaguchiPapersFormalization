/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_normModule_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Nyll.SchemeTheory.CategoryTheory.Pullback

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# Base change of the norm comparison for Poincaré bundles

The Poincaré bundle comparison with rigidified norms is preserved by base change.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FibreNormPoincare
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

universe u

namespace G7PinBC

open _root_.CategoryTheory.MonoidalCategory

section Rigidify

variable {T P P' : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (σ' : T ⟶ P') (q' : P' ⟶ T) (e : P' ⟶ P)
  (hσ : σ' ≫ e = σ) (hq : e ≫ q = q')

/-- Pullback commutes with rigidification along the compatible sections. -/
noncomputable def pullbackRigidifyIso (L : P.Modules) :
    (Scheme.Modules.pullback e).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback e).obj L) :=
  Scheme.Modules.pullbackTensorObjIso e L _ ≪≫
    (Iso.refl _ ⊗ᵢ
      (((Scheme.Modules.pullbackComp e q).app _) ≪≫ (Scheme.Modules.pullbackCongr hq).app _ ≪≫
        (Scheme.Modules.pullback q').mapIso
          (Scheme.Modules.dualMapIso
            (((Scheme.Modules.pullbackCongr hσ.symm).app L) ≪≫ ((Scheme.Modules.pullbackComp σ'
              e).app L).symm))))

end Rigidify

section BC

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (K : Type u) [CommRing K] [Algebra R K]

/-- Transport a module isomorphism through the base-change construction. -/
noncomputable def ofR_mapIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {M M' : RigidifiedLineBundle c ε (t ≫ specMap R K)} (e : M.L ≅ M'.L) :
    (BaseChange.ofR c ε K M).L ≅ (BaseChange.ofR c ε K M').L :=
  (Scheme.Modules.pullback (BaseChange.κ c K t).hom).mapIso e

/-- Base change commutes with pullback along a parameter morphism. -/
noncomputable def ofR_pullbackAlong_iso {T T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t'' : T'' ⟶ Spec (CommRingCat.of K)} (ψ : SchemeHomOver t'' t) (M : RigidifiedLineBundle c ε
      (t ≫ specMap R K)) :
    ((BaseChange.ofR c ε K M).pullbackAlong ψ).L ≅ (BaseChange.ofR c ε K (M.pullbackAlong
      (BaseChange.overR K ψ))).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c K) ψ) (BaseChange.κ c K t).hom).app
    M.L ≪≫
    (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_κ_hom c K ψ)).app M.L ≪≫
    ((Scheme.Modules.pullbackComp (BaseChange.κ c K t'').hom (baseChangeSnd c (BaseChange.overR K
      ψ))).app M.L).symm

variable (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
    (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
  (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
    (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- Project a point of the base-changed parameter scheme to the original scheme. -/
noncomputable def fstPoint (b : SchemeHomOver t (D.baseChange K).toBase) :
    SchemeHomOver (t ≫ specMap R K) D.toBase :=
  postComp ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩ (BaseChange.overR K b)

theorem fstPoint_coe (b : SchemeHomOver t (D.baseChange K).toBase) :
    (fstPoint c K D t b).1 = b.1 ≫ pullback.fst D.toBase (specMap R K) := rfl

/-- Compare the base-changed Poincaré bundle with its original pullback. -/
noncomputable def poincareOfRIso (b : SchemeHomOver t (D.baseChange K).toBase) :
    (h'.poincare.pullbackAlong b).L ≅ (BaseChange.ofR c ε K (h.poincare.pullbackAlong (fstPoint c K
      D t b))).L :=
  (Scheme.Modules.pullback (baseChangeSnd (baseChange R c K) b)).mapIso hP.some ≪≫
    ofR_pullbackAlong_iso c ε K b _ ≪≫
    ofR_mapIso c ε K (h.poincare.pullbackAlongPullbackAlongIso' _ _)

end BC

end G7PinBC

open G7PinBC
end JacobianVarieties.Picard.Proofs.FibreNormPoincare

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.FibreNormPoincare
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.NeronModelInfra _root_.GoodReductionJacobian _root_.AlgebraicGeometry.SmoothProperCurve
universe u
open _root_.JacobianVarieties.Picard.Proofs.FibreNormPoincare.G7PinBC

/-- The Poincaré bundle comparison with rigidified norms is preserved by base change. -/
theorem nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange_of_forall
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver
      (𝟙 (Spec (CommRingCat.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K]
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of R)} (πα πβ : SchemeHomOver c' c)
    [IsFinite πα.1] [Flat πα.1] [LocallyOfFinitePresentation πα.1] (d : ℕ) (hd : ∀ x : C,
      πα.1.finrank x = d)
    (φ : SchemeHomOver D.toBase D.toBase)
    (hφ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φ)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange πα.1 πα.2 t) d
            ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 t)).obj (h.poincare.pullbackAlong
              a).L))))
    (φK : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hφK : φK.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫ φ.1)
    (παK πβK : pullback c' (specMap R K) ⟶ pullback c (specMap R K))
    (hαK₁ : παK ≫ pullback.fst c (specMap R K) = pullback.fst c' (specMap R K) ≫ πα.1)
    (hαK₂ : παK ≫ pullback.snd c (specMap R K) = pullback.snd c' (specMap R K))
    (hβK₁ : πβK ≫ pullback.fst c (specMap R K) = pullback.fst c' (specMap R K) ≫ πβ.1)
    (hβK₂ : πβK ≫ pullback.snd c (specMap R K) = pullback.snd c' (specMap R K)) :
    ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t (D.baseChange
      K).toBase),
      Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φK)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange R c K) t (sectionBaseChange K ε))
          (pullback.snd (baseChange R c K) t)
          (Scheme.Modules.normModule
            (curveChange (c := baseChange R c K) (c' := pullback.snd c' (specMap R K)) παK hαK₂ t) d
            ((Scheme.Modules.pullback
                (curveChange (c := baseChange R c K) (c' := pullback.snd c' (specMap R K)) πβK hβK₂
                  t)).obj
              (h'.poincare.pullbackAlong a).L))) := by
  intro S t a
  classical
  let bK := specMap R K
  let κ := BaseChange.κ c K t
  let κ' := BaseChange.κ c' K t
  let aR := fstPoint c K D t a
  have hcoe : fstPoint c K D t (NeronModelInfra.schemeHomOverComp a φK) =
    NeronModelInfra.schemeHomOverComp aR φ := by
    apply Subtype.ext
    rw [fstPoint_coe, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc,
      hφK, ← Category.assoc]
    rfl
  let e1 : (h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φK)).L ≅
      (BaseChange.ofR c ε K (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp aR φ))).L
        :=
    poincareOfRIso c ε K D h h' hP t _ ≪≫ eqToIso (by rw [hcoe])
  let LR := (Scheme.Modules.pullback (curveChange πβ.1 πβ.2 (t ≫ bK))).obj
    (h.poincare.pullbackAlong aR).L
  let e2 := (Scheme.Modules.pullback κ.hom).mapIso (hφ (t ≫ bK) aR).some
  let e3 := pullbackRigidifyIso (rigSection c (t ≫ bK) ε) (pullback.snd c (t ≫ bK))
    (rigSection (baseChange R c K) t (sectionBaseChange K ε)) (pullback.snd (baseChange R c K) t)
      κ.hom
    (BaseChange.rigSection_κ_hom c ε K t) (BaseChange.κ_hom_snd c K t)
    (Scheme.Modules.normModule (curveChange πα.1 πα.2 (t ≫ bK)) d LR)
  have hsq : ∀ (π : SchemeHomOver c' c) (πK : pullback c' bK ⟶ pullback c bK)
      (h₁ : πK ≫ pullback.fst c bK = pullback.fst c' bK ≫ π.1) (h₂ : πK ≫ pullback.snd c bK =
        pullback.snd c' bK),
      κ'.hom ≫ curveChange π.1 π.2 (t ≫ bK) =
        curveChange (c := baseChange R c K) (c' := pullback.snd c' bK) πK h₂ t ≫ κ.hom := by
    intro π πK h₁ h₂
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_fst]
      simp only [curveChange, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, BaseChange.κ_hom_fst, Category.assoc, Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_snd]
      simp only [curveChange, pullback.lift_snd, Category.comp_id]
      rw [BaseChange.κ_hom_snd]
  have sqα := CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq c c' (t ≫ bK) πα.1 πα.2
  have : IsFinite (curveChange πα.1 πα.2 (t ≫ bK)) := MorphismProperty.of_isPullback (P :=
    @IsFinite) sqα inferInstance
  have : Flat (curveChange πα.1 πα.2 (t ≫ bK)) := MorphismProperty.of_isPullback (P := @Flat) sqα
    inferInstance
  have : LocallyOfFinitePresentation (curveChange πα.1 πα.2 (t ≫ bK)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqα inferInstance
  have hrk : ∀ z, (curveChange πα.1 πα.2 (t ≫ bK)).finrank z = d := fun z => by
    rw [curveChange, Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' (t ≫ bK) πα.1 πα.2, hd]
  have sqκ : IsPullback κ'.hom (curveChange (c := baseChange R c K) (c' := pullback.snd c' bK) παK
    hαK₂ t)
      (curveChange πα.1 πα.2 (t ≫ bK)) κ.hom :=
    IsPullback.of_horiz_isIso ⟨hsq πα παK hαK₁ hαK₂⟩
  have hLR : Scheme.Modules.IsInvertible LR := (h.poincare.pullbackAlong aR).isInvertible.pullback _
  obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange πα.1 πα.2 (t ≫ bK)) d
    hrk κ.hom
    (curveChange (c := baseChange R c K) (c' := pullback.snd c' bK) παK hαK₂ t) κ'.hom sqκ hLR
  let e5 : (Scheme.Modules.pullback κ'.hom).obj LR ≅
      (Scheme.Modules.pullback (curveChange (c := baseChange R c K) (c' := pullback.snd c' bK) πβK
        hβK₂ t)).obj
        (h'.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullbackComp κ'.hom _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (hsq πβ πβK hβK₁ hβK₂)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ κ.hom).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (poincareOfRIso c ε K D h h' hP t a).symm
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ Scheme.Modules.rigidifyMapIso _ _ (e4 ≪≫ Scheme.Modules.normModuleMapIso
    _ d e5)⟩
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
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
