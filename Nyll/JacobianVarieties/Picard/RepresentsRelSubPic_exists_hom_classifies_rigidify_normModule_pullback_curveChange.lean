/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_normModule_pullback_curveChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_existsUnique_hom_of_transform
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_normModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_normModule_iso
import Nyll.JacobianVarieties.Picard.FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Nyll.JacobianVarieties.Picard.IsPullback_baseChangeSnd_curveChange
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_pullbackMap_of_comp_eq

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Norms after changing the curve

Construct the represented Picard endomorphism induced by pullback and the norm.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NormCurveMap
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
attribute [-simp]
  AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard


universe u

noncomputable section

namespace CorrEndAux

universe v

section CurveChange

variable {R : Type v} [CommRing R] {C E : Scheme.{v}}
  {c : C ⟶ Spec (CommRingCat.of R)} {y : E ⟶ Spec (CommRingCat.of R)}
  (p : E ⟶ C) (hp : p ≫ c = y)

theorem isFinite_curveChange [IsFinite p] {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange p hp t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite p› (inferInstance : IsFinite (𝟙 T))
    hp.symm
    (Category.id_comp t).symm

theorem flat_curveChange [Flat p] {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Flat (curveChange p hp t) :=
  MorphismProperty.pullbackMap (P := @Flat) ‹Flat p› (inferInstance : Flat (𝟙 T)) hp.symm
    (Category.id_comp t).symm

theorem locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation p] {T : Scheme.{v}}
    (t : T ⟶ Spec (CommRingCat.of R)) : LocallyOfFinitePresentation (curveChange p hp t) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation p›
    (inferInstance : LocallyOfFinitePresentation (𝟙 T)) hp.symm (Category.id_comp t).symm

theorem finrank_curveChange [Flat p] [IsFinite p] {d : ℕ} (hd : ∀ x : C, p.finrank x = d)
    {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∀ z, (curveChange p hp t).finrank z = d :=
  fun z => (Scheme.Hom.finrank_pullbackMap_of_comp_eq c y t p hp z).trans (hd _)

end CurveChange

section Transform

variable {R : Type v} [CommRing R] {C E : Scheme.{v}}
  {c : C ⟶ Spec (CommRingCat.of R)} {y : E ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  (p e : E ⟶ C) (hp : p ≫ c = y) (he : e ≫ c = y)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (d : ℕ) (hd : ∀ x : C, p.finrank x = d)

/-- The underlying line bundle pulled back along the second curve map. -/
abbrev pulled {T : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    (pullback y t).Modules :=
  (Scheme.Modules.pullback (curveChange e he t)).obj M.L

theorem pulled_isInvertible {T : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible (pulled e he M) :=
  M.isInvertible.pullback _

theorem hfae {T : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) :
    ∀ (k : Type v) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt y t s)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd y t) s)).obj (pulled e he M)) := by
  intro k _ _ s
  let f : Limits.pullback (pullback.snd y t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange e he t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by rw [Category.comp_id, Category.id_comp])
  have hf : f ≫ fibreAt c t s = fibreAt y t s := by
    simp only [f, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : f ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd y t) s ≫ curveChange e he t := by
    simp only [f, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback f hf)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

include hd

theorem hinv {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange p hp t) d (pulled e he M))
      :=
  have := isFinite_curveChange p hp t
  have := flat_curveChange p hp t
  have := locallyOfFinitePresentation_curveChange p hp t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange p hp hd t) (pulled_isInvertible e
    he M)

/-- The rigidified norm of the pulled-back line bundle. -/
def Phi {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange p hp t) d (pulled e he M)) (hinv p e hp he d hd t M)

theorem hcongr {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi (ε := ε) p e hp he d hd t M).L ≅ (Phi (ε := ε) p e hp he d hd t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.normModuleMapIso _ d ((Scheme.Modules.pullback _).mapIso h.some))

theorem hcut {T : Scheme.{v}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε := ε) p e hp he d hd t M) :=
  FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) p hp d hd (pulled e he M)
    (pulled_isInvertible e he M) (hfae e he M hM) (hinv p e hp he d hd t M)

theorem hnat {T T' : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi (ε := ε) p e hp he d hd t M).pullbackAlong ψ).L ≅
      (Phi (ε := ε) p e hp he d hd t' (M.pullbackAlong ψ)).L) := by
  have := isFinite_curveChange p hp t
  have := flat_curveChange p hp t
  have := locallyOfFinitePresentation_curveChange p hp t
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) ψ
    (hinv p e hp he d hd t M)
  obtain ⟨e2⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange p hp t) d
    (finrank_curveChange p hp hd t) (baseChangeSnd c ψ) (curveChange p hp t') (baseChangeSnd y ψ)
    (isPullback_baseChangeSnd_curveChange p hp ψ) (pulled_isInvertible e he M)
  let e3 : (Scheme.Modules.pullback (baseChangeSnd y ψ)).obj (pulled e he M) ≅ pulled e he
    (M.pullbackAlong ψ) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd e he ψ).symm).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  obtain ⟨e4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((hinv p e hp he d hd t M).pullback (baseChangeSnd c ψ)) (hinv p e hp he d hd t'
      (M.pullbackAlong ψ))
    (e2 ≪≫ Scheme.Modules.normModuleMapIso _ d e3)
  exact ⟨e1 ≪≫ e4⟩

end Transform

end CorrEndAux

end

end JacobianVarieties.Picard.Proofs.NormCurveMap

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian

universe u

open _root_.JacobianVarieties.Picard.Proofs in
open NormCurveMap.CorrEndAux in
theorem RepresentsRelSubPic.exists_hom_classifies_rigidify_normModule_pullback_curveChange
    {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of
      R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {E : Scheme.{u}} (y : E ⟶ Spec (CommRingCat.of R)) (p e : E ⟶ C) (hp : p ≫ c = y) (he : e ≫ c =
      y)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] (d : ℕ) (hd : ∀ x : C, p.finrank x = d) :
    ∃ u : SchemeHomOver D.toBase D.toBase,
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
          Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
            (Scheme.Modules.normModule (curveChange (c := c) (c' := y) p hp t) d
              ((Scheme.Modules.pullback (curveChange (c := c) (c' := y) e he t)).obj
                (h.poincare.pullbackAlong b).L))) := by
  obtain ⟨u, hu, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform h h
    (Phi (ε := ε) p e hp he d hd)
    (fun t M M' i => hcongr (ε := ε) p e hp he d hd t M M' i)
    (fun ψ M => hnat (ε := ε) p e hp he d hd ψ M)
    (fun t M hM => hcut (ε := ε) p e hp he d hd t M hM)
  refine ⟨u, ?_⟩
  intro S t b
  let M : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong b
  have hM : (algEquivZeroCut c ε).P t M := (algEquivZeroCut c ε).pullback_mem _ _ b _ h.poincare_mem
  have hb : b = h.classify t M hM := h.classify_unique _ M hM b ⟨Iso.refl _⟩
  have hub : postComp u b = h.classify t (Phi (ε := ε) p e hp he d hd t M) (hcut (ε := ε) p e hp he
    d hd t M hM) := by
    conv_lhs => rw [hb]
    exact hu t M hM
  have hcomp : NeronModelInfra.schemeHomOverComp b u = postComp u b := rfl
  rw [hcomp, hub]
  exact h.classify_spec _ _ _
end AlgebraicGeometry.RelPicard
end ProofImplementation
