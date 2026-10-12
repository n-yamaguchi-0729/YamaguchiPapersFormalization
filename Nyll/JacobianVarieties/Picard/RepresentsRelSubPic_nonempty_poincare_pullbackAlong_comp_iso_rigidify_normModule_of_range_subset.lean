/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_normModule_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_morphismRestrict_eq_finrank

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# Restriction of the Poincaré norm comparison

The Poincaré norm comparison restricts to parameters whose image lies in the flat locus.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RestrictedNormPoincare
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

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  IsOpenImmersion.lift
  morphismRestrict_ι
  morphismRestrict_base_coe
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  IsFinite
  isPullback_morphismRestrict
  Spec
  Scheme
  IsOpenImmersion
  Flat
  Scheme.Hom.finrank_of_isPullback
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  Scheme.Opens
  LocallyOfFinitePresentation
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.rigidify
  Scheme.Modules.rigidifyMapIso
  Scheme.Modules.normModule
  Scheme.Modules.normModuleMapIso
  RelPicard.BaseChange.baseChangeSnd_fst'
  Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
  Scheme.Modules.nonempty_pullback_normModule_iso
  Scheme.Hom.finrank_morphismRestrict_eq_finrank)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  rigSection
  baseChangeSnd_comp
  rigSection_baseChangeSnd
  SubPicCondition
  RepresentsRelSubPic
  curveChange
  curveChange_baseChangeSnd
  curveChange_snd
  baseChangeSnd_snd
  BaseChange.baseChangeSnd_fst')

namespace C2_8f7a3a05

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}

private theorem curveChange_fst (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

private theorem isPullback_curveChange (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  exact (big.of_right (curveChange_fst f hf t) (IsPullback.of_hasPullback c t).flip).flip

private theorem exists_isPullback_curveChange_restrict (f : C' ⟶ C) (hf : f ≫ c = c')
    {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (U : C.Opens) :
    ∃ k : ↑((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)) ⟶ ↑(f ⁻¹ᵁ U),
      IsPullback k (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) (f ∣_ U) (pullback.fst c t ∣_
        U) := by
  have s : IsPullback
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t)
      (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) f (((pullback.fst c t) ⁻¹ᵁ U).ι ≫
        pullback.fst c t) :=
    (isPullback_morphismRestrict (curveChange f hf t) ((pullback.fst c t) ⁻¹ᵁ U)).flip.paste_horiz
      (isPullback_curveChange f hf t)
  have w : (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U ≫ pullback.fst c t ∣_ U) ≫ U.ι =
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t) ≫ f := by
    rw [Category.assoc, morphismRestrict_ι]
    exact s.w.symm
  refine ⟨(isPullback_morphismRestrict f U).lift _ _ w, ?_⟩
  refine IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ (IsPullback.lift_fst _ _ _ _)
    (isPullback_morphismRestrict f U).flip
  rw [IsPullback.lift_snd, morphismRestrict_ι]
  exact s

end AlgebraicGeometry.RelPicard.C2_8f7a3a05
end JacobianVarieties.Picard.Proofs.RestrictedNormPoincare

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs
open _root_.JacobianVarieties.Picard.Proofs.RestrictedNormPoincare
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
universe u

open RestrictedNormPoincare.AlgebraicGeometry.RelPicard.C2_8f7a3a05 in
/-- The Poincaré norm comparison restricts to parameters whose image lies in the flat locus. -/
theorem nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D)
    (πa πb : SchemeHomOver c' c) [IsFinite πa.1] [LocallyOfFinitePresentation πa.1]
    (U : C.Opens) (d : ℕ) (hfl : Flat (πa.1 ∣_ U)) (hrk : ∀ y : C, y ∈ U → πa.1.finrank y = d)
    (𝒩 : (pullback c D.toBase).Modules) (h𝒩 : Scheme.Modules.IsInvertible 𝒩)
    (hNe : ∀ (V : (pullback c D.toBase).Opens) (d' : ℕ),
      Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πa.1
        πa.2 D.toBase) ∣_ V) →
      (∀ y : V, ((curveChange πa.1 πa.2 D.toBase) ∣_ V).finrank y = d') →
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
        Scheme.Modules.normModule ((curveChange πa.1 πa.2 D.toBase) ∣_ V) d'
          ((Scheme.Modules.pullback ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι).obj
            ((Scheme.Modules.pullback (curveChange πb.1 πb.2 D.toBase)).obj h.poincare.L))))
    (T : SchemeHomOver D.toBase D.toBase)
    (hT : Nonempty ((h.poincare.pullbackAlong T).L ≅
      Scheme.Modules.rigidify (rigSection c D.toBase ε) (pullback.snd c D.toBase) 𝒩))
    {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase)
    (hU : Set.range (pullback.fst c t).base ⊆ (U : Set C)) :
    Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        (Scheme.Modules.normModule (curveChange πa.1 πa.2 t) d
          ((Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong
            a).L))) := by
  have e1 : (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
      (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((h.poincare.pullbackAlong T).L) := by
    change (Scheme.Modules.pullback (baseChangeSnd c (NeronModelInfra.schemeHomOverComp a T))).obj
      h.poincare.L ≅
      (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((Scheme.Modules.pullback (baseChangeSnd c
        T)).obj h.poincare.L)
    have hc : baseChangeSnd c (NeronModelInfra.schemeHomOverComp a T) = baseChangeSnd c a ≫
      baseChangeSnd c T :=
      (baseChangeSnd_comp c T a).symm
    exact (Scheme.Modules.pullbackCongr hc).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeSnd c a) (baseChangeSnd c T)).app h.poincare.L).symm
  obtain ⟨eT⟩ := hT
  obtain ⟨eR⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso (σ := rigSection c
    D.toBase ε)
    (q := pullback.snd c D.toBase) (σ' := rigSection c t ε) (q' := pullback.snd c t) a.1
      (baseChangeSnd c a)
    (rigSection_baseChangeSnd c ε a) (baseChangeSnd_snd (c := c) a) h𝒩
  let V : (pullback c D.toBase).Opens := (pullback.fst c D.toBase) ⁻¹ᵁ U
  have hgV : Set.range (baseChangeSnd c a).base ⊆ (V : Set ↥(pullback c D.toBase)) := by
    rintro _ ⟨x, rfl⟩
    change (pullback.fst c D.toBase).base ((baseChangeSnd c a).base x) ∈ U
    rw [← Scheme.Hom.comp_apply, AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst']
    exact hU ⟨x, rfl⟩
  have sqD := isPullback_curveChange (c := c) πa.1 πa.2 D.toBase
  obtain ⟨kV, sqV⟩ := exists_isPullback_curveChange_restrict (c := c) πa.1 πa.2 D.toBase U
  have : IsFinite (curveChange πa.1 πa.2 D.toBase) := MorphismProperty.of_isPullback sqD ‹_›
  have : LocallyOfFinitePresentation (curveChange πa.1 πa.2 D.toBase) :=
    MorphismProperty.of_isPullback sqD ‹_›
  have hflV : Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := by
    have : Flat (πa.1 ∣_ U) := hfl
    exact MorphismProperty.of_isPullback sqV ‹_›
  have hlfpV : LocallyOfFinitePresentation ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := inferInstance
  have hrkV : ∀ y : V, ((curveChange πa.1 πa.2 D.toBase) ∣_ V).finrank y = d := by
    intro y
    have : Flat (πa.1 ∣_ U) := hfl
    have hyU : (pullback.fst c D.toBase).base y.1 ∈ U := y.2
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqV y]
    have hy : ((pullback.fst c D.toBase) ∣_ U).base y = ⟨(pullback.fst c D.toBase).base y.1, hyU⟩ :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    rw [hy, Scheme.Hom.finrank_morphismRestrict_eq_finrank]
    exact hrk _ hyU
  obtain ⟨eN⟩ := hNe V d hflV hlfpV hrkV
  have hgV' : Set.range (baseChangeSnd c a).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hgV
  let g₀ : pullback c t ⟶ V := IsOpenImmersion.lift V.ι (baseChangeSnd c a) hgV'
  have hg₀ : g₀ ≫ V.ι = baseChangeSnd c a := IsOpenImmersion.lift_fac _ _ _
  have bigsq : IsPullback (baseChangeSnd c' a) (curveChange πa.1 πa.2 t) (curveChange πa.1 πa.2
    D.toBase)
      (baseChangeSnd c a) := by
    have s : IsPullback (baseChangeSnd c' a ≫ pullback.fst c' D.toBase) (curveChange πa.1 πa.2 t)
      πa.1
        (baseChangeSnd c a ≫ pullback.fst c D.toBase) := by
      rw [AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst',
        AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst']
      exact isPullback_curveChange (c := c) πa.1 πa.2 t
    exact s.of_right (curveChange_baseChangeSnd πa.1 πa.2 a).symm sqD
  have w2 : (curveChange πa.1 πa.2 t ≫ g₀) ≫ V.ι = baseChangeSnd c' a ≫ curveChange πa.1 πa.2
    D.toBase := by
    rw [Category.assoc, hg₀]; exact curveChange_baseChangeSnd πa.1 πa.2 a
  let g' := (isPullback_morphismRestrict (curveChange πa.1 πa.2 D.toBase) V).lift _ _ w2
  have hg' : g' ≫ ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι = baseChangeSnd c' a :=
    IsPullback.lift_snd _ _ _ _
  have sqg : IsPullback g' (curveChange πa.1 πa.2 t)
      ((curveChange πa.1 πa.2 D.toBase) ∣_ V) g₀ := by
    refine IsPullback.of_right (h₁₂ := ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι) (h₂₂ := V.ι) ?_
      (IsPullback.lift_fst _ _ _ _) (isPullback_morphismRestrict _ V).flip
    rw [hg', hg₀]; exact bigsq
  have : Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := hflV
  obtain ⟨eBC⟩ := Scheme.Modules.nonempty_pullback_normModule_iso ((curveChange πa.1 πa.2 D.toBase)
    ∣_ V) d hrkV
    g₀ (curveChange πa.1 πa.2 t) g' sqg ((h.poincare.isInvertible.pullback _).pullback _)
  have eL : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ((curveChange πa.1 πa.2
    D.toBase) ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback (curveChange πb.1 πb.2 D.toBase)).obj h.poincare.L)) ≅
      (Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullbackComp g' _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hg').app _ ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd c' a) (curveChange πb.1 πb.2 D.toBase)).app
        h.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd πb.1 πb.2 a).symm).app h.poincare.L
        ≪≫
      ((Scheme.Modules.pullbackComp (curveChange πb.1 πb.2 t) (baseChangeSnd c a)).app
        h.poincare.L).symm
  have e4 : (Scheme.Modules.pullback (baseChangeSnd c a)).obj 𝒩 ≅
      Scheme.Modules.normModule (curveChange πa.1 πa.2 t) d
        ((Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L) :=
    (Scheme.Modules.pullbackCongr hg₀.symm).app 𝒩 ≪≫ ((Scheme.Modules.pullbackComp g₀ V.ι).app
      𝒩).symm ≪≫
      (Scheme.Modules.pullback g₀).mapIso eN ≪≫ eBC ≪≫ Scheme.Modules.normModuleMapIso _ d eL
  exact ⟨e1 ≪≫ (Scheme.Modules.pullback (baseChangeSnd c a)).mapIso eT ≪≫ eR ≪≫
    Scheme.Modules.rigidifyMapIso _ _ e4⟩

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
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
attribute [-instance]
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
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
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
attribute [-simp]
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
