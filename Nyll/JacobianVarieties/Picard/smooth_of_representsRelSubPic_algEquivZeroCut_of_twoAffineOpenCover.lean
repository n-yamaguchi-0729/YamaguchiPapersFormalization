/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.LocalGeometry.LocalRepresentabilityULift
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf

/-!
# Smoothness of the represented relative Picard functor

Square-zero lifting of rigidified bundles supplies formal smoothness on affine charts.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    Smooth D.toBase := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  have hlfp : LocallyOfFinitePresentation D.toBase := inferInstance
  have : IsAffine (Spec (CommRingCat.of R)) := inferInstance
  refine HasRingHomProperty.of_source_openCover (P := @Smooth) D.P.affineCover ?_
  intro i
  have : IsAffine (D.P.affineCover.X i) := inferInstance
  have hlfp_i : LocallyOfFinitePresentation (D.P.affineCover.f i ≫ D.toBase) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ inferInstance hlfp
  set φ := ((D.P.affineCover.f i ≫ D.toBase).appTop).hom with hφ
  let : Algebra (Γ(Spec (CommRingCat.of R), ⊤))
      (Γ(D.P.affineCover.X i, ⊤)) := φ.toAlgebra
  refine { formallySmooth := ?fsm, finitePresentation := ?fp }
  case fp =>
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp hlfp_i
  case fsm =>
    refine Algebra.FormallySmooth.of_comp_surjective ?_
    intro B _ _ I hI2 ψ
    let : Algebra R B := RingHom.toAlgebra
      ((algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B).comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    have hI_nil : I ≤ _root_.nilradical B := fun a ha =>
      ⟨2, by have h2 := Ideal.pow_mem_pow ha 2; rw [hI2] at h2; exact Ideal.mem_bot.mp h2⟩
    have hι_comp : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    set ι : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
      ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)), hι_comp⟩ with hι_def
    let x₀ : Spec (CommRingCat.of (B ⧸ I)) ⟶ D.P.affineCover.X i :=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (D.P.affineCover.X i).isoSpec.inv
    have hx₀_over : (x₀ ≫ D.P.affineCover.f i) ≫ D.toBase =
        Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) := by
      have hnat : (D.P.affineCover.X i).isoSpec.inv ≫ (D.P.affineCover.f i ≫ D.toBase) =
          Spec.map ((D.P.affineCover.f i ≫ D.toBase).appTop) ≫
            (Spec (CommRingCat.of R)).isoSpec.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        exact (Scheme.isoSpec_hom_naturality (D.P.affineCover.f i ≫ D.toBase)).symm
      simp only [x₀, Category.assoc]; rw [hnat, ← Category.assoc, ← Spec.map_comp]
      rw [show (Spec (CommRingCat.of R)).isoSpec.inv =
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv from
          Scheme.isoSpec_Spec_inv (CommRingCat.of R), ← Spec.map_comp]
      congr 1
      ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      have h1 : ψ.toRingHom (((D.P.affineCover.f i ≫ D.toBase).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) =
          algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) (B ⧸ I)
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
        rw [← hφ]; exact (ψ.commutes _).symm |>.symm
      rw [h1]
      rfl
    set g₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) D.toBase :=
      ⟨x₀ ≫ D.P.affineCover.f i, hx₀_over⟩ with hg₀_def
    set M := h.poincare.pullbackAlong g₀ with hM_def
    have hM_cut : FibrewiseAlgEquivZero M :=
      (algEquivZeroCut c ε).pullback_mem _ _ g₀ _ h.poincare_mem
    obtain ⟨M', hM'_iso⟩ : ∃ M' : RigidifiedLineBundle c ε
          (Spec.map (CommRingCat.ofHom (algebraMap R B))),
        Nonempty ((M'.pullbackAlong ι).L ≅ M.L) :=
      RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover
        c ε 𝒱 I hI2 ι rfl M
    have hM'ι_cut : FibrewiseAlgEquivZero (M'.pullbackAlong ι) :=
      hM_cut.congr ⟨hM'_iso.some.symm⟩
    have hM'_cut : FibrewiseAlgEquivZero M' := by
      intro k _ _ s
      obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (B ⧸ I)),
          s₀ ≫ ι.1 = s := by
        set φk := (Spec.preimage s).hom with hφk'
        have hker : ∀ a ∈ I, φk a = 0 := fun a ha =>
          isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp (hI_nil ha)).map φk)
        refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φk hker)), ?_⟩
        rw [show ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from rfl,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
        exact Spec.map_preimage s
      subst hs₀
      have hψ' : pullback.snd c _ ≫ ι.1 = baseChangeSnd c ι ≫ pullback.snd c _ := by
        simp only [baseChangeSnd, pullback.lift_snd]
      let e : Limits.pullback (pullback.snd c
            (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))) s₀ ⟶
          Limits.pullback (pullback.snd c
            (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (s₀ ≫ ι.1) :=
        pullback.map _ _ _ _ (baseChangeSnd c ι) (𝟙 _) ι.1 hψ' (by simp only [Category.id_comp])
      have he : e ≫ fibreAt c _ (s₀ ≫ ι.1) = fibreAt c _ s₀ := by
        simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
      have hfst : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ baseChangeSnd c ι := by
        simp only [e, pullback.lift_fst]
      have hsnd : e ≫ pullback.snd _ _ = pullback.snd _ _ := by
        simp only [e, pullback.lift_snd, Category.comp_id]
      have hp : IsPullback (baseChangeSnd c ι) (pullback.snd c _) (pullback.snd c _) ι.1 := by
        refine IsPullback.of_right ?_ hψ'.symm (IsPullback.of_hasPullback c _)
        simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
        convert IsPullback.of_hasPullback c
          (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) using 2
      have hpaste : IsPullback (pullback.fst _ _ ≫ baseChangeSnd c ι) (pullback.snd _ s₀)
          (pullback.snd c _) (s₀ ≫ ι.1) :=
        (IsPullback.of_hasPullback _ s₀).paste_horiz hp
      have : IsIso e := by
        have heq : e = hpaste.isoPullback.hom := by
          apply pullback.hom_ext
          · rw [hfst, IsPullback.isoPullback_hom_fst]
          · rw [hsnd, IsPullback.isoPullback_hom_snd]
        exact heq ▸ inferInstance
      refine IsAlgEquivZero.of_iso ?_
        ((hM'ι_cut k s₀).pullback (inv e) (by rw [IsIso.inv_comp_eq, he]))
      refine (Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackComp _ _).app M'.L ≪≫
        (Scheme.Modules.pullbackCongr ?_).app M'.L
      rw [Category.assoc, ← hfst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    set g' := h.classify _ M' hM'_cut with hg'_def
    have hg'_comp : postComp g' ι = g₀ := by
      apply h.ext_of_iso
      refine ⟨?_⟩
      calc (h.poincare.pullbackAlong (postComp g' ι)).L
          ≅ (Scheme.Modules.pullback (baseChangeSnd c (postComp g' ι))).obj h.poincare.L :=
            Iso.refl _
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι ≫ baseChangeSnd c g')).obj h.poincare.L :=
            (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c g' ι).symm).app _
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι)).obj
              ((Scheme.Modules.pullback (baseChangeSnd c g')).obj h.poincare.L) :=
            ((Scheme.Modules.pullbackComp _ _).app _).symm
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι)).obj M'.L :=
            (Scheme.Modules.pullback _).mapIso (h.classify_spec _ M' hM'_cut).some
        _ ≅ M.L := hM'_iso.some
        _ ≅ (h.poincare.pullbackAlong g₀).L := Iso.refl _
    have hg₀_eq : g₀.1 = ι.1 ≫ g'.1 := by
      have := congrArg Subtype.val hg'_comp; simp only [postComp] at this; exact this.symm
    have hv_check : x₀ ≫ D.P.affineCover.f i =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g'.1 := by
      have h1 : (↑g₀ : _ ⟶ D.P) = x₀ ≫ D.P.affineCover.f i := rfl
      have h2 : (↑ι : _ ⟶ _) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := rfl
      rw [← h1, ← h2]; exact hg₀_eq
    obtain ⟨w', hw'⟩ : ∃ w' : Spec (CommRingCat.of B) ⟶ D.P.affineCover.X i,
        w' ≫ D.P.affineCover.f i = g'.1 := by
      have hsurj : Function.Surjective
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base := by
        change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hI_nil).2
      have hrange : Set.range (g'.1 : _ ⟶ D.P).base ⊆
          Set.range (D.P.affineCover.f i).base := by
        rintro y ⟨p, rfl⟩
        obtain ⟨q, rfl⟩ := hsurj p
        refine ⟨x₀.base q, ?_⟩
        have := congrArg (fun f => (Scheme.Hom.toLRSHom f).base q) hv_check
        exact this
      exact ⟨IsOpenImmersion.lift (D.P.affineCover.f i) g'.1 hrange,
        IsOpenImmersion.lift_fac (D.P.affineCover.f i) g'.1 hrange⟩
    have hx₀_eq : x₀ = ι.1 ≫ w' := by
      have : Mono (D.P.affineCover.f i) := inferInstance
      rw [← cancel_mono (D.P.affineCover.f i)]
      simp only [Category.assoc, hw', ← hg₀_eq, hg₀_def]
    have hw'_over : w' ≫ (D.P.affineCover.f i ≫ D.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [← Category.assoc, hw']; exact g'.2
    refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp w'.appTop.hom, fun r => ?_⟩, ?_⟩
    · change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (w'.appTop.hom (φ r)) =
        algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B r
      have happ : w'.appTop.hom (φ r) =
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop.hom r := by
        have := congrArg (fun f => (Scheme.Hom.appTop f).hom r) hw'_over
        rw [hφ]
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
          RingHom.comp_apply] using this
      rw [happ]
      have hnat2 := congrArg (fun g => g.hom r)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R B)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat2
      rw [hnat2]
      change ((algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B).comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = _
      simp only [RingHom.comp_apply]
      congr 1
      exact congrArg (fun g => CommRingCat.Hom.hom g r)
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
    · apply AlgHom.ext; intro a
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_mk,
        RingHom.coe_comp, Function.comp_apply]
      have hx₀_app : x₀.appTop.hom a = (ι.1).appTop.hom (w'.appTop.hom a) := by
        have := congrArg (fun f => (Scheme.Hom.appTop f).hom a) hx₀_eq
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using this
      have hι_nat := congrArg (fun g => g.hom (w'.appTop.hom a))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hι_nat
      rw [show (↑ι : _ ⟶ _) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from rfl]
        at hx₀_app
      rw [← hι_nat, ← hx₀_app]
      simp only [x₀, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have hnat3 := congrArg (fun g => g.hom
          (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ.toRingHom))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat3
      rw [hnat3]
      have htri : (D.P.affineCover.X i).isoSpec.inv.appTop ≫
          (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom = 𝟙 _ := by
        rw [show (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom =
            (D.P.affineCover.X i).isoSpec.hom.appTop from
            ((D.P.affineCover.X i).toSpecΓ_appTop).symm,
          ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      have htria : (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom.hom
          (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a) = a := by
        have := congrArg (fun g => CommRingCat.Hom.hom g a) htri
        exact this
      change ψ.toRingHom ((Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom.hom
        (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a)) = ψ a
      rw [htria]; rfl
end AlgebraicGeometry.RelPicard
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsLocallyInjectiveFunUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t'
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-simp]
  uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
