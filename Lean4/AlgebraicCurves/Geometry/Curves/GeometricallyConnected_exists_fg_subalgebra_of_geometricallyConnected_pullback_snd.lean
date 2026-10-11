/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Spectrum.Prime.Defs
import AlgebraicCurves.Geometry.Curves.GeometricallyConnected_descendsAlong_surjective
import AlgebraicCurves.Valuations.IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected
import AlgebraicCurves.Geometry.Curves.geometricallyConnected_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_pullback_snd

/-!
# Descending geometric connectedness to a finitely generated base algebra
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
attribute [-instance] ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
attribute [-simp] AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace GeomConnDesc

lemma iff_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {X X₁ Y B : Scheme.{u}}
    {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) :
    P (pullback.snd f ι) ↔ P g := by
  rw [← sq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

lemma exists_isPullback_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι
  : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι) :
    ∃ π' : X ⟶ pullback f κ, IsPullback π' g (pullback.snd f κ) ι' := by
  have w : π ≫ f = (g ≫ ι') ≫ κ := by rw [Category.assoc, hι]; exact sq.w
  refine ⟨pullback.lift π (g ≫ ι') w, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd
    _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

lemma exists_isPullback_comp {A₀ B C : Type u} [CommRing A₀] [CommRing B] [CommRing C]
    (β : A₀ →+* B) (δ : B →+* C) {γ : A₀ →+* C} (hγ : δ.comp β = γ)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    ∃ π : pullback f (Spec.map (CommRingCat.ofHom γ)) ⟶ pullback f (Spec.map (CommRingCat.ofHom β)),
      IsPullback π (pullback.snd f (Spec.map (CommRingCat.ofHom γ))) (pullback.snd f (Spec.map
        (CommRingCat.ofHom β)))
        (Spec.map (CommRingCat.ofHom δ)) :=
  exists_isPullback_of_fac (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom γ))) _ _
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hγ])

lemma surjective_specMap_of_field {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun x => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ x⟩⟩

scoped instance descendsAlong : MorphismProperty.DescendsAlong (@GeometricallyConnected :
  MorphismProperty Scheme.{u})
    @Surjective := AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective

theorem of_ring {A₀ T : Type u} [CommRing A₀] [CommRing T] (τ : A₀ →+* T)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsProper f] [Smooth f]
    (R L : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field L]
    (φ : T →+* R) (ψ : R →+* L) (hψ : Function.Injective ψ)
    (hL : GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom ((ψ.comp φ).comp
      τ)))))
    (c : ↥(Spec (CommRingCat.of R))) (t : ↥(Spec (CommRingCat.of T)))
    (hct : (Spec.map (CommRingCat.ofHom φ)) c = t) :
    GeometricallyConnected ((pullback.snd f (Spec.map (CommRingCat.ofHom
      τ))).fiberToSpecResidueField t) := by
  classical
  let fT := pullback.snd f (Spec.map (CommRingCat.ofHom τ))
  let fR := pullback.snd f (Spec.map (CommRingCat.ofHom (φ.comp τ)))
  let K := FractionRing R
  let ψK : K →+* L := IsFractionRing.lift hψ
  have hψK : ψK.comp (algebraMap R K) = ψ := RingHom.ext fun x => IsFractionRing.lift_algebraMap hψ
    x
  let fK := pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap R K).comp (φ.comp τ))))
  have hfacL : (ψK.comp ((algebraMap R K).comp (φ.comp τ))) = (ψ.comp φ).comp τ := by
    rw [← RingHom.comp_assoc, hψK, RingHom.comp_assoc]
  obtain ⟨πL, sqL⟩ := exists_isPullback_comp ((algebraMap R K).comp (φ.comp τ)) ψK hfacL f
  have : GeometricallyConnected fK :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected) (Q :=
      @Surjective)
      sqL.flip (surjective_specMap_of_field ψK) hL
  have : Smooth fK := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@Smooth : MorphismProperty Scheme.{u}) := smooth_isStableUnderBaseChange
    exact MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback f
        (Spec.map (CommRingCat.ofHom ((algebraMap R K).comp (φ.comp τ))))) ‹Smooth f›
  have : GeometricallyIntegral fK :=
    AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected fK
  obtain ⟨πK, sqK⟩ := exists_isPullback_comp (φ.comp τ) (algebraMap R K) rfl f
  have : GeometricallyReduced (pullback.snd fR (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    by
    have : MorphismProperty.RespectsIso
        (@GeometricallyReduced : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (iff_of_isPullback (P := @GeometricallyReduced) sqK).mpr inferInstance
  have : GeometricallyConnected (pullback.snd fR (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    := by
    have : MorphismProperty.RespectsIso
        (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (iff_of_isPullback (P := @GeometricallyConnected) sqK).mpr inferInstance
  have : IsProper fR := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@IsProper : MorphismProperty Scheme.{u}) := IsProper.isStableUnderBaseChange
    exact MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (φ.comp τ)))) ‹IsProper f›
  have : Flat fR := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@Flat : MorphismProperty Scheme.{u}) := Flat.isStableUnderBaseChange
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (φ.comp τ))))
      (show Flat f from inferInstance)
  have hR : GeometricallyConnected fR :=
    AlgebraicGeometry.geometricallyConnected_of_geometricallyConnected_pullback_snd
      K fR
  have hRc : GeometricallyConnected (fR.fiberToSpecResidueField c) := inferInstance
  obtain ⟨πR, sqR⟩ := exists_isPullback_comp τ φ rfl f
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sqR c
  have key := MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected) (Q :=
    @Surjective)
    sqF.flip (surjective_specMap_of_field _) hRc
  rw [hct] at key
  exact key

theorem exists_ring {T A : Type u} [CommRing T] [CommRing A] [IsNoetherianRing T]
    (ι : T →+* A) (hι : Function.Injective ι) (t : ↥(Spec (CommRingCat.of T))) :
    ∃ (R L : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (_ :
      IsIntegrallyClosed R)
      (_ : Field L) (φ : T →+* R) (ψ : R →+* L) (α : A →+* L),
      Function.Injective ψ ∧ ψ.comp φ = α.comp ι ∧
      ∃ c : ↥(Spec (CommRingCat.of R)), (Spec.map (CommRingCat.ofHom φ)) c = t := by
  classical
  have : t.asIdeal.IsPrime := (show PrimeSpectrum T from t).isPrime
  obtain ⟨η, hη, hηt⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal T)) (J := t.asIdeal) bot_le
  obtain ⟨𝔮, h𝔮, h𝔮η⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hι η hη
  have := h𝔮
  have : η.IsPrime := hη.1.1
  let L := FractionRing (A ⧸ 𝔮)
  let α : A →+* L := (algebraMap (A ⧸ 𝔮) L).comp (Ideal.Quotient.mk 𝔮)
  have hαker : Ideal.comap (α.comp ι) ⊥ = η := by
    rw [← Ideal.comap_comap, ← Ideal.comap_comap, Ideal.comap_bot_of_injective _
      (IsFractionRing.injective (A ⧸ 𝔮) L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, h𝔮η]
  by_cases ht : t.asIdeal = η
  · let c : PrimeSpectrum L := default
    have hc : c.asIdeal = ⊥ := by
      calc
        c.asIdeal = (⊥ : PrimeSpectrum L).asIdeal :=
          congrArg (fun p : PrimeSpectrum L => p.asIdeal) (Subsingleton.elim c ⊥)
        _ = ⊥ := PrimeSpectrum.asIdeal_bot
    refine ⟨L, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, α.comp
      ι, RingHom.id L, α,
      fun a b h => h, RingHom.id_comp _, c, ?_⟩
    change PrimeSpectrum.comap (α.comp ι) c = (show PrimeSpectrum T from t)
    apply PrimeSpectrum.ext
    change Ideal.comap (α.comp ι) c.asIdeal = t.asIdeal
    rw [hc]
    exact hαker.trans ht.symm
  · let D := T ⧸ η
    let P : Ideal D := t.asIdeal.map (Ideal.Quotient.mk η)
    have hP : P.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hηt)
    have hPcomap : P.comap (Ideal.Quotient.mk η) = t.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker,
        sup_eq_left.mpr hηt]
    have hPne : P ≠ ⊥ := by
      intro h
      apply ht
      rw [← hPcomap, h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    let B := Localization.AtPrime P
    let K₀ := FractionRing D
    have hBfield : ¬ IsField B := by
      intro hF
      apply hPne
      rw [← Localization.AtPrime.under_maximalIdeal (I := P), Ideal.under_def,
        IsLocalRing.isField_iff_maximalIdeal_eq.mp hF,
        Ideal.comap_bot_of_injective _ (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)]
    obtain ⟨V, hV, hBV, hdom⟩ :=
      IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates (R := B) hBfield K₀
    have := hV
    let φ₀ : T →+* K₀ := (algebraMap B K₀).comp ((algebraMap D B).comp (Ideal.Quotient.mk η))
    let φ : T →+* ↥V := φ₀.codRestrict V.toSubring (fun x => hBV _)
    let δ : D →+* A ⧸ 𝔮 := Ideal.quotientMap 𝔮 ι (le_of_eq h𝔮η.symm)
    have hδ : Function.Injective δ := Ideal.quotientMap_injective' (le_of_eq h𝔮η)
    let κL : K₀ →+* L :=
      IsFractionRing.lift (g := (algebraMap (A ⧸ 𝔮) L).comp δ) ((IsFractionRing.injective (A ⧸ 𝔮)
        L).comp hδ)
    let ψ : ↥V →+* L := κL.comp V.subtype
    let c : PrimeSpectrum ↥V := IsLocalRing.closedPoint ↥V
    refine ⟨↥V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, φ, ψ,
      α, ?_, ?_,
      c, ?_⟩
    · exact κL.injective.comp Subtype.val_injective
    · ext x
      change κL (algebraMap B K₀ (algebraMap D B (Ideal.Quotient.mk η x))) = α (ι x)
      rw [← IsScalarTower.algebraMap_apply D B K₀, IsFractionRing.lift_algebraMap]
      change algebraMap (A ⧸ 𝔮) L (δ (Ideal.Quotient.mk η x)) = algebraMap (A ⧸ 𝔮) L
        (Ideal.Quotient.mk 𝔮 (ι x))
      rw [Ideal.quotientMap_mk]
    · change PrimeSpectrum.comap φ c = (show PrimeSpectrum T from t)
      apply PrimeSpectrum.ext
      change Ideal.comap φ (IsLocalRing.maximalIdeal ↥V) = t.asIdeal
      rw [← hPcomap]
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      change algebraMap B K₀ (algebraMap D B (Ideal.Quotient.mk η x)) ∈ V.nonunits ↔ _
      rw [← hdom, IsLocalization.AtPrime.to_map_mem_maximal_iff B P]

end GeomConnDesc

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd in
attribute [local instance]
  GeomConnDesc.descendsAlong


end GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry.GeometricallyConnected

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd in
attribute [local instance] GeomConnDesc.descendsAlong

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd in
open GeomConnDesc in
theorem exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsProper f] [Smooth f]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) :=
        by
  classical
  let T : Subalgebra A₀ A := Algebra.adjoin A₀ ↑s
  refine ⟨T, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin, ?_⟩
  have : Algebra.FiniteType A₀ ↥T := (Subalgebra.fg_iff_finiteType _).mp
    (Subalgebra.fg_adjoin_finset s)
  have : IsNoetherianRing ↥T := Algebra.FiniteType.isNoetherianRing A₀ ↥T
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro t
  obtain ⟨R, L, _, _, _, _, _, φ, ψ, α, hψ, hcomp, c, hct⟩ :=
    exists_ring (algebraMap ↥T A) Subtype.val_injective t
  have hfac : (ψ.comp φ).comp (algebraMap A₀ ↥T) = α.comp (algebraMap A₀ A) := by
    rw [hcomp, RingHom.comp_assoc]; rfl
  obtain ⟨πA, sqA⟩ := exists_isPullback_comp (algebraMap A₀ A) α hfac.symm f
  have hL : GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom ((ψ.comp φ).comp
    (algebraMap A₀ ↥T))))) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqA inferInstance
  exact of_ring (algebraMap A₀ ↥T) f R L φ ψ hψ hL c t hct

end AlgebraicGeometry.GeometricallyConnected
end ProofImplementation
