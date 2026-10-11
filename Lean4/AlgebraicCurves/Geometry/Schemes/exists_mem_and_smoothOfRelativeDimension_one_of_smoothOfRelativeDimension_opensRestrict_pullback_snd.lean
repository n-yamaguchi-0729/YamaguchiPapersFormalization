/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Push
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField

/-!
# exists mem and smooth Of Relative Dimension one of smooth Of Relative Dimension opens
Restrict pullback snd
-/

section ProofImplementation

open _root_.AlgebraicGeometry.Scheme.Hom (
  fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField)

namespace AlgebraicCurves.Geometry.Schemes.Proofs.SmoothRestrictedPullbackDescent
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Hom.resLE_comp_ι HasRingHomProperty.iff_of_isAffine
  SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension
  Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Smooth.exists_isStandardSmooth IsAffine
  isPullback_morphismRestrict Spec Spec.map Scheme Smooth Scheme.stalkClosedPointTo
  arrowResLEAppIso Flat Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
  HasRingHomProperty.appLE smoothOfRelativeDimension_isStableUnderBaseChange
  exists_isAffineOpen_mem_and_subset Scheme.Hom.isoImage_inv_ι HasRingHomProperty.Spec_iff
  Scheme.homOfLE_ι LocallyOfFinitePresentation HasRingHomProperty Scheme.Hom.comp_apply
  Scheme.Hom.smoothLocus_le_preimage_of_isPullback
  Scheme.Hom.fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField)

namespace FibreCritPt

open _root_.AlgebraicGeometry


theorem eq_of_locally_isStandardSmoothOfRelativeDimension {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {n m : ℕ} (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f)
    (hm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) f)
    (Q : Ideal S) [Q.IsPrime] : n = m := by
  classical
  obtain ⟨s, hs, Hn⟩ := hn
  obtain ⟨s', hs', Hm⟩ := hm
  have pick : ∀ (s : Set S), Ideal.span s = ⊤ → ∃ t ∈ s, t ∉ Q := fun s hs => by
    by_contra hall
    push Not at hall
    exact ‹Q.IsPrime›.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hall))
  obtain ⟨t, hts, htQ⟩ := pick s hs
  obtain ⟨t', hts', ht'Q⟩ := pick s' hs'
  let T : Type u := Localization.Away (algebraMap S (Localization.Away t) t')
  let T' : Type u := Localization.Away (algebraMap S (Localization.Away t') t)
  have : IsLocalization.Away (t * t') T := inferInstance
  have : IsLocalization.Away (t * t') T' := inferInstance
  have : Nontrivial T := by
    have htt' : t * t' ∉ Q := fun h => (‹Q.IsPrime›.mem_or_mem h).elim htQ ht'Q
    have hdisj : Disjoint (↑(Submonoid.powers (t * t')) : Set S) ↑Q := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ hn
      exact htt' (‹Q.IsPrime›.mem_of_pow_mem n hn)
    have hP : (Ideal.map (algebraMap S T) Q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (t * t')) _ Q ‹_› hdisj
    exact ⟨⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ Ideal.zero_mem _))⟩⟩
  have hnT : (RingHom.IsStandardSmoothOfRelativeDimension n) ((algebraMap S T).comp f) := by
    have h1 :=
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
      T (algebraMap S (Localization.Away t) t') _ (Hn t hts)
    rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h1
  have hmT : (RingHom.IsStandardSmoothOfRelativeDimension m) ((algebraMap S T).comp f) := by
    have h1 :=
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
      T' (algebraMap S (Localization.Away t') t) _ (Hm t' hts')
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h1
    let e : T' ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers (t * t')) T' T
    have h2 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _ e.toRingEquiv h1
    have he : e.toRingEquiv.toRingHom.comp ((algebraMap S T').comp f) = (algebraMap S T).comp f :=
      by
      rw [← RingHom.comp_assoc]
      congr 1
      ext a
      exact e.commutes a
    rwa [he] at h2
  let := ((algebraMap S T).comp f).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n R T := hnT
  have : Algebra.IsStandardSmoothOfRelativeDimension m R T := hmT
  have h1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := T)
    n
  have h2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := T)
    m
  rw [h1] at h2
  exact_mod_cast h2

theorem SmoothOfRelativeDimension.eq_of_nonempty {X Y : Scheme.{u}} (f : X ⟶ Y) {n m : ℕ}
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) [hX : Nonempty X] : n
      = m := by
  obtain ⟨x⟩ := hX
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show f.base x ∈ (⊤ : Y.Opens) from
    trivial)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ U from hxU)
  have Hn := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have Hm := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ hVU
  exact eq_of_locally_isStandardSmoothOfRelativeDimension _ Hn Hm (hV.primeIdealOf ⟨x, hxV⟩).asIdeal

theorem exists_smoothOpen
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (Ω : (pullback c x).Opens) (hΩ : SmoothOfRelativeDimension 1 (Ω.ι ≫ pullback.snd c x)) :
    ∀ y ∈ (pullback.fst c x).base '' (Ω : Set ↥(pullback c x)),
      ∃ W : C.Opens, y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ c) := by
  rintro _ ⟨y', hy'Ω, rfl⟩
  have := hΩ
  have hy'sm : y' ∈ (pullback.snd c x).smoothLocus := by
    have : Smooth (Ω.ι ≫ pullback.snd c x) := SmoothOfRelativeDimension.smooth 1 _
    have h := (Ω.ι ≫ pullback.snd c x).smoothLocus_eq_top
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
    have : (⟨y', hy'Ω⟩ : Ω) ∈ Ω.ι ⁻¹ᵁ (pullback.snd c x).smoothLocus := by rw [h]; trivial
    exact this
  let s : ↥(Spec (CommRingCat.of R)) := x.base (IsLocalRing.closedPoint k)
  let φ := (Spec (CommRingCat.of R)).descResidueField (Scheme.stalkClosedPointTo x)
  let g : Spec (CommRingCat.of k) ⟶ Spec ((Spec (CommRingCat.of R)).residueField s) := Spec.map φ
  have hfac : g ≫ (Spec (CommRingCat.of R)).fromSpecResidueField s = x :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k _ x
  let g' : pullback c x ⟶ c.fiber s :=
    pullback.lift (pullback.fst c x) (pullback.snd c x ≫ g)
      (by rw [Category.assoc, hfac]; exact pullback.condition)
  have hg'fst : g' ≫ c.fiberι s = pullback.fst c x := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ c.fiberToSpecResidueField s = pullback.snd c x ≫ g := pullback.lift_snd _ _ _
  have hsq : IsPullback g' (pullback.snd c x) (c.fiberToSpecResidueField s) g := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c ((Spec (CommRingCat.of
      R)).fromSpecResidueField s))
    rw [hfac]
    change IsPullback (g' ≫ c.fiberι s) _ _ _
    rw [hg'fst]
    exact IsPullback.of_hasPullback c x
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat ((Spec (CommRingCat.of R)).residueField s) k)
  have : ∀ s', LocallyOfFinitePresentation (c.fiberToSpecResidueField s') := fun s' =>
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))
  have hz : g'.base y' ∈ (c.fiberToSpecResidueField s).smoothLocus :=
    AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback hsq hy'sm
  have hzy : (c.fiberι s).base (g'.base y') = (pullback.fst c x).base y' := by
    rw [← Scheme.Hom.comp_apply, hg'fst]
  have hy : (pullback.fst c x).base y' ∈ c.smoothLocus :=
    hzy ▸
      fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField c s (g'.base y') hz
  have hW₀ : Smooth (c.smoothLocus.ι ≫ c) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact c.smoothLocus.ι_preimage_self
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ := Smooth.exists_isStandardSmooth (c.smoothLocus.ι ≫ c) ⟨_,
    hy⟩
  obtain ⟨d, hd⟩ : ∃ d, ((c.smoothLocus.ι ≫ c).appLE U V e).hom.IsStandardSmoothOfRelativeDimension
    d := by
    let := ((c.smoothLocus.ι ≫ c).appLE U V e).hom.toAlgebra
    have h : Algebra.IsStandardSmooth _ _ := hstd
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have hPd : SmoothOfRelativeDimension d ((c.smoothLocus.ι ≫ c).resLE U V e) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    exact ((RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
      (arrowResLEAppIso _ U V e)).mpr (RingHom.locally_of
        RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hd)
  have hVd : SmoothOfRelativeDimension d (V.ι ≫ c.smoothLocus.ι ≫ c) := by
    have := hPd
    have h2 : SmoothOfRelativeDimension (d + 0) ((c.smoothLocus.ι ≫ c).resLE U V e ≫ U.ι) :=
      inferInstance
    rwa [Scheme.Hom.resLE_comp_ι] at h2
  let W : C.Opens := c.smoothLocus.ι ''ᵁ V
  have hyW : (pullback.fst c x).base y' ∈ W := ⟨⟨_, hy⟩, hyV, rfl⟩
  have hWd : SmoothOfRelativeDimension d (W.ι ≫ c) := by
    rw [← Scheme.Hom.isoImage_inv_ι c.smoothLocus.ι V, Category.assoc]
    have := hVd
    have h := (inferInstance : SmoothOfRelativeDimension (0 + d)
      ((c.smoothLocus.ι.isoImage V).inv ≫ V.ι ≫ c.smoothLocus.ι ≫ c))
    rwa [zero_add] at h
  refine ⟨W, hyW, ?_⟩
  have hsq' := (isPullback_morphismRestrict (pullback.fst c x) W).paste_vert
    (IsPullback.of_hasPullback c x)
  have hWk : SmoothOfRelativeDimension d ((pullback.fst c x ⁻¹ᵁ W).ι ≫ pullback.snd c x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback hsq' hWd
  let O : (pullback c x).Opens := (pullback.fst c x ⁻¹ᵁ W) ⊓ Ω
  have hO1 : SmoothOfRelativeDimension 1 (O.ι ≫ pullback.snd c x) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : O ≤ Ω), Category.assoc]
    have h := (inferInstance : SmoothOfRelativeDimension (0 + 1)
      ((pullback c x).homOfLE (inf_le_right : O ≤ Ω) ≫ Ω.ι ≫ pullback.snd c x))
    rwa [zero_add] at h
  have hOd : SmoothOfRelativeDimension d (O.ι ≫ pullback.snd c x) := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : O ≤ pullback.fst c x ⁻¹ᵁ W), Category.assoc]
    have := hWk
    have h := (inferInstance : SmoothOfRelativeDimension (0 + d)
      ((pullback c x).homOfLE (inf_le_left : O ≤ pullback.fst c x ⁻¹ᵁ W) ≫ (pullback.fst c x ⁻¹ᵁ
        W).ι ≫ pullback.snd c x))
    rwa [zero_add] at h
  have : Nonempty O := ⟨⟨y', show (pullback.fst c x).base y' ∈ W from hyW, hy'Ω⟩⟩
  obtain rfl : d = 1 := SmoothOfRelativeDimension.eq_of_nonempty _ hOd hO1
  exact hWd

end AlgebraicGeometry.FibreCritPt
end AlgebraicCurves.Geometry.Schemes.Proofs.SmoothRestrictedPullbackDescent

namespace AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.SmoothRestrictedPullbackDescent
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry


theorem
exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (Ω : (pullback c x).Opens) (hΩ : SmoothOfRelativeDimension 1 (Ω.ι ≫ pullback.snd c x)) :
    ∀ y ∈ (pullback.fst c x).base '' (Ω : Set ↥(pullback c x)),
      ∃ W : C.Opens, y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ c) := by
  exact AlgebraicGeometry.FibreCritPt.exists_smoothOpen
    c x Ω hΩ
end AlgebraicGeometry
end ProofImplementation
