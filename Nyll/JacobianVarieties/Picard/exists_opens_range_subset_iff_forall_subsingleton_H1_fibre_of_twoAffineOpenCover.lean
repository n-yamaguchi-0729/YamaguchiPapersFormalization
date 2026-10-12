/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Picard.Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Nyll.JacobianVarieties.Picard.Subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
import Nyll.JacobianVarieties.Picard.Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import Nyll.JacobianVarieties.Picard.isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover

/-! The open locus where first fibre cohomology vanishes. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.H1VanishingOpen
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

noncomputable section
namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Spec.map_preimage
  IsOpenImmersion.lift
  IsProper
  Scheme.Modules.pullback
  LocallyOfFiniteType
  Spec
  Spec.map
  Scheme
  IsOpenImmersion
  IsSeparated
  Spec.preimage
  Scheme.Modules
  IsOpenImmersion.lift_fac
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  fibreAt
  fibreModule
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
  subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
  exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
  isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover)

namespace OpenLocusIffSol'

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

theorem chart_of_point
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules) (hM :
      Scheme.Modules.IsInvertible M)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭)
    (hvan : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :
    Subsingleton ((𝒱.pullback πA 𝔭.asIdeal.ResidueField).sectionsOf
        (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A
          𝔭.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback g').obj M))).H1 := by
  classical
  set K₀ : Type u := 𝔭.asIdeal.ResidueField with hK₀
  set s₁ : Spec (CommRingCat.of K₀) ⟶ T := Scheme.TwoAffineOpenCover.specMap A K₀ ≫ j with hs₁def
  have hcart₁ : IsPullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g')
      (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀)) (pullback.snd c t) s₁ :=
    (IsPullback.of_hasPullback πA (Scheme.TwoAffineOpenCover.specMap A K₀)).paste_horiz hcart
  obtain ⟨𝒲₁, -, ⟨l₁⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t
    M s₁
    (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀))
    (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g') hcart₁
    ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀))).obj
      ((Scheme.Modules.pullback g').obj M))
    ((Scheme.Modules.pullbackComp (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀))
      g').app M)
    (𝒱.pullback πA K₀)
  obtain ⟨s', hs'⟩ : ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A), s' ≫ j = s := by
    refine ⟨IsOpenImmersion.lift j s ?_, IsOpenImmersion.lift_fac j s _⟩
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k), hs]
    exact ⟨𝔭, rfl⟩
  subst hs'
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of A ⟶ CommRingCat.of k, Spec.map φ = s' := ⟨Spec.preimage
    s', Spec.map_preimage s'⟩
  have hpt : (Spec.map φ).base (IsLocalRing.closedPoint k) = 𝔭 := by
    apply j.isOpenEmbedding.injective
    exact hs
  have hker : RingHom.ker φ.hom = 𝔭.asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal hpt
    have hmax : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    have h2 : ((Spec.map φ).base (IsLocalRing.closedPoint k)).asIdeal =
        Ideal.comap φ.hom (IsLocalRing.closedPoint k).asIdeal := rfl
    rw [h2, hmax] at h1
    exact h1
  have hφ𝔭 : ∀ a ∈ 𝔭.asIdeal, φ.hom a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha
  set φbar : A ⧸ 𝔭.asIdeal →+* k := Ideal.Quotient.lift 𝔭.asIdeal φ.hom hφ𝔭 with hφbar
  have hinj : Function.Injective φbar := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hφbar, Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker ▸ (RingHom.mem_ker.mpr ha))
  set ψ : K₀ →+* k := IsFractionRing.lift (A := A ⧸ 𝔭.asIdeal) (K := K₀) (g := φbar) hinj with hψ
  let : Algebra K₀ k := ψ.toAlgebra
  have hφfac : φ = CommRingCat.ofHom ((algebraMap K₀ k).comp (algebraMap A K₀)) := by
    ext a
    change φ.hom a = ψ ((algebraMap A K₀) a)
    rw [hψ, IsScalarTower.algebraMap_apply A (A ⧸ 𝔭.asIdeal) K₀, IsFractionRing.lift_algebraMap,
      hφbar, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk]
  have h : Spec.map φ ≫ j = Scheme.TwoAffineOpenCover.specMap K₀ k ≫ s₁ := by
    rw [hs₁def, ← Category.assoc, hφfac, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨𝒲', -, hiff⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t
    M hM s₁ 𝒲₁ k
  have hvan' : ∀ 𝒲 : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap K₀ k ≫
    s₁)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap K₀ k ≫ s₁))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap K₀ k ≫ s₁) M)).H1 := by
    rw [← h]; exact hvan
  have h₁ : Subsingleton (𝒲₁.sectionsOf (fibreAt c t s₁) (fibreModule c t s₁ M)).H1 := hiff.mp
    (hvan' 𝒲')
  exact l₁.toEquiv.subsingleton

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ U : T.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ (U : Set T) ↔
        ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by
  classical
  refine ⟨⟨{x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1},
    isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover R c 𝒱 t M hM⟩, fun k _ s =>
      ⟨fun hsub 𝒲 => ?_, fun hvan => ?_⟩⟩
  · exact hsub ⟨IsLocalRing.closedPoint k, rfl⟩ k s rfl 𝒲
  · rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    intro k' _ s' hs' 𝒲'
    set x := s.base (IsLocalRing.closedPoint k) with hx
    obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x ∈ (⊤ : T.Opens) from trivial)
    let : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
    obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c
      t W hW
    have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
    let 𝒱A := 𝒱.pullback c Γ(T, W)
    have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, h𝔭⟩ := hxr
    have hO := chart_of_point c t M hM hW.fromSpec _ g' hcart 𝒱A 𝔭 s h𝔭.symm hvan
    exact subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart c t M hM hW.fromSpec _ g'
      hcart
      𝒱A 𝔭 hO s' (hs'.trans h𝔭.symm) 𝒲'

end AlgebraicGeometry.RelPicard.OpenLocusIffSol'
end
end JacobianVarieties.Picard.Proofs.H1VanishingOpen

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs
open _root_.JacobianVarieties.Picard.Proofs.H1VanishingOpen
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

/-- The open locus where first fibre cohomology vanishes. -/
theorem exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ U : T.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ (U : Set T) ↔
        ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 :=
  H1VanishingOpen.AlgebraicGeometry.RelPicard.OpenLocusIffSol'.main R c 𝒱 t M hM
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
