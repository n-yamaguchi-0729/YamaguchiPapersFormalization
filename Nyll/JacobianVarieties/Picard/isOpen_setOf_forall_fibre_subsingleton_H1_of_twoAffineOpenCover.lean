/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover.lean
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
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.Subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart

/-!
# Openness of fibrewise cohomology vanishing

Fibrewise vanishing of first cohomology defines an open locus.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.H1VanishingLocus
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
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
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ

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
  IsProper
  Scheme.Modules.pullback
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Modules
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
  Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom
  Scheme.TwoAffineOpenCover.finiteType_algebraOfHom
  Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
  RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  fibreAt
  fibreModule
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
  subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart)

namespace OpenLocusSol'

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField) = 𝔭 := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap (algebraMap A 𝔭.asIdeal.ResidueField)
    (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField)).asIdeal = 𝔭.asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  have hbot : (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField).asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal _ = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem toK4
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T)
    {CA : Scheme.{u}} (g' : CA ⟶ pullback c t) (πA : CA ⟶ Spec (CommRingCat.of A))
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = j.base 𝔭 →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :
    Subsingleton ((𝒱.pullback πA 𝔭.asIdeal.ResidueField).sectionsOf
        (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A
          𝔭.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback g').obj M))).H1 := by
  let κ : Type u := 𝔭.asIdeal.ResidueField
  let s₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) :=
    Scheme.TwoAffineOpenCover.specMap A κ
  have hsq : IsPullback (pullback.fst πA s₀ ≫ g') (pullback.snd πA s₀) (pullback.snd c t) (s₀ ≫ j)
    :=
    (IsPullback.of_hasPullback πA s₀).paste_horiz hcart
  obtain ⟨𝒲, -, ⟨e1⟩⟩ :=
    RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M (s₀ ≫ j)
    (pullback.snd πA s₀) (pullback.fst πA s₀ ≫ g') hsq
    ((Scheme.Modules.pullback (pullback.fst πA s₀)).obj ((Scheme.Modules.pullback g').obj M))
    ((Scheme.Modules.pullbackComp (pullback.fst πA s₀) g').app M) (𝒱.pullback πA κ)
  have hs : (s₀ ≫ j).base (IsLocalRing.closedPoint κ) = j.base 𝔭 := by
    change j.base (s₀.base (IsLocalRing.closedPoint κ)) = j.base 𝔭
    rw [specMap_residueField_base]
  have := hU κ (s₀ ≫ j) hs 𝒲
  exact e1.toEquiv.subsingleton

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ (⊤ : T.Opens) from trivial)
  let : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
  have : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  have : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t
    W hW
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  let 𝒱A := 𝒱.pullback c Γ(T, W)
  have hO := Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝒱A
    ((Scheme.Modules.pullback g').obj M) (hM.pullback g')
  refine ⟨hW.fromSpec.base '' {𝔭 : PrimeSpectrum Γ(T, W) | Subsingleton
      ((𝒱A.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
        𝔭.asIdeal.ResidueField).sectionsOf
        (pullback.snd (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
          (Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c (Scheme.TwoAffineOpenCover.specMap
          R Γ(T, W)))
          (Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback g').obj M))).H1}, ?_, ?_, ?_⟩
  · rintro y ⟨𝔭, h𝔭, rfl⟩
    intro k _ s hs 𝒲
    exact RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart c t M hM
      hW.fromSpec _ g' hcart 𝒱A 𝔭 h𝔭 s hs 𝒲
  · exact hW.fromSpec.isOpenEmbedding.isOpenMap _ hO
  · have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    exact ⟨𝔭, toK4 c t M hW.fromSpec g' _ hcart 𝒱A 𝔭 hx, rfl⟩

end AlgebraicGeometry.RelPicard.OpenLocusSol'
end
end JacobianVarieties.Picard.Proofs.H1VanishingLocus

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.H1VanishingLocus.AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.H1VanishingLocus
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

/-- Fibrewise vanishing of first cohomology defines an open locus. -/
theorem isOpen_setOf_forall_fibre_subsingleton_H1_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} :=
  OpenLocusSol'.main R c 𝒱 t M hM
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
