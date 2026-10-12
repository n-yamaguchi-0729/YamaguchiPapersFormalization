/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverPreimage
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.JacobianVarieties.Picard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
import Nyll.JacobianVarieties.Picard.pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Nyll.AlgebraicCurves.Geometry.Picard.Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul

/-!
# The open locus of supported zero schemes

Fibre cohomology of dimension one provides local generating sections. Their zero-scheme
support conditions glue to an open locus in the parameter scheme.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ZeroSupportOpen
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
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
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
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  IsOpenImmersion.lift
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.Hom.zero_app
  Scheme.Modules.pushforward
  IsProper
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.preimage_inf
  Scheme.Modules.Hom
  UniversallyClosed
  Scheme.Pullback.range_fst
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Hom.comp_base
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackPushforwardAdjunction
  Scheme.Modules.pullbackId
  Scheme.Hom.preimage_sup
  Scheme.Modules
  Scheme.Opens
  IsAffineHom
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  range_eq_univ
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.algebraOfHom
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.Modules.toUnitSection
  Scheme.Modules.ofUnitSection
  Scheme.Modules.ofUnitSection_toUnitSection
  Scheme.Modules.ofUnitSection_injective
  Scheme.Modules.ofUnitSection_map
  Scheme.Modules.ofUnitSection_smul
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
  Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  fibreAt
  fibreModule
  isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
  pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback)

namespace FinTransport

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

/-- The support of a pulled-back zero scheme is the inverse image of its support. -/
theorem coe_support_zeroSchemeIdeal_pullbackSection {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F, Scheme.IdealSheafData.support_comap]
  rfl

/-- An isomorphism of schemes induces an equivalence of module categories. -/
noncomputable def pullbackEquivOfIso {X X' : Scheme.{u}} (e : X' ≅ X) : X.Modules ≌ X'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId X')

scoped instance full_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Full :=
  (pullbackEquivOfIso (asIso F)).full_functor

scoped instance faithful_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Faithful :=
  (pullbackEquivOfIso (asIso F)).faithful_functor

/-- Pullback along an isomorphism preserves nonzero sections. -/
theorem pullbackSection_ne_zero_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M : X.Modules}
    {s : 𝟙_ X.Modules ⟶ M} (hs : s ≠ 0) : Scheme.Modules.pullbackSection F s ≠ 0 := by
  intro h
  rw [Scheme.Modules.pullbackSection_def] at h
  have h1 : (Scheme.Modules.pullback F).map s = 0 := by
    have h' := congrArg (fun f => (Scheme.Modules.pullbackUnitIso F).hom ≫ f) h
    exact ((Scheme.Modules.pullbackUnitIso F).hom_inv_id_assoc
      ((Scheme.Modules.pullback F).map s)).symm.trans (h'.trans (Limits.comp_zero))
  exact hs ((Scheme.Modules.pullback F).map_injective
    (h1.trans ((Scheme.Modules.pullback F).map_zero _ _).symm))

/-- Every section over an isomorphic scheme descends uniquely to a section. -/
theorem exists_pullbackSection_eq_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F]
    {M : X.Modules}
    (τ : 𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M) :
    ∃ s : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection F s = τ := by
  refine ⟨(Scheme.Modules.pullback F).preimage ((Scheme.Modules.pullbackUnitIso F).hom ≫ τ), ?_⟩
  rw [Scheme.Modules.pullbackSection_def]
  erw [Functor.map_preimage]
  exact (Scheme.Modules.pullbackUnitIso F).inv_hom_id_assoc τ

/-- Support containment of nonzero sections is invariant under scheme and module isomorphisms. -/
theorem forall_support_subset_iff_of_isIso {Y Y' : Scheme.{u}} (F : Y' ⟶ Y) [IsIso F]
    {P : Y.Modules}
    (hP : Scheme.Modules.IsInvertible P) {P' : Y'.Modules} (j : P' ≅ (Scheme.Modules.pullback
      F).obj P)
    (V : Set Y) :
    (∀ σ' : 𝟙_ Y'.Modules ⟶ P', σ' ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ').support : Set Y') ⊆ F.base ⁻¹' V) ↔
      (∀ σ : 𝟙_ Y.Modules ⟶ P, σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set Y) ⊆ V)
        := by
  constructor
  · intro h σ hσ
    have hσ' : Scheme.Modules.pullbackSection F σ ≫ j.inv ≠ 0 := fun h0 =>
      pullbackSection_ne_zero_of_isIso F hσ ((Preadditive.IsIso.comp_right_eq_zero _ _).mp h0)
    have := h _ hσ'
    rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      coe_support_zeroSchemeIdeal_pullbackSection F hP] at this
    exact F.homeomorph.surjective.preimage_subset_preimage_iff.mp this
  · intro h σ' hσ'
    obtain ⟨σ, hσ⟩ := exists_pullbackSection_eq_of_isIso F (σ' ≫ j.hom)
    have hσ0 : σ ≠ 0 := by
      intro hz
      apply hσ'
      have h1 : σ' ≫ j.hom = 0 := by
        rw [← hσ, Scheme.Modules.pullbackSection_def, hz]
        exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·)
          ((Scheme.Modules.pullback F).map_zero _ _)).trans comp_zero
      exact (Preadditive.IsIso.comp_right_eq_zero _ _).mp h1
    have := h σ hσ0
    rw [← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso σ' j.hom, ← hσ,
      coe_support_zeroSchemeIdeal_pullbackSection F hP]
    exact Set.preimage_mono this

/-- All nonzero sections on the fibre have zero schemes supported in the chosen open. -/
abbrev FinerAt {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  ∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M,
    σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆
      ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))

/-- Transport the fibre support condition through base change and a module comparison. -/
theorem finerAt_transport {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec
      (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : (pullback c t').Modules) (i : M' ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M)
    {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ T') :
    FinerAt c U t' M' x' ↔ FinerAt c U t M (x' ≫ ψ.1) := by
  obtain ⟨ψ1, hψ⟩ := ψ
  subst hψ
  let e : pullback c (x' ≫ ψ1 ≫ t) ≅ pullback c ((x' ≫ ψ1) ≫ t) :=
    pullback.congrHom rfl (Category.assoc _ _ _).symm
  have he_fst : e.hom ≫ pullback.fst c ((x' ≫ ψ1) ≫ t) = pullback.fst c (x' ≫ ψ1 ≫ t) := by
    rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have hE : mapOnProdOver c x' rfl ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      e.hom ≫ mapOnProdOver c (x' ≫ ψ1) rfl := by
    apply pullback.hom_ext
    · simp only [e, Category.assoc, mapOnProdOver_fst, pullback.congrHom_hom, baseChangeSnd,
        pullback.lift_fst,
        Category.comp_id]
    · simp only [e, Category.assoc, mapOnProdOver_snd, pullback.congrHom_hom, baseChangeSnd,
        pullback.lift_snd,
        Category.comp_id, mapOnProdOver_snd_assoc, pullback.lift_snd_assoc]
  have hP : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj M) :=
    hM.pullback _
  let j : (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj M' ≅
      (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1)
        rfl)).obj M) :=
    (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).mapIso i ≪≫
      (Scheme.Modules.pullbackComp (mapOnProdOver c x' rfl) (baseChangeSnd c ⟨ψ1, rfl⟩)).app M ≪≫
      (Scheme.Modules.pullbackCongr hE).app M ≪≫
      ((Scheme.Modules.pullbackComp e.hom (mapOnProdOver c (x' ≫ ψ1) rfl)).app M).symm
  have hV : e.hom.base ⁻¹' ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫
    t))) =
      ((pullback.fst c (x' ≫ ψ1 ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x' ≫ ψ1 ≫ t))) := by
    rw [← he_fst]
    rfl
  have key := forall_support_subset_iff_of_isIso e.hom hP j
    ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t)))
  rw [hV] at key
  exact key

end AlgebraicGeometry.RelPicard.FinTransport

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  IsOpenImmersion.lift
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.Hom.zero_app
  Scheme.Modules.pushforward
  IsProper
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.preimage_inf
  Scheme.Modules.Hom
  UniversallyClosed
  Scheme.Pullback.range_fst
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Hom.comp_base
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackPushforwardAdjunction
  Scheme.Modules.pullbackId
  Scheme.Hom.preimage_sup
  Scheme.Modules
  Scheme.Opens
  IsAffineHom
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  range_eq_univ
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.algebraOfHom
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.Modules.toUnitSection
  Scheme.Modules.ofUnitSection
  Scheme.Modules.ofUnitSection_toUnitSection
  Scheme.Modules.ofUnitSection_injective
  Scheme.Modules.ofUnitSection_map
  Scheme.Modules.ofUnitSection_smul
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
  Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  fibreAt
  fibreModule
  isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
  pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback)

namespace E6B

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.JacobianVarieties.Picard.Proofs.ZeroSupportOpen.AlgebraicGeometry

/-- The induced product map has range equal to the inverse image of the parameter range. -/
theorem range_mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    Set.range ⇑(mapOnProdOver f φ hφ) = ⇑(pullback.snd f g') ⁻¹' Set.range ⇑φ := by
  have H := isPullback_mapOnProdOver f φ hφ
  rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (show Function.Surjective ⇑H.isoPullback.hom from
      H.isoPullback.hom.homeomorph.surjective),
    Set.image_univ, Scheme.Pullback.range_fst]

/-- Universal closedness gives an open parameter locus for a fibrewise support condition. -/
theorem exists_opens_range_subset_iff_preimage_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [UniversallyClosed
      c] (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Z : Set ↥(pullback c t)) (hZ : IsClosed Z) :
    ∃ U' : T.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ (U' : Set T) ↔
        ⇑(mapOnProdOver c s rfl) ⁻¹' Z ⊆ ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫
          t))) := by
  have hq : IsClosedMap ⇑(pullback.snd c t) := (pullback.snd c t).isClosedMap
  set B : Set ↥(pullback c t) := Z ∩ ((pullback.fst c t) ⁻¹ᵁ U : Set ↥(pullback c t))ᶜ with hB
  have hBc : IsClosed B := hZ.inter ((pullback.fst c t) ⁻¹ᵁ U).isOpen.isClosed_compl
  refine ⟨⟨(⇑(pullback.snd c t) '' B)ᶜ, (hq B hBc).isOpen_compl⟩, fun k _ s => ?_⟩
  have hfst : ∀ p : ↥(pullback c (s ≫ t)),
      p ∈ ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t))) ↔
        mapOnProdOver c s rfl p ∈ ((pullback.fst c t) ⁻¹ᵁ U : Set ↥(pullback c t)) := by
    intro p
    change (pullback.fst c (s ≫ t)) p ∈ (U : Set C) ↔ (pullback.fst c t) (mapOnProdOver c s rfl p)
      ∈ (U : Set C)
    rw [← Scheme.Hom.comp_apply, mapOnProdOver_fst]
  constructor
  · intro hs p hp
    by_contra hU
    have hmem : (pullback.snd c t) (mapOnProdOver c s rfl p) ∈ ⇑(pullback.snd c t) '' B :=
      ⟨mapOnProdOver c s rfl p, ⟨hp, fun h => hU ((hfst p).2 h)⟩, rfl⟩
    have hrange : (pullback.snd c t) (mapOnProdOver c s rfl p) ∈ Set.range ⇑s := by
      rw [← Scheme.Hom.comp_apply, mapOnProdOver_snd]
      exact ⟨_, rfl⟩
    exact hs hrange hmem
  · intro h
    rintro _ ⟨z, rfl⟩ ⟨p', ⟨hp'Z, hp'U⟩, hq'⟩
    obtain ⟨p, rfl⟩ : p' ∈ Set.range ⇑(mapOnProdOver c s rfl) := by
      rw [range_mapOnProdOver]; exact ⟨z, hq'.symm⟩
    exact hp'U ((hfst p).1 (h hp'Z))

end AlgebraicGeometry.RelPicard.E6B

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  IsOpenImmersion.lift
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.Hom.zero_app
  Scheme.Modules.pushforward
  IsProper
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.preimage_inf
  Scheme.Modules.Hom
  UniversallyClosed
  Scheme.Pullback.range_fst
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Hom.comp_base
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackPushforwardAdjunction
  Scheme.Modules.pullbackId
  Scheme.Hom.preimage_sup
  Scheme.Modules
  Scheme.Opens
  IsAffineHom
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  range_eq_univ
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.algebraOfHom
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.Modules.toUnitSection
  Scheme.Modules.ofUnitSection
  Scheme.Modules.ofUnitSection_toUnitSection
  Scheme.Modules.ofUnitSection_injective
  Scheme.Modules.ofUnitSection_map
  Scheme.Modules.ofUnitSection_smul
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
  Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  fibreAt
  fibreModule
  isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
  pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback)

namespace H0LINK

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.JacobianVarieties.Picard.Proofs.ZeroSupportOpen.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.JacobianVarieties.Picard.Proofs.ZeroSupportOpen.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

/-- A morphism from the unit module vanishes if its global unit section vanishes. -/
theorem eq_zero_of_app_top_toUnitSection_one {X : Scheme.{u}} {P : X.Modules} (F : 𝟙_ X.Modules ⟶ P)
    (h : F.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = 0) : F = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  have hm : m = (Scheme.Modules.ofUnitSection U m) • Scheme.Modules.toUnitSection U (1 : Γ(X, U))
    := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h1 : Scheme.Modules.toUnitSection U (1 : Γ(X, U)) =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1)
        := by
    apply Scheme.Modules.ofUnitSection_injective U
    rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one]
  have hnat : F.app U ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (Scheme.Modules.toUnitSection ⊤ 1)) =
      P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (F.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
        := by
    have := F.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op
    exact congr($(this) (Scheme.Modules.toUnitSection ⊤ 1))
  rw [hm, Scheme.Modules.Hom.app_smul, h1, hnat, h, map_zero, smul_zero,
    Scheme.Modules.Hom.zero_app]
  rfl

/-- Nonzero sections of a one-dimensional space of sections have the same zero scheme. -/
theorem zeroSchemeIdeal_eq_of_finrank_H0_eq_one
    {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (𝒱 : Y.TwoAffineOpenCover) (h0 : Module.finrank k (𝒱.sectionsOf y P).H0 = 1)
    (σ₀ σ : 𝟙_ Y.Modules ⟶ P) (hσ₀ : σ₀ ≠ 0) (hσ : σ ≠ 0) :
    Scheme.Modules.zeroSchemeIdeal σ = Scheme.Modules.zeroSchemeIdeal σ₀ := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom y P ⊤
  obtain ⟨e1, -⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 y P
  have hfin : Module.finrank k Γ(P, ⊤) = 1 := by rw [e1.finrank_eq, h0]
  have hv₀0 : σ₀.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) ≠ 0 := fun h => hσ₀
    (eq_zero_of_app_top_toUnitSection_one σ₀ h)
  have hv0 : σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) ≠ 0 := fun h => hσ
    (eq_zero_of_app_top_toUnitSection_one σ h)
  obtain ⟨lam, hlam⟩ := (finrank_eq_one_iff_of_nonzero' _ hv₀0).1 hfin (σ.app ⊤
    (Scheme.Modules.toUnitSection ⊤ 1))
  have hlam0 : lam ≠ 0 := by rintro rfl; exact hv0 (by rw [← hlam, zero_smul])
  have hu : IsUnit (algebraMap k Γ(Y, ⊤) lam) := (IsUnit.mk0 lam hlam0).map _
  have h : σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = (algebraMap k Γ(Y, ⊤) lam) • σ₀.app ⊤
    (Scheme.Modules.toUnitSection ⊤ 1) :=
    hlam.symm
  exact (hP.zeroSchemeIdeal_eq_of_app_eq_smul σ₀ σ _ hu h).symm

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)

/-- The two-affine cover obtained by base change to the chosen fibre. -/
noncomputable def coverOfFibre (𝒱 : C.TwoAffineOpenCover) :
    (pullback c (s ≫ t)).TwoAffineOpenCover :=
  have : IsAffineHom (pullback.fst c (s ≫ t)) :=
    (_root_.AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{u}).of_isPullback
      (IsPullback.of_hasPullback c (s ≫ t)).flip inferInstance
  { U0 := (pullback.fst c (s ≫ t)) ⁻¹ᵁ 𝒱.U0
    U1 := (pullback.fst c (s ≫ t)) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

/-- The fibre cohomology comparison identifies the zero schemes of nonzero sections. -/
theorem zeroSchemeIdeal_eq_of_forall_finrank_H0_eq_one (𝒱 : C.TwoAffineOpenCover)
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    (σ₀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
      M)
    (hσ₀ : σ₀ ≠ 0) (hσ : σ ≠ 0) :
    Scheme.Modules.zeroSchemeIdeal σ = Scheme.Modules.zeroSchemeIdeal σ₀ := by
  obtain ⟨𝒲, ⟨e2⟩, -⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M
    s
    (pullback.snd c (s ≫ t)) (mapOnProdOver c s rfl) (isPullback_mapOnProdOver c s rfl)
    ((Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M) (Iso.refl _) (coverOfFibre c t s 𝒱)
  exact zeroSchemeIdeal_eq_of_finrank_H0_eq_one (pullback.snd c (s ≫ t)) _ (hM.pullback _)
    (coverOfFibre c t s 𝒱)
    (by rw [e2.finrank_eq, h0 𝒲]) σ₀ σ hσ₀ hσ

end AlgebraicGeometry.RelPicard.H0LINK

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  IsOpenImmersion.lift
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.Hom.zero_app
  Scheme.Modules.pushforward
  IsProper
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.preimage_inf
  Scheme.Modules.Hom
  UniversallyClosed
  Scheme.Pullback.range_fst
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Hom.comp_base
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackPushforwardAdjunction
  Scheme.Modules.pullbackId
  Scheme.Hom.preimage_sup
  Scheme.Modules
  Scheme.Opens
  IsAffineHom
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  range_eq_univ
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.algebraOfHom
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.Modules.toUnitSection
  Scheme.Modules.ofUnitSection
  Scheme.Modules.ofUnitSection_toUnitSection
  Scheme.Modules.ofUnitSection_injective
  Scheme.Modules.ofUnitSection_map
  Scheme.Modules.ofUnitSection_smul
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
  Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  fibreAt
  fibreModule
  isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
  pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback)

namespace E6A

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

/-- Naturally isomorphic functors detect the same zero morphisms. -/
theorem map_eq_zero_iff_of_natIso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒟]
    {F G : 𝒞 ⥤ 𝒟} (α : F ≅ G) {X Y : 𝒞} (f : X ⟶ Y) : F.map f = 0 ↔ G.map f = 0 := by
  constructor
  · intro h
    have := α.hom.naturality f
    rw [h] at this
    have h2 : α.hom.app X ≫ G.map f = 0 := this.symm.trans zero_comp
    exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp h2
  · intro h
    have := α.inv.naturality f
    rw [h] at this
    have h2 : α.inv.app X ≫ F.map f = 0 := this.symm.trans zero_comp
    exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp h2

/-- Pullback along a scheme isomorphism detects nonzero morphisms. -/
theorem map_ne_zero_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M M' : X.Modules}
    {f : M ⟶ M'}
    (hf : f ≠ 0) : (Scheme.Modules.pullback F).map f ≠ 0 := by
  have : (Scheme.Modules.pullback F).Faithful := (FinTransport.pullbackEquivOfIso (asIso
    F)).faithful_functor
  intro h
  exact hf ((Scheme.Modules.pullback F).map_injective (h.trans ((Scheme.Modules.pullback
    F).map_zero _ _).symm))

section

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)

/-- The pushforward of the family of modules to the parameter scheme. -/
noncomputable abbrev N : T.Modules := (Scheme.Modules.pushforward (pullback.snd c t)).obj M

private noncomputable abbrev _root_.AlgebraicGeometry.RelPicard.E6A.counit :
  (Scheme.Modules.pullback (pullback.snd c t)).obj (N c t M) ⟶ M :=
  (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M

export _root_.AlgebraicGeometry.RelPicard.E6A (counit)

/-- Pull a local trivialization of the pushforward back to the family. -/
noncomputable def unitIsoPullbackN (W : T.Opens)
    (φ : (Scheme.Modules.pullback W.ι).obj (N c t M) ≅ 𝟙_ (W : Scheme.{u}).Modules) :
    𝟙_ (pullback c (W.ι ≫ t)).Modules ≅
      (Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj
        ((Scheme.Modules.pullback (pullback.snd c t)).obj (N c t M)) :=
  (Scheme.Modules.pullbackUnitIso (pullback.snd c (W.ι ≫ t))).symm ≪≫
    (Scheme.Modules.pullback (pullback.snd c (W.ι ≫ t))).mapIso φ.symm ≪≫
    (Scheme.Modules.pullbackComp (pullback.snd c (W.ι ≫ t)) W.ι).app (N c t M) ≪≫
    (Scheme.Modules.pullbackCongr (mapOnProdOver_snd c W.ι rfl).symm).app (N c t M) ≪≫
    ((Scheme.Modules.pullbackComp (mapOnProdOver c W.ι rfl) (pullback.snd c t)).app (N c t M)).symm

/-- The local section induced by the trivialization and the adjunction counit. -/
noncomputable def trivSection (W : T.Opens)
    (φ : (Scheme.Modules.pullback W.ι).obj (N c t M) ≅ 𝟙_ (W : Scheme.{u}).Modules) :
    𝟙_ (pullback c (W.ι ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj M :=
  (unitIsoPullbackN c t M W φ).hom ≫ (Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).map
    (counit c t M)

/-- Composition of the two product maps agrees with the associativity comparison. -/
theorem mapOnProdOver_comp_mapOnProdOver_eq (W : T.Opens) {k : Type u} [Field k]
    (x' : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})) :
    mapOnProdOver c x' rfl ≫ mapOnProdOver c W.ι rfl =
      (pullback.congrHom rfl (Category.assoc x' W.ι t).symm).hom ≫ mapOnProdOver c (x' ≫ W.ι) rfl
        := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mapOnProdOver_fst, pullback.congrHom_hom, pullback.lift_fst,
      Category.comp_id]
  · simp only [Category.assoc, mapOnProdOver_snd, pullback.congrHom_hom,
      Category.comp_id, mapOnProdOver_snd_assoc, pullback.lift_snd_assoc]

/-- The counit construction gives a nonzero section on each fibre. -/
theorem pullbackSection_trivSection_ne_zero [IsNoetherianRing R] [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover) [LocallyOfFiniteType t] (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    (W : T.Opens) (φ : (Scheme.Modules.pullback W.ι).obj (N c t M) ≅ 𝟙_ (W : Scheme.{u}).Modules)
    {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})) :
    Scheme.Modules.pullbackSection (mapOnProdOver c x' rfl) (trivSection c t M W φ) ≠ 0 := by
  have h0 := pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover R c 𝒱 t M hM
    hfib (x' ≫ W.ι)
  set m := mapOnProdOver c x' rfl
  set mW := mapOnProdOver c W.ι rfl
  let e : pullback c (x' ≫ W.ι ≫ t) ≅ pullback c ((x' ≫ W.ι) ≫ t) :=
    pullback.congrHom rfl (Category.assoc x' W.ι t).symm
  have hE : m ≫ mW = e.hom ≫ mapOnProdOver c (x' ≫ W.ι) rfl := mapOnProdOver_comp_mapOnProdOver_eq
    c t W x'
  have h1 : (Scheme.Modules.pullback e.hom).map
      ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ W.ι) rfl)).map (counit c t M)) ≠ 0 :=
    map_ne_zero_of_isIso e.hom h0
  have h2 : (Scheme.Modules.pullback (m ≫ mW)).map (counit c t M) ≠ 0 := by
    intro h; apply h1
    have := (map_eq_zero_iff_of_natIso (Scheme.Modules.pullbackCongr hE) (counit c t M)).mp h
    exact (map_eq_zero_iff_of_natIso
      (Scheme.Modules.pullbackComp e.hom (mapOnProdOver c (x' ≫ W.ι) rfl)).symm (counit c t M)).mp
        this
  have h3 : (Scheme.Modules.pullback m).map ((Scheme.Modules.pullback mW).map (counit c t M)) ≠ 0
    := by
    intro h; apply h2
    exact (map_eq_zero_iff_of_natIso (Scheme.Modules.pullbackComp m mW) (counit c t M)).mp h
  intro h
  apply h3
  rw [Scheme.Modules.pullbackSection_def] at h
  have h4 : (Scheme.Modules.pullback m).map (trivSection c t M W φ) = 0 := by
    have h' := congrArg (fun f => (Scheme.Modules.pullbackUnitIso m).hom ≫ f) h
    exact ((Scheme.Modules.pullbackUnitIso m).hom_inv_id_assoc
      ((Scheme.Modules.pullback m).map (trivSection c t M W φ))).symm.trans (h'.trans
        (Limits.comp_zero))
  have h5 : (Scheme.Modules.pullback m).map (unitIsoPullbackN c t M W φ).hom ≫
      (Scheme.Modules.pullback m).map ((Scheme.Modules.pullback mW).map (counit c t M)) = 0 :=
    ((Scheme.Modules.pullback m).map_comp _ _).symm.trans h4
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp h5

/-- A local trivialization gives the common closed support of all nonzero fibre sections. -/
theorem fibre_half [IsNoetherianRing R] [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover) [LocallyOfFiniteType t] (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    (W : T.Opens) (φ : (Scheme.Modules.pullback W.ι).obj (N c t M) ≅ 𝟙_ (W : Scheme.{u}).Modules) :
    ∃ Z : Set ↥(pullback c (W.ι ≫ t)), IsClosed Z ∧
      ∀ (k : Type u) [Field k] (x' : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})),
        (∃ σ₀ : 𝟙_ (pullback c (x' ≫ W.ι ≫ t)).Modules ⟶
            (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj
              ((Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj M), σ₀ ≠ 0) ∧
        ∀ σ : 𝟙_ (pullback c (x' ≫ W.ι ≫ t)).Modules ⟶
            (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj
              ((Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj M),
          σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x' ≫ W.ι ≫ t))) =
            (mapOnProdOver c x' rfl).base ⁻¹' Z := by
  have hMW : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj
    M) :=
    hM.pullback _
  refine ⟨((Scheme.Modules.zeroSchemeIdeal (trivSection c t M W φ)).support : Set _),
    (Scheme.Modules.zeroSchemeIdeal (trivSection c t M W φ)).support.isClosed, ?_⟩
  intro k _ x'
  have hσ₀ := pullbackSection_trivSection_ne_zero c t M 𝒱 hM hfib W φ x'
  refine ⟨⟨_, hσ₀⟩, ?_⟩
  intro σ hσ
  have hP : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj
      ((Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj M)) := hMW.pullback _
  have : IsAffineHom (pullback.fst c (x' ≫ W.ι ≫ t)) :=
    (_root_.AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{u}).of_isPullback
      (IsPullback.of_hasPullback c (x' ≫ W.ι ≫ t)).flip inferInstance
  have hcart : IsPullback (mapOnProdOver c x' rfl ≫ mapOnProdOver c W.ι rfl) (pullback.snd c (x' ≫
    W.ι ≫ t))
      (pullback.snd c t) (x' ≫ W.ι) :=
    (isPullback_mapOnProdOver c x' rfl).paste_horiz (isPullback_mapOnProdOver c W.ι rfl)
  obtain ⟨𝒲, ⟨e0⟩, -⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M
    (x' ≫ W.ι)
    (pullback.snd c (x' ≫ W.ι ≫ t)) (mapOnProdOver c x' rfl ≫ mapOnProdOver c W.ι rfl) hcart
    ((Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj ((Scheme.Modules.pullback
      (mapOnProdOver c W.ι rfl)).obj M))
    ((Scheme.Modules.pullbackComp (mapOnProdOver c x' rfl) (mapOnProdOver c W.ι rfl)).app M)
    (𝒱.preimage (pullback.fst c (x' ≫ W.ι ≫ t)))
  have h0 : Module.finrank k ((𝒱.preimage (pullback.fst c (x' ≫ W.ι ≫ t))).sectionsOf
      (pullback.snd c (x' ≫ W.ι ≫ t)) ((Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj
        ((Scheme.Modules.pullback (mapOnProdOver c W.ι rfl)).obj M))).H0 = 1 := by
    rw [e0.finrank_eq]; exact (hfib k (x' ≫ W.ι) 𝒲).2
  have hZ := H0LINK.zeroSchemeIdeal_eq_of_finrank_H0_eq_one _ _ hP _ h0 _ σ hσ₀ hσ
  rw [hZ, FinTransport.coe_support_zeroSchemeIdeal_pullbackSection _ hMW]

end

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

end AlgebraicGeometry.RelPicard.E6A

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  IsOpenImmersion.lift
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.Hom.zero_app
  Scheme.Modules.pushforward
  IsProper
  Scheme.Modules.pullback
  Scheme.Opens.range_ι
  Scheme.Hom
  Scheme.Hom.preimage_inf
  Scheme.Modules.Hom
  UniversallyClosed
  Scheme.Pullback.range_fst
  LocallyOfFiniteType
  Spec
  Scheme
  IsOpenImmersion
  Scheme.Hom.comp_base
  Flat
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackPushforwardAdjunction
  Scheme.Modules.pullbackId
  Scheme.Hom.preimage_sup
  Scheme.Modules
  Scheme.Opens
  IsAffineHom
  IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply
  range_eq_univ
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.algebraOfHom
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.Modules.toUnitSection
  Scheme.Modules.ofUnitSection
  Scheme.Modules.ofUnitSection_toUnitSection
  Scheme.Modules.ofUnitSection_injective
  Scheme.Modules.ofUnitSection_map
  Scheme.Modules.ofUnitSection_smul
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
  Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  baseChangeSnd
  fibreAt
  fibreModule
  isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover
  pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
  exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback)

namespace E6Glue

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

/-- The fibre support condition respects equality of the parameter map. -/
theorem finerAt_congr {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] {s₁ s₂ : Spec (CommRingCat.of k) ⟶ T} (h : s₁ = s₂) :
    FinTransport.FinerAt c U t M s₁ ↔ FinTransport.FinerAt c U t M s₂ := by
  subst h; exact Iff.rfl

/-- Containment of a field-valued point is determined by its unique point. -/
theorem range_subset_iff {k : Type u} [Field k] {T : Scheme.{u}} (s : Spec (CommRingCat.of k) ⟶ T)
    (A : Set T) :
    Set.range ⇑s ⊆ A ↔ s (IsLocalRing.closedPoint k) ∈ A := by
  constructor
  · intro h; exact h ⟨_, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]

end AlgebraicGeometry.RelPicard.E6Glue

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.full_pullback_of_isIso
attribute [local instance] AlgebraicGeometry.RelPicard.FinTransport.faithful_pullback_of_isIso

end JacobianVarieties.Picard.Proofs.ZeroSupportOpen

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

namespace AlgebraicGeometry.RelPicard

universe u

open JacobianVarieties.Picard.Proofs.ZeroSupportOpen.AlgebraicGeometry.RelPicard in
/-- The fibrewise zero-scheme support condition is represented by an open parameter locus. -/
theorem exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1) :
    ∃ U' : T.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ (U' : Set T) ↔
        ∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s
          rfl)).obj M,
          σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆
            ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t))) := by
  have hN : Scheme.Modules.IsInvertible (E6A.N c t M) :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (isLocallyFreeOfRank_pushforward_of_forall_fibre_of_twoAffineOpenCover R c 𝒱 t M hM 1 hfib)
  choose W hpW hφ using hN.exists_trivialization
  have hloc : ∀ p : T, ∃ U'p : (W p : Scheme.{u}).Opens,
      ∀ (k : Type u) [Field k] (x' : Spec (CommRingCat.of k) ⟶ (W p : Scheme.{u})),
        Set.range ⇑x' ⊆ (U'p : Set (W p : Scheme.{u})) ↔ FinTransport.FinerAt c U t M (x' ≫ (W
          p).ι) := by
    intro p
    obtain ⟨Z, hZc, hZ⟩ := E6A.fibre_half c t M 𝒱 hM hfib (W p) (hφ p).some
    obtain ⟨U'p, hU'p⟩ := E6B.exists_opens_range_subset_iff_preimage_subset c U ((W p).ι ≫ t) Z hZc
    refine ⟨U'p, fun k _ x' => (hU'p k x').trans (Iff.trans ?_
      (FinTransport.finerAt_transport c U t ((W p).ι ≫ t) ⟨(W p).ι, rfl⟩ M hM
        ((Scheme.Modules.pullback (mapOnProdOver c (W p).ι rfl)).obj M) (Iso.refl _) x'))⟩
    obtain ⟨⟨σ₀, hσ₀⟩, hall⟩ := hZ k x'
    constructor
    · intro hsub σ hσ
      rw [hall σ hσ]; exact hsub
    · intro hfin
      have := hfin σ₀ hσ₀
      rw [hall σ₀ hσ₀] at this; exact this
  choose U'p hU'p using hloc
  refine ⟨⨆ p, (W p).ι ''ᵁ (U'p p), fun k _ s => ?_⟩
  constructor
  · intro hs
    have hpt : s (IsLocalRing.closedPoint k) ∈ ((⨆ p, (W p).ι ''ᵁ (U'p p) : T.Opens) : Set T) := hs
      ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hpt
    obtain ⟨q, hq, hqe⟩ := hp
    have hsW : Set.range ⇑s ⊆ Set.range ⇑(W p).ι := by
      rw [E6Glue.range_subset_iff]; exact ⟨q, hqe⟩
    have hx' : IsOpenImmersion.lift (W p).ι s hsW ≫ (W p).ι = s := IsOpenImmersion.lift_fac _ _ _
    refine (E6Glue.finerAt_congr c U t M hx').mp ((hU'p p k _).mp ?_)
    rw [E6Glue.range_subset_iff]
    have h1 : (W p).ι (IsOpenImmersion.lift (W p).ι s hsW (IsLocalRing.closedPoint k)) = (W p).ι q
      := by
      exact (congrArg (fun f : Spec (CommRingCat.of k) ⟶ T =>
        f.base (IsLocalRing.closedPoint k)) hx').trans hqe.symm
    rwa [(W p).ι.isOpenEmbedding.injective h1]
  · intro hfin
    set p := s (IsLocalRing.closedPoint k) with hp
    have hsW : Set.range ⇑s ⊆ Set.range ⇑(W p).ι := by
      rw [Scheme.Opens.range_ι, E6Glue.range_subset_iff]; exact hpW p
    have hx' : IsOpenImmersion.lift (W p).ι s hsW ≫ (W p).ι = s := IsOpenImmersion.lift_fac _ _ _
    have h1 : Set.range ⇑(IsOpenImmersion.lift (W p).ι s hsW) ⊆ (U'p p : Set (W p : Scheme.{u})) :=
      (hU'p p k _).mpr ((E6Glue.finerAt_congr c U t M hx').mpr hfin)
    rintro _ ⟨w, rfl⟩
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨p, IsOpenImmersion.lift (W p).ι s hsW w, h1 ⟨w, rfl⟩, ?_⟩
    have h2 := Scheme.Hom.comp_apply (IsOpenImmersion.lift (W p).ι s hsW) (W p).ι w
    rw [hx'] at h2
    exact h2.symm
end AlgebraicGeometry.RelPicard
end ProofImplementation

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
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
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
attribute [-simp]
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
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
