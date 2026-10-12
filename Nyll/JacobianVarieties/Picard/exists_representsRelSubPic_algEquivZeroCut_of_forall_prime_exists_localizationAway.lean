/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Choose
import Mathlib.Topology.Sets.Opens
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.LocalGeometry.LocalRepresentabilityULift
import Nyll.JacobianVarieties.Picard.RelSubPicGlue
import Nyll.SchemeTheory.LocalGeometry.OverTotalOpenChart
import Nyll.JacobianVarieties.Picard.IsSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections
import Nyll.AlgebraicCurves.Geometry.Curves.smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# Gluing Picard representations from localizations

Representations over a covering family of localizations glue to a global Picard representation.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.LocalizedRepresentation
attribute [-instance]
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
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
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

namespace N11

/-- Restrict a represented functor by the pullback adjunction over the base. -/
noncomputable def representableByPullback {S U : Scheme.{u}} (j : U ⟶ S)
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    {Z : Over S} (e : G.RepresentableBy Z) :
    ((Over.map j).op ⋙ G).RepresentableBy ((Over.pullback j).obj Z) where
  homEquiv {X} := ((Over.mapPullbackAdj j).homEquiv X Z).symm.trans e.homEquiv
  homEquiv_comp {X X'} φ g := by
    change e.homEquiv (((Over.mapPullbackAdj j).homEquiv X Z).symm (φ ≫ g)) =
      G.map ((Over.map j).map φ).op (e.homEquiv (((Over.mapPullbackAdj j).homEquiv X' Z).symm g))
    rw [Adjunction.homEquiv_naturality_left_symm, e.homEquiv_comp]

theorem app_eq {X : Scheme.{u}} {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)}
    (τ : uliftYoneda.{u + 1}.obj X ⟶ F)
    (Z : Scheme.{u}ᵒᵖ) (a : (uliftYoneda.{u + 1}.obj X).obj Z) :
    τ.app Z a = uliftYonedaEquiv (uliftYoneda.{u + 1}.map a.down ≫ τ) := by
  obtain ⟨T⟩ := Z
  rw [uliftYonedaEquiv_apply]
  change τ.app (op T) a = τ.app (op T) ((uliftYoneda.{u + 1}.map a.down).app (op T) ⟨𝟙 T⟩)
  rw [uliftYoneda_map_app]
  change τ.app (op T) a = τ.app (op T) ⟨𝟙 T ≫ a.down⟩
  rw [Category.id_comp]
  cases a
  rfl

end N11

open N11
end JacobianVarieties.Picard.Proofs.LocalizedRepresentation

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.LocalizedRepresentation
universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.AlgebraicGeometry.SmoothProperCurve _root_.NeronModelInfra _root_.GoodReductionJacobian
open _root_.JacobianVarieties.Picard.Proofs.LocalizedRepresentation.N11

/-- Representations over a covering family of localizations glue to a global
Picard representation. -/
theorem exists_representsRelSubPic_algEquivZeroCut_of_forall_prime_exists_localizationAway
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤)))
    (hloc : ∀ 𝔭 : PrimeSpectrum R, ∃ (f : R) (_ : f ∉ 𝔭.asIdeal)
      (D' : RelativePic0Designation (Localization.Away f) (SmoothProperCurve.baseChange R c
        (Localization.Away f))),
      Nonempty (RepresentsRelSubPic (SmoothProperCurve.baseChange R c (Localization.Away f))
          (sectionBaseChange (Localization.Away f) ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange R c (Localization.Away f))
            (sectionBaseChange (Localization.Away f) ε)) D') ∧
        Smooth D'.toBase ∧ IsSeparated D'.toBase ∧ QuasiCompact D'.toBase ∧
        Surjective D'.toBase ∧ GeometricallyConnected D'.toBase) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧
        Surjective D.toBase ∧ GeometricallyConnected D.toBase := by
  classical
  have hG := isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections R c ε hH0
  choose f hf D' hD' using hloc
  let G := relSubPicPresheaf c ε (algEquivZeroCut c ε)
  let Rl : PrimeSpectrum R → Type u := fun i => Localization.Away (f i)
  let jm : ∀ i, Spec (CommRingCat.of (Rl i)) ⟶ Spec (CommRingCat.of R) := fun i => specMap R (Rl i)
  have hjo : ∀ i, IsOpenImmersion (jm i) := fun i => IsOpenImmersion.of_isLocalization (f i)
  have h' : ∀ i, RepresentsRelSubPic (SmoothProperCurve.baseChange R c (Rl i)) (sectionBaseChange
    (Rl i) ε)
      (algEquivZeroCut _ _) (D' i) := fun i => Classical.choice (hD' i).1
  let e : ∀ i, ((Over.map (jm i)).op ⋙ G).RepresentableBy (Over.mk (D' i).toBase) :=
    fun i => AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε (Rl i) (h' i)
  have hch := fun i =>
    Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
      (jm i) G (D' i).toBase (e i)
  choose φ hφ₁ hφ₂ hφ₃ using hch
  have hφ : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (φ i) := hφ₂
  have hcov : ∀ x : Spec (CommRingCat.of R), ∃ i, x ∈ Set.range (jm i).base := by
    intro x
    refine ⟨x, ?_⟩
    have hr := PrimeSpectrum.localization_away_comap_range (Rl x) (f x)
    have hx : x ∈ (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum R)) := hf x
    rw [← hr] at hx
    exact hx
  have hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc φ) := by
    constructor
    intro T s
    obtain ⟨x, rfl⟩ : ∃ x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal, uliftYonedaEquiv x = s :=
      uliftYonedaEquiv.{u + 1}.surjective s
    let t : T ⟶ Spec (CommRingCat.of R) := (uliftYonedaEquiv x).1
    let V : PrimeSpectrum R → T.Opens := fun i => t ⁻¹ᵁ (Scheme.Hom.opensRange (jm i))
    have hV : TopologicalSpace.IsOpenCover V :=
      TopologicalSpace.IsOpenCover.mk <| top_le_iff.mp fun p _ => by
        obtain ⟨i, hi⟩ := hcov (t.base p)
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
        change t.base p ∈ (Scheme.Hom.opensRange (jm i) : Set _)
        rw [Scheme.Hom.coe_opensRange]
        exact hi
    refine GrothendieckTopology.superset_covering _ ?_
      ((T.openCoverOfIsOpenCover V hV).mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    change PrimeSpectrum R at i
    have hrange : Set.range ((uliftYonedaEquiv (uliftYoneda.{u + 1}.map (V i).ι ≫ x)).1).base ⊆
        Set.range (jm i).base := by
      have hn : G.overTotal.map (V i).ι.op (uliftYonedaEquiv x) =
          uliftYonedaEquiv (uliftYoneda.{u + 1}.map (V i).ι ≫ x) := uliftYonedaEquiv_naturality _ _
      rw [← hn]
      rintro _ ⟨v, rfl⟩
      change t.base ((V i).ι.base v) ∈ Set.range (jm i).base
      rw [← Scheme.Hom.coe_opensRange]
      exact v.2
    obtain ⟨ψ, hψ⟩ := hφ₃ i (uliftYoneda.{u + 1}.map (V i).ι ≫ x) hrange
    refine ⟨(Sigma.ι (fun i => uliftYoneda.{u + 1}.obj ((D' i).P)) i).app _ ⟨ψ⟩, ?_⟩
    change (Sigma.desc φ).app (op (V i).toScheme)
        ((Sigma.ι (fun i => uliftYoneda.{u + 1}.obj ((D' i).P)) i).app
          (op (V i).toScheme) ⟨ψ⟩) = G.overTotal.map (V i).ι.op (uliftYonedaEquiv x)
    have hdesc := congrArg
      (fun τ : uliftYoneda.{u + 1}.obj ((D' i).P) ⟶ G.overTotal =>
        τ.app (op (V i).toScheme)
          (show (uliftYoneda.{u + 1}.obj ((D' i).P)).obj (op (V i).toScheme) from ⟨ψ⟩))
      (Sigma.ι_comp_desc φ i)
    exact hdesc.trans ((app_eq (φ i) (op (V i).toScheme) ⟨ψ⟩).trans
      ((congrArg uliftYonedaEquiv hψ).trans
        (uliftYonedaEquiv_naturality x (V i).ι.op).symm))
  let D : RelativePic0Designation R c := RelPicard.gluedDesignation hG φ hφ
  obtain ⟨hD⟩ := RelPicard.RepresentsRelSubPic.nonempty_gluedDesignation hG φ hφ
  refine ⟨D, ⟨hD⟩, ?_⟩
  have hiso : ∀ i, ∃ ei : pullback D.toBase (jm i) ≅ (D' i).P, ei.hom ≫ (D' i).toBase =
    pullback.snd D.toBase (jm i) := by
    intro i
    let e₁ : ((Over.map (jm i)).op ⋙ G).RepresentableBy ((Over.pullback (jm i)).obj (Over.mk
      D.toBase)) :=
      representableByPullback (jm i) G hD.representableBy
    let ii := Functor.RepresentableBy.uniqueUpToIso e₁ (e i)
    refine ⟨(Over.forget _).mapIso ii, ?_⟩
    have := Over.w ii.hom
    exact this
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hf ⟨𝔪, h𝔪.isPrime⟩ (hle (Ideal.subset_span ⟨⟨𝔪, h𝔪.isPrime⟩, rfl⟩))
  apply
    smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top
    D.toBase f hspan
  intro i
  obtain ⟨ei, hei⟩ := hiso i
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hD' i
  have key : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso], P (D' i).toBase → P (pullback.snd
    D.toBase (jm i)) := by
    intro P _ hP
    rw [← hei]
    exact (MorphismProperty.cancel_left_of_respectsIso P ei.hom (D' i).toBase).mpr hP
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Smooth.{u})
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @QuasiCompact.{u})
  have : MorphismProperty.RespectsIso (@GeometricallyConnected.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @GeometricallyConnected.{u})
  exact ⟨key @Smooth h1, key @IsSeparated h2, key @QuasiCompact h3, key @Surjective h4,
    key @GeometricallyConnected h5⟩
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
  AlgebraicGeometry.RelPicard.isOpenImmersion_toGlued
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
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
attribute [-simp]
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
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
attribute [-simp]
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
