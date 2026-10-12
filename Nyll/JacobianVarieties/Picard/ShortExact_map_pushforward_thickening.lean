/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_exteriorPower_free_iso_unit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import Nyll.AlgebraicCurves.Geometry.Picard.Nonempty_pullback_sectionTwist_iso
import Nyll.SchemeTheory.Modules.PullbackUnitComposition
import Nyll.SchemeTheory.Modules.OpenImmersionUnit

/-!
# Pushforward of a short exact sequence on a section thickening

This file proves preservation of a specified short exact sequence supported on an infinitesimal
thickening of a section of a proper smooth relative curve. The comparison map is required to
agree with the original adjunction-unit map, and the sequence remains short exact after
pushforward to the base.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ShortExact_map_pushforward_thickening
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
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
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.TensorProduct

namespace Ws31X1
open AlgebraicGeometry.Scheme.Modules

/-- Restrict a trivialization on an open subset to a smaller open subset. -/
noncomputable def restrictTriv {Z : Scheme.{u}} {N : Z.Modules} {U₀ U : Z.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj N ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj N ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (Z.homOfLE_ι h).symm).app N ≪≫
    ((pullbackComp (Z.homOfLE h) U₀.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (Z.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (Z.homOfLE h)
end Ws31X1

namespace Ws31ThetaF

open AlgebraicGeometry.Scheme.Modules

theorem locallyTrivialOver {Z T : Scheme.{u}} (q : Z ⟶ T) [UniversallyClosed q]
    (hinj : Function.Injective q.base) (hsurj : Function.Surjective q.base)
    (N : Z.Modules) (hN : IsInvertible N) (t : T) :
    ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅
        𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules) := by
  obtain ⟨z, hz⟩ := hsurj t
  obtain ⟨V, hzV, ⟨eV⟩⟩ := hN.exists_trivialization z
  have hcl : IsClosed (q.base '' ((V : Set Z)ᶜ)) :=
    q.isClosedMap _ (isClosed_compl_iff.mpr V.isOpen)
  let W : T.Opens := ⟨(q.base '' ((V : Set Z)ᶜ))ᶜ, isOpen_compl_iff.mpr hcl⟩
  have htW : t ∈ W := by
    rintro ⟨z', hz'V, hz't⟩
    apply hz'V
    rw [hinj (hz't.trans hz.symm)]
    exact hzV
  have hle : q ⁻¹ᵁ W ≤ V := by
    intro z' hz'
    by_contra h
    exact hz' ⟨z', h, rfl⟩
  exact ⟨W, htW, ⟨Ws31X1.restrictTriv hle eV⟩⟩

section setting

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
lemma rigSection_snd : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _

scoped instance smooth_snd : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback c t) (inferInstance : SmoothOfRelativeDimension 1 c)

scoped instance isClosedImmersion_rigSection : IsClosedImmersion (rigSection c t ε) := by
  have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
    rw [rigSection_snd]; infer_instance
  exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)

lemma isInvertible_sectionIdeal : (sectionIdeal c ε t).IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t)
    (rigSection c t ε) (rigSection_snd k c ε t)

lemma pker (n : ℕ) :
    IsFinite ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) ∧
      (∀ s : T, ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).finrank s = n) ∧
      Flat ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) ∧
      LocallyOfFinitePresentation ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) :=
  Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := pullback.snd c t)
    (rigSection c t ε) (rigSection_snd k c ε t) n

omit [SmoothOfRelativeDimension 1 c] in
lemma range_rigSection_eq_support :
    Set.range (rigSection c t ε) =
      (((sectionIdeal c ε t).support : Closeds ↥(pullback c t)) : Set ↥(pullback c t)) := by
  change _ = (((rigSection c t ε).ker.support : Closeds ↥(pullback c t)) : Set ↥(pullback c t))
  rw [Scheme.Hom.support_ker, (rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq]

omit [SmoothOfRelativeDimension 1 c] in
lemma injective_q (n : ℕ) (hn : n ≠ 0) :
    Function.Injective ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).base := by
  intro z z' h
  have hz : (sectionIdeal c ε t ^ n).subschemeι z ∈ Set.range (rigSection c t ε) := by
    rw [range_rigSection_eq_support, ← Scheme.IdealSheafData.support_pow _ n hn,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hz' : (sectionIdeal c ε t ^ n).subschemeι z' ∈ Set.range (rigSection c t ε) := by
    rw [range_rigSection_eq_support, ← Scheme.IdealSheafData.support_pow _ n hn,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z', rfl⟩
  obtain ⟨s, hs⟩ := hz
  obtain ⟨s', hs'⟩ := hz'
  have e1 : (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z) = s := by
    rw [← hs, ← Scheme.Hom.comp_apply, rigSection_snd]; rfl
  have e2 : (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z') = s' := by
    rw [← hs', ← Scheme.Hom.comp_apply, rigSection_snd]; rfl
  have hss : s = s' := by
    rw [← e1, ← e2]
    exact h
  apply (sectionIdeal c ε t ^ n).subschemeι.isClosedEmbedding.injective
  rw [← hs, ← hs', hss]

omit [SmoothOfRelativeDimension 1 c] in
lemma surjective_q (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).base := by
  intro s
  have hs : rigSection c t ε s ∈ Set.range ((sectionIdeal c ε t ^ n).subschemeι) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ n hn,
      ← range_rigSection_eq_support]
    exact ⟨s, rfl⟩
  obtain ⟨z, hz⟩ := hs
  refine ⟨z, ?_⟩
  change (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z) = s
  rw [hz, ← Scheme.Hom.comp_apply, rigSection_snd]
  rfl

variable (M : RigidifiedLineBundle c ε t)

lemma isInvertible_G (r : ℕ) : IsInvertible (M.L ⊗ sectionTwist c ε t r) :=
  M.isInvertible.tensor ((isInvertible_sectionIdeal k c ε t).pow r).isInvertible_invModule

theorem lf [LocallyOfFiniteType t] (r n : ℕ) (hn : n ≠ 0) :
    IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c t)).obj
        ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj
            (M.L ⊗ sectionTwist c ε t r)))) := by
  obtain ⟨hfin, hrk, hflat, hlfp⟩ := pker k c ε t n
  have := hfin; have := hflat; have := hlfp
  have hN := locallyTrivialOver ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t)
    (injective_q k c ε t n hn) (surjective_q k c ε t n hn) _
    ((isInvertible_G k c ε t M r).pullback ((sectionIdeal c ε t ^ n).subschemeι))
  have h :=
    Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
      ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) n hrk _ hN
  exact IsLocallyFreeOfRank.of_iso
    ((pushforwardComp ((sectionIdeal c ε t ^ n).subschemeι) (pullback.snd c t)).app _).symm h

end setting

end Ws31ThetaF

noncomputable section

namespace Ws31ThetaF
namespace E6

/-- Recover a trivialization of a module sheaf from its trivial pullback along an isomorphism. -/
def isoUnitOfPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (L : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ 𝟙_ X.Modules) : L ≅ 𝟙_ Y.Modules :=
  ((Scheme.Modules.pullbackId Y).app L).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp (inv f) f).app L).symm ≪≫
    (Scheme.Modules.pullback (inv f)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (inv f)

/-- Identify pushforward along the inverse of a scheme isomorphism with pullback along the
isomorphism. -/
def pushforwardInvIsoPullback {X Y : Scheme.{u}} (e : X ≅ Y) :
    Scheme.Modules.pushforward e.inv ≅ Scheme.Modules.pullback e.hom :=
  Adjunction.leftAdjointUniq
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.inv)
      (Scheme.Modules.pushforward e.hom)
      ((Scheme.Modules.pushforwardId Y).symm ≪≫
        (Scheme.Modules.pushforwardCongr e.inv_hom_id).symm ≪≫
        (Scheme.Modules.pushforwardComp e.inv e.hom).symm)
      (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫ Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫
        Scheme.Modules.pushforwardId X)).toAdjunction
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom)

theorem nonempty_iso_unit_of_field {K : Type u} [Field K] (L : (Spec (CommRingCat.of K)).Modules)
    (hL : Scheme.Modules.IsInvertible L) : Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.exists_trivialization default
  have hU : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Unique.eq_default y]; exact hxU
  subst hU
  exact ⟨isoUnitOfPullbackIso (Spec (CommRingCat.of K)).topIso.hom L eU⟩

section setting2

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
lemma rigSection_snd : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _

scoped instance smooth_snd : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback c t) (inferInstance : SmoothOfRelativeDimension 1 c)

lemma isInvertible_sectionIdeal : (sectionIdeal c ε t).IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t)
    (rigSection c t ε) (rigSection_snd k c ε t)

theorem nonempty_pullback_rigSection_sectionTwist_iso (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionTwist c ε t r) ≅
      𝟙_ T.Modules) := by
  let ψ : SchemeHomOver t (𝟙 (Spec (CommRingCat.of k))) := ⟨t, Category.comp_id t⟩
  obtain ⟨e₁⟩ := AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso k c ε ψ r
  have hcomm : rigSection c t ε ≫ baseChangeSnd c ψ = t ≫ rigSection c (𝟙 _) ε :=
    rigSection_baseChangeSnd c ε ψ
  have hL₀ : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).obj
        (sectionTwist c ε (𝟙 (Spec (CommRingCat.of k))) r)) :=
    (((isInvertible_sectionIdeal k c ε (𝟙 _)).pow r).isInvertible_invModule).pullback _
  obtain ⟨e₀⟩ := nonempty_iso_unit_of_field _ hL₀
  exact ⟨(Scheme.Modules.pullback (rigSection c t ε)).mapIso e₁.symm ≪≫
    (Scheme.Modules.pullbackComp (rigSection c t ε) (baseChangeSnd c ψ)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcomm).app _ ≪≫
    ((Scheme.Modules.pullbackComp t (rigSection c (𝟙 _) ε)).app _).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso t⟩

theorem nonempty_pullback_rigSection_module_iso :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionIdeal c ε t).module ≅
      𝟙_ T.Modules) := by
  obtain ⟨eB⟩ := nonempty_pullback_rigSection_sectionTwist_iso k c ε t 1
  have h1 : sectionTwist c ε t 1 = (sectionIdeal c ε t).invModule := by
    unfold sectionTwist
    rw [pow_one]
  obtain ⟨eLD⟩ := ((isInvertible_sectionIdeal k c ε t).isInvertible_module).dual.2
  let σ := rigSection c t ε
  let A := (Scheme.Modules.pullback σ).obj (sectionIdeal c ε t).module
  let eB' : (Scheme.Modules.pullback σ).obj (sectionIdeal c ε t).invModule ≅ 𝟙_ T.Modules :=
    (Scheme.Modules.pullback σ).mapIso (eqToIso h1.symm) ≪≫ eB
  exact ⟨(ρ_ A).symm ≪≫ whiskerLeftIso A eB'.symm ≪≫
    (Scheme.Modules.pullbackTensorObjIso σ _ _).symm ≪≫
    (Scheme.Modules.pullback σ).mapIso eLD ≪≫ Scheme.Modules.pullbackUnitIso σ⟩

omit [SmoothOfRelativeDimension 1 c] in
theorem nonempty_pushforward_thickening_one_iso (H : (pullback c t).Modules) :
    Nonempty ((Scheme.Modules.pushforward (pullback.snd c t)).obj
      ((Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H)) ≅
      (Scheme.Modules.pullback (rigSection c t ε)).obj H) := by
  have : IsClosedImmersion (rigSection c t ε) := by
    have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
      rw [rigSection_snd]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)
  let i : (sectionIdeal c ε t).subscheme ⟶ pullback c t := (sectionIdeal c ε t).subschemeι
  let : IsIso (rigSection c t ε).toImage :=
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] =>
      (inferInstance : IsIso f.toImage)) (rigSection c t ε)
  let e : T ≅ (rigSection c t ε).ker.subscheme := asIso (rigSection c t ε).toImage
  have he : e.hom ≫ i = rigSection c t ε := by
    change (rigSection c t ε).toImage ≫ (rigSection c t ε).imageι = rigSection c t ε
    exact (rigSection c t ε).toImage_imageι
  have hq : i ≫ pullback.snd c t = e.inv :=
    (cancel_epi e.hom).mp
      ((Category.assoc e.hom i (pullback.snd c t)).symm.trans
        ((congrArg (fun g : T ⟶ pullback c t => g ≫ pullback.snd c t) he).trans
          ((rigSection_snd k c ε t).trans e.hom_inv_id.symm)))
  let N : (sectionIdeal c ε t).subscheme.Modules := (Scheme.Modules.pullback i).obj H
  let i₁ : (Scheme.Modules.pushforward (pullback.snd c t)).obj
      ((Scheme.Modules.pushforward i).obj N) ≅
      (Scheme.Modules.pushforward (i ≫ pullback.snd c t)).obj N :=
    (Scheme.Modules.pushforwardComp i (pullback.snd c t)).app N
  let i₂ : (Scheme.Modules.pushforward (i ≫ pullback.snd c t)).obj N ≅
      (Scheme.Modules.pushforward e.inv).obj N :=
    (Scheme.Modules.pushforwardCongr hq).app N
  let i₃ : (Scheme.Modules.pushforward e.inv).obj N ≅ (Scheme.Modules.pullback e.hom).obj N :=
    (pushforwardInvIsoPullback e).app N
  let i₄ : (Scheme.Modules.pullback e.hom).obj N ≅ (Scheme.Modules.pullback (e.hom ≫ i)).obj H :=
    (Scheme.Modules.pullbackComp e.hom i).app H
  let i₅ : (Scheme.Modules.pullback (e.hom ≫ i)).obj H ≅
      (Scheme.Modules.pullback (rigSection c t ε)).obj H :=
    (Scheme.Modules.pullbackCongr he).app H
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅⟩

theorem nonempty_pullback_rigSection_G_iso (M : RigidifiedLineBundle c ε t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (M.L ⊗ sectionTwist c ε t r) ≅
      𝟙_ T.Modules) := by
  obtain ⟨eM⟩ := M.rigidified
  obtain ⟨eS⟩ := nonempty_pullback_rigSection_sectionTwist_iso k c ε t r
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eM ⊗ᵢ eS) ≪≫ λ_ (𝟙_ T.Modules)⟩

end setting2

end Ws31ThetaF.E6

end

noncomputable section

namespace Ws31ThetaF
namespace E6

lemma surjective_of_comp_of_injective {A B C : Ab.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Function.Injective g) (h : Function.Surjective (f ≫ g)) : Function.Surjective f := by
  intro b
  obtain ⟨a, ha⟩ := h (g b)
  rw [ConcreteCategory.comp_apply] at ha
  exact ⟨a, hg ha⟩

lemma surjective_comp {A B C : Ab.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by rw [ConcreteCategory.comp_apply]⟩

lemma unit_app_unit_comp_map_pullbackObjUnitToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules) ≫
        (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      f.unitToPushforwardUnit := by
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  exact h


theorem surjective_unit_app_of_isAffineOpen_of_trivial {Z' Z : Scheme.{u}}
    (k : Z' ⟶ Z) [IsClosedImmersion k]
    (N : Z.Modules) (W : Z.Opens) (hW : IsAffineOpen W)
    (e : (Scheme.Modules.pullback W.ι).obj N ≅ 𝟙_ (↑W : Scheme.{u}).Modules) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app N).app W) := by
  have hsq : (k ⁻¹ᵁ W).ι ≫ k = (k ∣_ W) ≫ W.ι := (morphismRestrict_ι k W).symm
  have h1 := Scheme.Modules.unit_app_comp_pullbackComp_inv (k ⁻¹ᵁ W).ι k N W
  have hb1 : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction (k ⁻¹ᵁ W).ι).unit.app
        ((Scheme.Modules.pullback k).obj N)).app (k ⁻¹ᵁ W)) :=
    Scheme.Modules.bijective_unit_app_of_le_opensRange (k ⁻¹ᵁ W).ι _ _
      (Scheme.Opens.opensRange_ι _).ge
  apply surjective_of_comp_of_injective _ _ hb1.1
  apply (congrArg (fun g : Γ(N, W) ⟶ _ => Function.Surjective g.hom) h1).mp
  have hbij : Function.Bijective
      (((Scheme.Modules.pullbackComp (k ⁻¹ᵁ W).ι k).inv.app N).app
        (((k ⁻¹ᵁ W).ι ≫ k) ⁻¹ᵁ W)) :=
    (ConcreteCategory.isIso_iff_bijective (C := Ab)
      (((Scheme.Modules.pullbackComp (k ⁻¹ᵁ W).ι k).inv.app N).app
        (((k ⁻¹ᵁ W).ι ≫ k) ⁻¹ᵁ W))).mp
      ((Scheme.Modules.Hom.isIso_iff_isIso_app
        (φ := (Scheme.Modules.pullbackComp (k ⁻¹ᵁ W).ι k).inv.app N)).mp
          (Iso.isIso_inv ((Scheme.Modules.pullbackComp (k ⁻¹ᵁ W).ι k).app N))
          (((k ⁻¹ᵁ W).ι ≫ k) ⁻¹ᵁ W))
  refine surjective_comp _ _ ?_ hbij.2
  rw [hsq]
  have h3 := Scheme.Modules.unit_app_comp_pullbackComp_inv (k ∣_ W) W.ι N W
  have hb3 : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app N).app W) :=
    Scheme.Modules.bijective_unit_app_of_le_opensRange W.ι N W (Scheme.Opens.opensRange_ι W).ge
  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pullbackComp (k ∣_ W) W.ι).inv.app N).app ((k ∣_ W ≫ W.ι) ⁻¹ᵁ W))
    (ConcreteCategory.bijective_of_isIso _).1
  apply (congrArg (fun g : Γ(N, W) ⟶ _ => Function.Surjective g.hom) h3).mpr
  refine surjective_comp _ _ hb3.2 ?_
  have nat := (Scheme.Modules.pullbackPushforwardAdjunction (k ∣_ W)).unit.naturality e.hom
  have nat' := congrArg (fun φ => Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ W)) nat
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Scheme.Modules.Hom.comp_app] at nat'
  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pushforward (k ∣_ W)).map
        ((Scheme.Modules.pullback (k ∣_ W)).map e.hom)).app (W.ι ⁻¹ᵁ W))
    (ConcreteCategory.bijective_of_isIso _).1
  apply (congrArg (fun g : Γ((Scheme.Modules.pullback W.ι).obj N, W.ι ⁻¹ᵁ W) ⟶ _ =>
    Function.Surjective g.hom) nat').mp
  refine surjective_comp _ _ (ConcreteCategory.bijective_of_isIso _).2 ?_
  have hbijUnit : Function.Bijective
      (((Scheme.Modules.pushforward (k ∣_ W)).map
        (Scheme.Modules.pullbackUnitIso (k ∣_ W)).hom).app (W.ι ⁻¹ᵁ W)) :=
    (ConcreteCategory.isIso_iff_bijective (C := Ab)
      (((Scheme.Modules.pushforward (k ∣_ W)).map
        (Scheme.Modules.pullbackUnitIso (k ∣_ W)).hom).app (W.ι ⁻¹ᵁ W))).mp
      ((Scheme.Modules.Hom.isIso_iff_isIso_app
        (φ := (Scheme.Modules.pushforward (k ∣_ W)).map
          (Scheme.Modules.pullbackUnitIso (k ∣_ W)).hom)).mp
        (Iso.isIso_hom ((Scheme.Modules.pushforward (k ∣_ W)).mapIso
          (Scheme.Modules.pullbackUnitIso (k ∣_ W)))) (W.ι ⁻¹ᵁ W))
  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pushforward (k ∣_ W)).map
      (Scheme.Modules.pullbackUnitIso (k ∣_ W)).hom).app (W.ι ⁻¹ᵁ W))
    hbijUnit.1
  have hu := unit_app_unit_comp_map_pullbackObjUnitToUnit (k ∣_ W)
  have huApp := congrArg (fun φ => Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ W)) hu
  simp only [Scheme.Modules.Hom.comp_app] at huApp
  apply (congrArg
    (fun g : Γ((𝟙_ (↑W : Scheme.{u}).Modules), W.ι ⁻¹ᵁ W) ⟶ _ =>
      Function.Surjective g.hom) huApp).mpr
  have : IsAffine (↑W : Scheme.{u}) := hW
  have hV : IsAffineOpen (W.ι ⁻¹ᵁ W) := by
    rw [Scheme.Opens.ι_preimage_self]
    exact isAffineOpen_top _
  have hsurj : Function.Surjective ((k ∣_ W).app (W.ι ⁻¹ᵁ W)) := (k ∣_ W).app_surjective _ hV
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, hx⟩

end Ws31ThetaF.E6

end

namespace Ws31ThetaF

namespace BaseCase

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (N : Z.Modules)
    (U : Z.Opens) :
    Subsingleton Γ(N, U) := by
  have hU : U = ⊥ := le_bot_iff.mp fun x _ => isEmptyElim x
  let D : TopCat.Sheaf Ab Z.toTopCat := ⟨N.presheaf, N.isSheaf⟩
  have hT : IsTerminal (D.obj.obj (op U)) := D.isTerminalOfEqEmpty hU
  exact AddCommGrpCat.subsingleton_of_isZero hT.isZero

theorem isZero_of_subsingleton {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.Opens, Subsingleton Γ(M, U)) :
    IsZero M :=
  (IsZero.iff_id_eq_zero M).mpr (Scheme.Modules.hom_ext _ _ fun U => by
    have := h U
    ext x
    exact Subsingleton.elim _ _)

theorem isZero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (N : Z.Modules) : IsZero N :=
  isZero_of_subsingleton N (subsingleton_sections_of_isEmpty N)

theorem isZero_free_fin_zero (X : Scheme.{u}) :
    IsZero (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin 0))) :=
  (IsZero.iff_id_eq_zero _).mpr
    ((SheafOfModules.freeHomEquiv (R := X.ringCatSheaf)
      (SheafOfModules.free.{u} (ULift.{u} (Fin 0)))
      (I := ULift.{u} (Fin 0))).injective (funext fun i => isEmptyElim i))

theorem isLocallyFreeOfRank_zero_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    IsLocallyFreeOfRank 0 F :=
  ⟨fun _ => ⟨⊤, trivial, ⟨((Scheme.Modules.pullback (⊤ : X.Opens).ι).map_isZero hF).iso
    (isZero_free_fin_zero _)⟩⟩⟩

theorem nonempty_det_zero_iso_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    Nonempty (Scheme.Modules.det 0 F ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_exteriorPower_free_iso_unit X 0
  exact ⟨(exteriorPower X 0).mapIso (hF.iso (isZero_free_fin_zero X)) ≪≫ e⟩

theorem support_pow_zero {X : Scheme.{u}} (I : X.IdealSheafData) : (I ^ 0).support = ⊥ := by
  have h : I ^ 0 = ⊤ := pow_zero I
  rw [h]
  exact Scheme.IdealSheafData.support_top

theorem isEmpty_subscheme_of_support_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.support = ⊥) :
    IsEmpty I.subscheme := by
  refine ⟨fun z => ?_⟩
  have hz : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι, hI] at hz
  exact hz

end BaseCase

end Ws31ThetaF

namespace Ws31ThetaF

open AlgebraicGeometry.Scheme.Modules

theorem surjective_pushforward_map_app {Z Y : Scheme.{u}} (f : Z ⟶ Y) {M N : Z.Modules}
    (φ : M ⟶ N) (U : Y.Opens)
    (h : Function.Surjective (φ.app (f ⁻¹ᵁ U))) :
    Function.Surjective (((Scheme.Modules.pushforward f).map φ).app U) := by
  rw [Scheme.Modules.pushforward_map_app]
  exact h

theorem surjective_comp_app {X : Scheme.{u}} {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (U : X.Opens)
    (ha : Function.Surjective (a.app U)) (hb : Function.Surjective (b.app U)) :
    Function.Surjective ((a ≫ b).app U) := by
  rw [Scheme.Modules.Hom.comp_app]
  intro z
  obtain ⟨y, rfl⟩ := hb z
  obtain ⟨x, rfl⟩ := ha y
  exact ⟨x, rfl⟩

theorem surjective_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Surjective (e.hom.app U) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2

theorem surjective_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Surjective (e.inv.app U) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv U)).2

theorem epi_unit_of_iso {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R)
    {A B : C} (φ : A ≅ B) (h : Epi (adj.unit.app A)) : Epi (adj.unit.app B) := by
  have e : adj.unit.app B = φ.inv ≫ adj.unit.app A ≫ (L ⋙ R).map φ.hom := by
    rw [← adj.unit.naturality φ.hom, CategoryTheory.Functor.id_map, φ.inv_hom_id_assoc]
  have := h
  rw [e]
  infer_instance

section unitfactor

variable {ZA ZB X : Scheme.{u}} (iA : ZA ⟶ X) (iB : ZB ⟶ X) (k : ZA ⟶ ZB) (hk : k ≫ iB = iA)

/-- Compare the nested pullback and pushforward with the direct pullback and pushforward along the
composite inclusion. -/
noncomputable def cmpIso (H : X.Modules) :
    (Scheme.Modules.pushforward iB).obj ((Scheme.Modules.pushforward k).obj
      ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback iB).obj H))) ≅
      (Scheme.Modules.pushforward iA).obj ((Scheme.Modules.pullback iA).obj H) :=
  (Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward iB).mapIso
    ((pullbackComp k iB).app H) ≪≫
    (pushforwardComp k iB).app ((Scheme.Modules.pullback (k ≫ iB)).obj H) ≪≫
    (Scheme.Modules.pushforward (k ≫ iB)).mapIso ((pullbackCongr hk).app H) ≪≫
    (pushforwardCongr hk).app ((Scheme.Modules.pullback iA).obj H)

theorem unit_app_eq_comp_unit (H : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction iA).unit.app H =
      (Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H ≫
        (Scheme.Modules.pushforward iB).map
          ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
            ((Scheme.Modules.pullback iB).obj H)) ≫
        (cmpIso iA iB k hk H).hom := by
  have u1 := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ iB))
    ((Scheme.Modules.pullbackPushforwardAdjunction iB).comp
      (Scheme.Modules.pullbackPushforwardAdjunction k))
    (pullbackComp k iB).hom H
  rw [conjugateEquiv_pullbackComp_hom, Adjunction.comp_unit_app, ← Iso.app_inv,
    Iso.comp_inv_eq] at u1
  have u2 := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction iA)
    (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ iB)) (pullbackCongr hk).hom H
  rw [conjugateEquiv_pullbackCongr_hom, ← Iso.app_inv, Iso.comp_inv_eq] at u2
  rw [u2, u1]
  simp only [cmpIso, Category.assoc, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.comp_map]


/-- The morphism induced by the adjunction unit for the intermediate inclusion and the comparison
isomorphism. -/
noncomputable def ΦGen (H : X.Modules) :
    (Scheme.Modules.pushforward iB).obj ((Scheme.Modules.pullback iB).obj H) ⟶
      (Scheme.Modules.pushforward iA).obj ((Scheme.Modules.pullback iA).obj H) :=
  (Scheme.Modules.pushforward iB).map
      ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
        ((Scheme.Modules.pullback iB).obj H)) ≫
    (cmpIso iA iB k hk H).hom

theorem unit_app_comp_ΦGen (H : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H ≫ ΦGen iA iB k hk H =
      (Scheme.Modules.pullbackPushforwardAdjunction iA).unit.app H := by
  rw [ΦGen]
  exact (unit_app_eq_comp_unit iA iB k hk H).symm

theorem ΦGen_app_surjective (H : X.Modules) (W : X.Opens)
    (h : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
        ((Scheme.Modules.pullback iB).obj H)).app
        (iB ⁻¹ᵁ W))) :
    Function.Surjective ((ΦGen iA iB k hk H).app W) := by
  rw [ΦGen]
  exact surjective_comp_app _ _ W (surjective_pushforward_map_app iB _ W h)
    (surjective_hom_app (cmpIso iA iB k hk H) W)

end unitfactor

private theorem _root_.Ws31ThetaF.nonempty_iso_unit_of_field {K : Type u} [Field K]
    (L : (Spec (CommRingCat.of K)).Modules)
    (hL : IsInvertible L) : Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) :=
  Ws31ThetaF.E6.nonempty_iso_unit_of_field L hL

section setting2

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

private theorem _root_.Ws31ThetaF.nonempty_pullback_rigSection_module_iso :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionIdeal c ε t).module ≅
      𝟙_ T.Modules) :=
  Ws31ThetaF.E6.nonempty_pullback_rigSection_module_iso k c ε t


omit [SmoothOfRelativeDimension 1 c] in
private theorem _root_.Ws31ThetaF.nonempty_pushforward_thickening_one_iso
    (H : (pullback c t).Modules) :
    Nonempty ((Scheme.Modules.pushforward (pullback.snd c t)).obj
      ((Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H)) ≅
      (Scheme.Modules.pullback (rigSection c t ε)).obj H) :=
  Ws31ThetaF.E6.nonempty_pushforward_thickening_one_iso k c ε t H


/-- Push forward the given module sheaf restricted to the subscheme cut out by the m-th power of
the section ideal. -/
noncomputable abbrev Fm (m : ℕ) (H : (pullback c t).Modules) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd c t)).obj
    ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ m).subschemeι)).obj
      ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ m).subschemeι)).obj H))

theorem lf_gen [LocallyOfFiniteType t] (H : (pullback c t).Modules) (hH : IsInvertible H)
    (m : ℕ) (hm : m ≠ 0) :
    IsLocallyFreeOfRank m (Fm k c ε t m H) := by
  obtain ⟨hfin, hrk, hflat, hlfp⟩ := pker k c ε t m
  have := hfin; have := hflat; have := hlfp
  have hN := locallyTrivialOver ((sectionIdeal c ε t ^ m).subschemeι ≫ pullback.snd c t)
    (injective_q k c ε t m hm) (surjective_q k c ε t m hm) _
      (hH.pullback ((sectionIdeal c ε t ^ m).subschemeι))
  have h :=
    Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
      ((sectionIdeal c ε t ^ m).subschemeι ≫ pullback.snd c t) m hrk _ hN
  exact IsLocallyFreeOfRank.of_iso
    ((pushforwardComp ((sectionIdeal c ε t ^ m).subschemeι) (pullback.snd c t)).app _).symm h

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
lemma pow_succ_le (m : ℕ) : sectionIdeal c ε t ^ (m + 1) ≤ sectionIdeal c ε t := by
  rw [pow_succ]
  intro U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact Ideal.mul_le_right

/-- The inclusion of the section subscheme into the thickening cut out by the (m + 1)-st power of
its ideal. -/
noncomputable def kIncl (m : ℕ) :
    (sectionIdeal c ε t).subscheme ⟶ (sectionIdeal c ε t ^ (m + 1)).subscheme :=
  (sectionIdeal c ε t).subschemeMap (sectionIdeal c ε t ^ (m + 1)) (𝟙 _)
    (by rw [Scheme.IdealSheafData.map_id]; exact pow_succ_le k c ε t m)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
lemma kIncl_comp (m : ℕ) :
    kIncl k c ε t m ≫ (sectionIdeal c ε t ^ (m + 1)).subschemeι =
      (sectionIdeal c ε t).subschemeι := by
  rw [kIncl, Scheme.IdealSheafData.subschemeMap_subschemeι, Category.comp_id]

scoped instance (m : ℕ) : IsClosedImmersion (kIncl k c ε t m) := by
  have : IsClosedImmersion (kIncl k c ε t m ≫ (sectionIdeal c ε t ^ (m + 1)).subschemeι) := by
    rw [kIncl_comp]; infer_instance
  exact IsClosedImmersion.of_comp (kIncl k c ε t m) ((sectionIdeal c ε t ^ (m + 1)).subschemeι)

/-- The adjunction unit restricting a module sheaf on the thickening to the section subscheme. -/
noncomputable def νT (H : (pullback c t).Modules) (m : ℕ) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app
    ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
lemma Φ_app_surjective (H : (pullback c t).Modules) (m : ℕ) (W : (pullback c t).Opens)
    (h : Function.Surjective
      ((νT k c ε t H m).app (((sectionIdeal c ε t ^ (m + 1)).subschemeι) ⁻¹ᵁ W))) :
    Function.Surjective
      ((ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι)
        (kIncl k c ε t m) (kIncl_comp k c ε t m) H).app W) :=
  ΦGen_app_surjective _ _ _ _ H W h
theorem g_eq_of_pin (H : (pullback c t).Modules) (hH : IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin :
      (Scheme.Modules.pullbackPushforwardAdjunction
        ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    S.g = e₂.hom ≫
      ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι)
        (kIncl k c ε t m) (kIncl_comp k c ε t m) H ≫ e₃.inv := by
  let iB := (sectionIdeal c ε t ^ (m + 1)).subschemeι
  let N := (Scheme.Modules.pullback iB).obj H
  let ν := (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app N
  have : Epi ((Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H) := by
    have hIm := (isInvertible_sectionIdeal k c ε t).pow (m + 1)
    obtain ⟨eLD⟩ := (hIm.isInvertible_module).dual.2
    let φ :
        (H ⊗ (sectionIdeal c ε t ^ (m + 1)).module) ⊗
          (sectionIdeal c ε t ^ (m + 1)).invModule ≅ H :=
      α_ _ _ _ ≪≫ whiskerLeftIso H eLD ≪≫ ρ_ H
    have hepi :=
      (Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact
      (sectionIdeal c ε t) (isInvertible_sectionIdeal k c ε t)
        (H ⊗ (sectionIdeal c ε t ^ (m + 1)).module)
      (hH.tensor hIm.isInvertible_module) (m + 1) (m + 1) 0 (Nat.zero_add _)).1
    exact epi_unit_of_iso (Scheme.Modules.pullbackPushforwardAdjunction iB) φ hepi
  have h2 := hpin.trans (unit_app_comp_ΦGen _ iB _ (kIncl_comp k c ε t m) H).symm
  have hψ := (cancel_epi _).mp h2
  have hψ' : e₂.inv ≫ S.g ≫ e₃.hom =
      ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι)
        (kIncl k c ε t m)
        (kIncl_comp k c ε t m) H := hψ
  exact ((Iso.eq_comp_inv e₃).mpr ((Iso.inv_comp_eq e₂).mp hψ')).trans (Category.assoc _ _ _)

theorem shortExact_map_pushforward_thickening [LocallyOfFiniteType t]
    (H : (pullback c t).Modules) (hH : IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules) (hS : S.ShortExact)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin :
      (Scheme.Modules.pullbackPushforwardAdjunction
        ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    (S.map (Scheme.Modules.pushforward (pullback.snd c t))).ShortExact := by
  let iB := (sectionIdeal c ε t ^ (m + 1)).subschemeι
  let q := iB ≫ pullback.snd c t
  let N := (Scheme.Modules.pullback iB).obj H
  let ν := (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app N
  have hg : S.g = e₂.hom ≫
      ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι)
        (kIncl k c ε t m) (kIncl_comp k c ε t m) H ≫ e₃.inv :=
    g_eq_of_pin k c ε t H hH m S e₂ e₃ hpin
  obtain ⟨hfin, -, -, -⟩ := pker k c ε t (m + 1)
  have := hfin
  apply shortExact_map_pushforward_of_forall_exists_surjective_app (pullback.snd c t) S hS
  intro U y hyU
  obtain ⟨W₀, hyW₀, ⟨e₀⟩⟩ := locallyTrivialOver q (injective_q k c ε t (m + 1) (Nat.succ_ne_zero m))
    (surjective_q k c ε t (m + 1) (Nat.succ_ne_zero m)) N (hH.pullback iB) y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVle⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ U ⊓ W₀ from ⟨hyU, hyW₀⟩) (U ⊓ W₀).isOpen
  refine ⟨V, hyV, fun z hz => (hVle hz).1, ?_⟩
  have hqV : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have eV : (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj N ≅ 𝟙_ _ :=
    Ws31X1.restrictTriv (show q ⁻¹ᵁ V ≤ q ⁻¹ᵁ W₀ from fun z hz => (hVle hz).2) e₀
  have hν : Function.Surjective ((νT k c ε t H m).app (iB ⁻¹ᵁ ((pullback.snd c t) ⁻¹ᵁ V))) :=
    Ws31ThetaF.E6.surjective_unit_app_of_isAffineOpen_of_trivial
      (kIncl k c ε t m) N (q ⁻¹ᵁ V) hqV eV
  rw [hg]
  exact surjective_comp_app _ _ _ (surjective_hom_app e₂ _)
    (surjective_comp_app _ _ _ (Φ_app_surjective k c ε t H m ((pullback.snd c t) ⁻¹ᵁ V) hν)
      (surjective_inv_app e₃ _))

end setting2

end Ws31ThetaF

theorem _root_.AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (H : (pullback c t).Modules) (hH : Scheme.Modules.IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules) (hS : S.ShortExact)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin :
      (Scheme.Modules.pullbackPushforwardAdjunction
        ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    (S.map (Scheme.Modules.pushforward (pullback.snd c t))).ShortExact :=
  Ws31ThetaF.shortExact_map_pushforward_thickening k c ε t H hH m S hS e₂ e₃ hpin
end JacobianVarieties.Picard.Proofs.ShortExact_map_pushforward_thickening
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop) in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop) in
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
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
attribute [-instance]
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
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  exteriorPower.mulₗ_apply_coe
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
