/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Data.Set.Disjoint
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic.Ext
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_pullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Nyll.AlgebraicCurves.Geometry.Picard.isInvertible_sectionIdeal_of_range_subset
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit

/-!
# Triviality of fibre twists away from their supports

A section twist and an effective Cartier divisor module become trivial away
from their supports. Tensoring them preserves a given trivialisation on the fibre.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DisjointFibreTwist
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
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
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicCurve
open _root_.NeronModelInfra


namespace Book1


open _root_.AlgebraicGeometry.Scheme.Modules


/-- Pullback trivialises an invertible module when the image avoids the zeros of a section. -/
theorem nonempty_pullback_iso_unit_of_forall_notMem {X Y : Scheme.{u}} (φ : Y ⟶ X)
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hφ : ∀ y : Y, φ.base y ∉ ((Scheme.Modules.zeroSchemeIdeal s).support : Set X)) :
    Nonempty ((Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y.Modules) := by
  let V : X.Opens := (Scheme.Modules.zeroSchemeIdeal s).support.compl
  have hdisj : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support :=
    Set.disjoint_left.mpr fun x hx hx' => hx hx'
  have hfr := hM.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal s V hdisj
  have hfr' := hfr.pullbackLocalSection φ
  have hV : φ ⁻¹ᵁ V = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
      Set.mem_univ, iff_true]
    exact hφ y
  rw [hV] at hfr'
  set σ := Scheme.Modules.pullbackLocalSection φ (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) with
    hσ
  refine Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul (U := ⊤) (V := ⊤)
    (sup_top_eq (⊤ : Y.Opens)) hfr' hfr' 1 (by rw [one_smul]) 1 1
    isUnit_one isUnit_one (by rw [one_mul])

end Book1

end JacobianVarieties.Picard.Proofs.DisjointFibreTwist

namespace AlgebraicGeometry.RelPicard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open CategoryTheory.MonoidalCategory
open Opposite AlgebraicCurve
open JacobianVarieties.Picard.Proofs.DisjointFibreTwist.Book1

/-- Disjointness from the section and divisor supports preserves a fibre trivialisation
 after twisting. -/
theorem
nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {r e : ℕ}
    (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (i₂ : Y ⟶ pullback (pullback.snd c t) pt)
    (hD : ∀ y : Y, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉ D.I.support)
    (hε : ∀ y : Y, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉
      Set.range (rigSection c t ε).base)
    (LL : (pullback c t).Modules)
    (hLL₂ : Nonempty ((Scheme.Modules.pullback i₂).obj (fibreModule c t pt LL) ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback (pullback.snd c t)
        pt).ringCatSheaf))) :
    Nonempty ((Scheme.Modules.pullback i₂).obj (fibreModule c t pt (LL ⊗ (sectionTwist c ε t r ⊗
      D.idealModule))) ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback (pullback.snd c t)
        pt).ringCatSheaf))  := by
  let pr := pullback.fst (pullback.snd c t) pt
  let φ : Y ⟶ pullback c t := i₂ ≫ pr
  have hφb : ∀ y : Y, φ.base y = pr.base (i₂.base y) := fun y => rfl
  let J := sectionIdeal c ε t
  have hJ : J = sectionIdeal c ε t := rfl
  have hJinv : J.IsInvertible := isInvertible_sectionIdeal_of_range_subset c ε U hεU t
  have hJr : (J ^ r).IsInvertible := hJinv.pow r
  have hI : D.I.IsInvertible := D.isInvertible_I_of_supportedIn U hDU
  have hεclosed : IsClosedImmersion (rigSection c t ε) := by
    have h1 : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
    have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)
  have hsuppJ : (J.support : Set ↥(pullback c t)) = Set.range (rigSection c t ε).base := by
    change ((rigSection c t ε).ker.support : Set ↥(pullback c t)) = _
    rw [Scheme.Hom.support_ker,
      ((rigSection c t ε).isClosedEmbedding.isClosedMap.isClosed_range).closure_eq]
  have hsuppJr : ((J ^ r).support : Set ↥(pullback c t)) ⊆ Set.range (rigSection c t ε).base := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
      intro x hx
      exact False.elim hx
    · rw [Scheme.IdealSheafData.support_pow _ _ hr.ne', hsuppJ]
  obtain ⟨eS⟩ :
      Nonempty ((Scheme.Modules.pullback φ).obj (sectionTwist c ε t r) ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hJr
    refine nonempty_pullback_iso_unit_of_forall_notMem φ hJr.isInvertible_invModule
      (J ^ r).invModuleSection ?_
    intro y hy
    have hy' : φ.base y ∈ ((J ^ r).support : Set ↥(pullback c t)) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal (J ^ r).invModuleSection).support :
          Set ↥(pullback c t)) = (J ^ r).support := by rw [hz]
      rw [← hs]; exact hy
    exact hε y (hφb y ▸ hsuppJr hy')
  obtain ⟨eD'⟩ : Nonempty ((Scheme.Modules.pullback φ).obj D.I.invModule ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hI
    refine nonempty_pullback_iso_unit_of_forall_notMem φ hI.isInvertible_invModule
      D.I.invModuleSection ?_
    intro y hy
    have hy' : φ.base y ∈ (D.I.support : Set ↥(pullback c t)) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal D.I.invModuleSection).support :
          Set ↥(pullback c t)) = D.I.support := by rw [hz]
      rw [← hs]; exact hy
    exact hD y (hφb y ▸ hy')
  have hN : Scheme.Modules.IsInvertible D.idealModule := hI.isInvertible_module
  have eEv : D.idealModule ⊗ D.I.invModule ≅ 𝟙_ (pullback c t).Modules :=
    @asIso _ _ _ _ ((ihom.ev D.idealModule).app (𝟙_ (pullback c t).Modules))
      hN.isIso_ev_app_tensorUnit
  have eN : (Scheme.Modules.pullback φ).obj D.idealModule ≅ 𝟙_ Y.Modules :=
    (ρ_ _).symm ≪≫ (whiskerLeftIso _ eD'.symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ _ _).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso eEv ≪≫ Scheme.Modules.pullbackTensorUnitObjIso φ
  obtain ⟨eL2⟩ := hLL₂
  have eL : (Scheme.Modules.pullback φ).obj LL ≅ 𝟙_ Y.Modules :=
    ((Scheme.Modules.pullbackComp i₂ pr).app LL).symm ≪≫ eL2 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso i₂
  have eF : (Scheme.Modules.pullback φ).obj (LL ⊗ (sectionTwist c ε t r ⊗ D.idealModule)) ≅
      𝟙_ Y.Modules :=
    Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫ (eL ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso φ _ _
      ≪≫ (eS ⊗ᵢ eN) ≪≫ λ_ _)) ≪≫ λ_ _
  exact ⟨(Scheme.Modules.pullbackComp i₂ pr).app _ ≪≫ eF ≪≫
    (Scheme.Modules.pullbackTensorUnitObjIso i₂).symm⟩
end AlgebraicGeometry.RelPicard
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
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
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
attribute [-instance]
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
attribute [-simp]
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
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
