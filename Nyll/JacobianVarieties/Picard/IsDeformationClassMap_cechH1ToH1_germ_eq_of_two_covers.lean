/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Models.Places
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_exists_crossSections
import Nyll.AlgebraicCurves.Cohomology.CechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GermToFunctionField_inf_mem_lSpaceOn_inter_placesOf

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Independence of the affine cover for deformation classes
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationCoverComparison
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u

open  CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace CoverGlue

/-- Two nonempty open subsets of an irreducible scheme intersect. -/
theorem nonempty_inf {X : Scheme.{u}} [IrreducibleSpace X] (U V : X.Opens) [hU : Nonempty U]
    [hV : Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) :=
  (nonempty_preirreducible_inter U.isOpen V.isOpen (Set.nonempty_coe_sort.mp hU)
    (Set.nonempty_coe_sort.mp hV)).to_subtype

/-- A nonempty intersection implies the first open is nonempty. -/
theorem nonempty_of_nonempty_inf_left {X : Scheme.{u}} (U V : X.Opens)
    [h : Nonempty (U ⊓ V : X.Opens)] :
    Nonempty U := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ⟨⟨x, hx.1⟩⟩

/-- A nonempty intersection implies the second open is nonempty. -/
theorem nonempty_of_nonempty_inf_right {X : Scheme.{u}} (U V : X.Opens)
    [h : Nonempty (U ⊓ V : X.Opens)] :
    Nonempty V := by
  obtain ⟨⟨x, hx⟩⟩ := h
  exact ⟨⟨x, hx.2⟩⟩

/-- Restriction preserves the germ of a section in the function field. -/
theorem germToFunctionField_map {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Opens} [Nonempty U]
    [Nonempty V]
    (h : V ≤ U) (s : Γ(X, U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map (homOfLE h).op).hom s)
      = (X.germToFunctionField U).hom s := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_res]
  try rfl

end CoverGlue

end JacobianVarieties.Picard.Proofs.DeformationCoverComparison

namespace AlgebraicGeometry.RelPicard.IsDeformationClassMap

open _root_.JacobianVarieties.Picard.Proofs.DeformationCoverComparison
universe u
open  _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.NeronModelInfra _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.JacobianVarieties.Picard.Proofs.DeformationCoverComparison.CoverGlue in
/-- The cohomology class of a deformation is independent of its two affine cover. -/
theorem cechH1ToH1_germ_eq_of_two_covers
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    [IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲'}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ) (hδ' : IsDeformationClassMap c ε K 𝒲' δ')
    (x : RigKerDualNumber c ε K)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (s' : ((𝒲'.pullback c K).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' : Scheme.{u} := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)
    let c' : X' ⟶ Spec (.of K) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)
    let : Algebra K X'.functionField := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    let W : X'.TwoAffineOpenCover := 𝒲.pullback c K
    let W' : X'.TwoAffineOpenCover := 𝒲'.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)] [Nonempty (W'.U0 ⊓ W'.U1 : X'.Opens)]
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hW' : AlgebraicCurve.placesOf c' W'.U0 ∪ AlgebraicCurve.placesOf c' W'.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField))
      (hsr' : (X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s' ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W'.U0 ∩ AlgebraicCurve.placesOf c'
          W'.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      AlgebraicCurve.cechH1ToH1 hW 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩) =
        AlgebraicCurve.cechH1ToH1 hW' 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s', hsr'⟩) := by
  intro X' c' algKFunctionField W W' hne hne' hW hW' hsr hsr'
  have : Nonempty ((𝒲.pullback c K).U0 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).Opens) :=
    nonempty_of_nonempty_inf_left _ (𝒲.pullback c K).U1
  have : Nonempty ((𝒲.pullback c K).U1 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).Opens) :=
    nonempty_of_nonempty_inf_right (𝒲.pullback c K).U0 _
  have : Nonempty ((𝒲'.pullback c K).U0 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).Opens) :=
    nonempty_of_nonempty_inf_left _ (𝒲'.pullback c K).U1
  have : Nonempty ((𝒲'.pullback c K).U1 : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).Opens) :=
    nonempty_of_nonempty_inf_right (𝒲'.pullback c K).U0 _
  have : Nonempty ((𝒲.pullback c K).U0 ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty ((𝒲.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty ((𝒲.pullback c K).U1 ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty ((𝒲.pullback c K).U1 ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1 :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty ((𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  have : Nonempty ((𝒲.pullback c K).U1 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) :
      (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).Opens) := nonempty_inf _ _
  obtain ⟨g00, g01, g10, g11, h1, h2, h3, -⟩ :=
    IsDeformationClassMap.exists_crossSections c ε K 𝒲 𝒲' hδ hδ' x s s' hs hs'
  have m00 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U0 (𝒲'.pullback c
      K).U0 g00
  have m01 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U0 (𝒲'.pullback c
      K).U1 g01
  have m10 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U1 (𝒲'.pullback c
      K).U0 g10
  have m11 := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) (𝒲.pullback c K).U1 (𝒲'.pullback c
      K).U1 g11
  have e1 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).germToFunctionField
    (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0)).hom h1
  have e2 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).germToFunctionField
    (((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1)).hom h2
  have e3 := congrArg ((Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R
    K)).germToFunctionField
    ((𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1))).hom h3
  simp only [map_add, germToFunctionField_map] at e1 e2 e3
  rw [germToFunctionField_map (X := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))
    (U := (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)
    (V := ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0)
    (inf_le_left : ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U0 ≤ (𝒲.pullback
      c K).U0 ⊓ (𝒲.pullback c K).U1)
    (s : Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K), (𝒲.pullback c K).U0 ⊓
      (𝒲.pullback c K).U1))] at e1
  rw [germToFunctionField_map (X := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))
    (U := (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)
    (V := ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1)
    (inf_le_left : ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) ⊓ (𝒲'.pullback c K).U1 ≤ (𝒲.pullback
      c K).U0 ⊓ (𝒲.pullback c K).U1)
    (s : Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K), (𝒲.pullback c K).U0 ⊓
      (𝒲.pullback c K).U1))] at e2
  rw [germToFunctionField_map (X := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))
    (U := (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
    (V := (𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1))
    (inf_le_right : (𝒲.pullback c K).U0 ⊓ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) ≤
      (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
    (s' : Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K), (𝒲'.pullback c K).U0 ⊓
      (𝒲'.pullback c K).U1))] at e3
  exact AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections hW hW' ⟨_, hsr⟩ ⟨_, hsr'⟩ _
    _ _ _
    m00 m01 m10 m11 e1 e2 e3
end AlgebraicGeometry.RelPicard.IsDeformationClassMap
end ProofImplementation
