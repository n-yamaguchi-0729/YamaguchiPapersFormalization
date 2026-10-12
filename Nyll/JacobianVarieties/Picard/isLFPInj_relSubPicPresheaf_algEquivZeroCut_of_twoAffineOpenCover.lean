/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Schemes.AffineLimit
import Nyll.JacobianVarieties.Picard.IsLFPInj_relPicardPresheaf

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf

/-!
The algebraically trivial sub-Picard presheaf inherits injectivity along filtered affine limits.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.LFPInjSubPic
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
  AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instNonempty
  AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
  AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.AffineLimit


namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (
  Spec
  Scheme
  Flat
  geometrically
  AffineLimit.specOverOfSubalgebra
  AffineLimit.IsLFPInj)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (
  relPicardPresheaf
  SubPicCondition
  algEquivZeroCut
  relSubPicPresheaf
  relSubPicPresheaf_map_coe
  isLFPInj_relPicardPresheaf)
end AlgebraicGeometry.RelPicard

open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.RelPicard in
theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_of_relPicardPresheaf'
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (P : SubPicCondition c ε)
    (h : AffineLimit.IsLFPInj (relPicardPresheaf c ε)) :
    AffineLimit.IsLFPInj (relSubPicPresheaf c ε P) := by
  intro A _ _ A₀ hA₀ x₀ x₀' hx
  have hx' : (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀.1 =
      (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀'.1 := by
    have := congrArg Subtype.val hx
    simp only [relSubPicPresheaf_map_coe] at this
    exact this
  obtain ⟨A₁, hA₁, hle, h1⟩ := h A A₀ hA₀ x₀.1 x₀'.1 hx'
  refine ⟨A₁, hA₁, hle, Subtype.ext ?_⟩
  exact h1

open _root_.JacobianVarieties.Picard.Proofs.LFPInjSubPic.AlgebraicGeometry.RelPicard
  renaming isLFPInj_relSubPicPresheaf_of_relPicardPresheaf' → subPicLFPInj in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  exact subPicLFPInj c ε _ (isLFPInj_relPicardPresheaf R 𝒱 c ε)
end JacobianVarieties.Picard.Proofs.LFPInjSubPic
end ProofImplementation
