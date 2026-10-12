/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Schemes.AffineLimit
import Nyll.JacobianVarieties.Picard.IsLFPInj_relPicardPresheaf

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Relative Picard varieties and fibre cohomology

Transfer finite-presentation injectivity from the relative Picard presheaf to its algebraically
trivial cut.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsLFPInj_relSubPicPresheaf_algEquivZeroCut
attribute [-instance] AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
open _root_.AlgebraicGeometry.FGSubalgebra
  (instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram)
in
attribute [-instance]
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instNonempty
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
open _root_.AlgebraicGeometry.FGSubalgebra
  (instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram)
in
attribute [-instance]
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsFiltered
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
attribute [-instance] AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
attribute [-instance] AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
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
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
end AlgebraicGeometry.RelPicard
open scoped AlgebraicGeometry AlgebraicGeometry.RelPicard in
theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_of_relPicardPresheaf
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

open IsLFPInj_relSubPicPresheaf_algEquivZeroCut.AlgebraicGeometry.RelPicard
  (isLFPInj_relSubPicPresheaf_of_relPicardPresheaf)
in
theorem _root_.AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  exact isLFPInj_relSubPicPresheaf_of_relPicardPresheaf c ε _
    (isLFPInj_relPicardPresheaf R 𝔉.twoAffineOpenCover c ε)
end JacobianVarieties.Picard.Proofs.IsLFPInj_relSubPicPresheaf_algEquivZeroCut
end ProofImplementation
